library(shiny)
library(ggplot2)
library(dplyr)
library(tidyr)
library(lubridate)
library(stats)
library(brms)

# ---- for Sheets + caching ----
library(googlesheets4)
library(memoise)
library(cachem)

options(mc.cores = 1)
Sys.setenv(OMP_NUM_THREADS = "1")   # avoid OpenMP/BLAS oversubscription
rstan::rstan_options(auto_write = TRUE)  # reuse compiled model in the instance

# ---------- helpers ----------
parse_time_hms <- function(x, tz = "America/Los_Angeles") {
  # Normalize ANY input to a POSIXct at an anchor date with the same clock time (no shifting).
  # We only care about time-of-day for downstream logic.
  anchor <- as.POSIXct("1970-01-01", tz = tz)
  
  to_posix_one <- function(v) {
    # 1) POSIXct: keep the clock, throw away the date; DO NOT shift time zones
    if (inherits(v, c("POSIXct","POSIXt"))) {
      hh <- lubridate::hour(v)
      mm <- lubridate::minute(v)
      ss <- floor(lubridate::second(v))
      return(anchor + hh*3600 + mm*60 + ss)
    }
    
    # 2) Numeric serials (Excel/Sheets): use the FRACTIONAL DAY only (time-of-day)
    if (is.numeric(v) && !is.na(v)) {
      secs <- (v %% 1) * 86400
      return(anchor + secs)
    }
    
    # 3) Character: try common patterns; then map to anchor with same clock
    if (is.character(v)) {
      s <- trimws(v)
      if (s == "") return(as.POSIXct(NA_real_, origin = "1970-01-01", tz = tz))
      try_parsers <- list(
        function(z) lubridate::parse_date_time(z, orders = "I:M:S p", tz = tz, quiet = TRUE),
        function(z) lubridate::parse_date_time(z, orders = "I:M p",   tz = tz, quiet = TRUE),
        function(z) lubridate::parse_date_time(z, orders = "H:M:S",   tz = tz, quiet = TRUE),
        function(z) lubridate::parse_date_time(z, orders = "H:M",     tz = tz, quiet = TRUE),
        function(z) suppressWarnings(lubridate::ymd_hms(z, tz = tz, quiet = TRUE)),
        function(z) suppressWarnings(lubridate::ymd_hm(z,  tz = tz, quiet = TRUE))
      )
      for (f in try_parsers) {
        dt <- f(s)
        if (!all(is.na(dt))) {
          hh <- lubridate::hour(dt)
          mm <- lubridate::minute(dt)
          ss <- floor(lubridate::second(dt))
          return(anchor + hh*3600 + mm*60 + ss)
        }
      }
    }
    
    # 4) Date-only: treat as missing (no time info)
    if (inherits(v, "Date")) return(as.POSIXct(NA_real_, origin = "1970-01-01", tz = tz))
    
    as.POSIXct(NA_real_, origin = "1970-01-01", tz = tz)
  }
  
  res <- vapply(x, to_posix_one, FUN.VALUE = as.POSIXct(NA_real_, origin = "1970-01-01", tz = tz))
  as.POSIXct(res, origin = "1970-01-01", tz = tz)
}


make_bins <- function(df, bin_minutes = 15, tz_use = "America/Los_Angeles", active_only = TRUE) {
  # df columns expected: "Parking Start", "Parking End", "Ticket Time (if any)"
  # 1) Expand exposure to minutes
  parks <- df %>%
    filter(!is.na(`Parking Start`), !is.na(`Parking End`)) %>%
    mutate(
      start = parse_time_hms(`Parking Start`, tz_use),
      end   = parse_time_hms(`Parking End`,   tz_use)
    ) %>%
    filter(!is.na(start), !is.na(end), end > start) %>%
    mutate(start = floor_date(start, "minute"),
           end   = floor_date(end,   "minute"))
  
  if (nrow(parks) == 0) {
    return(NULL)
  }
  
  parks_exp <- parks %>%
    rowwise() %>%
    summarize(minute = list(seq(from = start, to = end - seconds(1), by = "1 min")),
              .groups = "drop") %>%
    unnest(minute) %>%
    mutate(hod_min = hour(minute)*60 + minute(minute),
           hod_hr  = hod_min/60)
  
  # 2) Tickets (times-of-day only)
  tix <- df %>%
    filter(!is.na(`Ticket Time (if any)`)) %>%
    mutate(tt = parse_time_hms(`Ticket Time (if any)`, tz_use)) %>%
    filter(!is.na(tt)) %>%
    transmute(hod_min = hour(tt)*60 + minute(tt),
              hod_hr  = hod_min/60)
  
  # active window toggle
  if (active_only) {
    parks_exp <- parks_exp %>% filter(hod_hr >= 6, hod_hr < 21)
    tix       <- tix       %>% filter(hod_hr >= 6, hod_hr < 21)
    day_min   <- 6*60; day_max <- 21*60
  } else {
    day_min   <- 0; day_max <- 24*60
  }
  
  breaks_min  <- seq(day_min, day_max, by = bin_minutes)
  # ensure we cover the last partial bin (if needed)
  if (tail(breaks_min,1) < day_max) breaks_min <- c(breaks_min, day_max)
  labels_hr   <- head(breaks_min, -1)/60
  bin_width_h <- bin_minutes/60
  
  exposure_bins <- parks_exp %>%
    mutate(bin = cut(hod_min, breaks = breaks_min, right = FALSE, labels = labels_hr)) %>%
    count(bin, name = "exposure_minutes") %>%
    mutate(
      exposure_hours = exposure_minutes/60,
      tod_mid = as.numeric(as.character(bin)) + bin_width_h/2
    ) %>%
    select(tod_mid, exposure_hours)
  
  ticket_bins <- tix %>%
    mutate(bin = cut(hod_min, breaks = breaks_min, right = FALSE, labels = labels_hr)) %>%
    count(bin, name = "tickets") %>%
    mutate(tod_mid = as.numeric(as.character(bin)) + bin_width_h/2) %>%
    select(tod_mid, tickets)
  
  bins <- tibble(tod_mid = head(breaks_min, -1)/60 + bin_width_h/2) %>%
    left_join(exposure_bins, by = "tod_mid") %>%
    left_join(ticket_bins,  by = "tod_mid") %>%
    mutate(
      exposure_hours = replace_na(exposure_hours, 0),
      tickets        = replace_na(tickets, 0),
      bin_width_h    = bin_width_h
    )
  
  list(bins = bins,
       tickets_times_hr = tix$hod_hr,
       breaks_min = breaks_min,
       bin_width_h = bin_width_h,
       active_only = active_only)
}

fit_bayes <- function(df_bins) {
  data_model <- df_bins %>%
    dplyr::filter(exposure_hours > 0) %>%
    dplyr::transmute(
      tickets,
      tod = tod_mid,
      exposure_hours
    )
  
  stopifnot(!any(is.na(data_model$exposure_hours)),
            !any(is.infinite(data_model$exposure_hours)))
  
  priors <- c(
    set_prior("normal(-3.5, 1.5)", class = "Intercept"),
    set_prior("student_t(3, 0, 1.0)", class = "sds")
  )
  
  # Build model data explicitly
  data_model <- df_bins %>%
    dplyr::transmute(tickets, tod = tod_mid, exposure_hours)
  
  if (exists("offset", inherits = FALSE)) rm(offset)
  
  brm(
    tickets ~ s(tod, k = 5) + stats::offset(log(exposure_hours)),           # non-cyclic smooth over active window
    family  = poisson(link = "log"),
    data    = data_model,
    prior   = priors,
    chains  = 4, iter = 3000, warmup = 1000, cores = 4,
    control = list(adapt_delta = 0.995)
  )
}

posterior_rates <- function(fit, df_bins) {
  # We modeled: tickets ~ s(tod, ...) + offset(logexposure)
  # For rate/hr, set exposure = 1 hr -> logexposure = 0 in newdata.
  newdat <- df_bins %>% transmute(
    tod = tod_mid,
    exposure_hours = 1   # <- key: no offset arg passed to posterior_epred()
  )
  
  ep <- posterior_epred(
    fit,
    newdata    = newdat,
    re_formula = NA
  )
  # ep: draws x bins (rate per hour because exposure=1)
  list(
    draws = ep,
    mean  = apply(ep, 2, mean),
    lo    = apply(ep, 2, quantile, 0.025),
    hi    = apply(ep, 2, quantile, 0.975)
  )
}

# Use embedded PREFIT posterior; interpolate to current bins if needed
posterior_rates_prefit <- function(prefit, df_bins) {
  stopifnot(is.list(prefit), is.numeric(prefit$grid), is.matrix(prefit$draws))
  x_src <- prefit$grid
  x_dst <- df_bins$tod_mid
  
  # Fast path if grids match exactly
  if (length(x_src) == length(x_dst) && all(abs(x_src - x_dst) < 1e-8)) {
    return(list(
      draws = prefit$draws,
      mean  = prefit$mean,
      lo    = prefit$lo,
      hi    = prefit$hi
    ))
  }
  
  # Otherwise, interpolate each draw row-wise to the destination grid
  # (linear interpolation; extrapolation uses boundary values)
  interp_row <- function(y) approx(x = x_src, y = y, xout = x_dst, rule = 2, ties = "ordered")$y
  draws_interp <- t(apply(prefit$draws, 1, interp_row))
  mean_interp  <- approx(x_src, prefit$mean, xout = x_dst, rule = 2, ties = "ordered")$y
  lo_interp    <- approx(x_src, prefit$lo,   xout = x_dst, rule = 2, ties = "ordered")$y
  hi_interp    <- approx(x_src, prefit$hi,   xout = x_dst, rule = 2, ties = "ordered")$y
  
  list(draws = draws_interp, mean = mean_interp, lo = lo_interp, hi = hi_interp)
}

fmt_hhmm <- function(x) sprintf("%02d:%02d", floor(x), round((x - floor(x))*60))

# Expected-cost optimizer for a CONTIGUOUS pay window within the user's interval
opt_pay_window <- function(rates_hr, bin_width_h, fine, rate_per_hr = 5, day_cap = 25) {
  n <- length(rates_hr); bw <- bin_width_h
  total_lambda <- sum(rates_hr) * bw
  best <- list(cost = Inf, i = NA, j = NA, pay_hours = 0)
  for (i in 1:(n+1)) {
    for (j in (i-1):n) {
      pay_bins   <- if (j >= i) (j - i + 1) else 0
      pay_hours  <- pay_bins * bw
      pay_cost   <- min(rate_per_hr * pay_hours, day_cap)
      paid_lambda   <- if (pay_bins > 0) sum(rates_hr[i:j]) * bw else 0
      unpaid_lambda <- total_lambda - paid_lambda
      exp_cost  <- pay_cost + fine * (1 - exp(-unpaid_lambda))
      if (exp_cost < best$cost) {
        best <- list(cost = exp_cost, i = i, j = j, pay_hours = pay_hours,
                     unpaid_lambda = unpaid_lambda)
      }
    }
  }
  best
}

# ---------- prefit posterior ----------
# Use the provided PDLParkingSupport.R to adjust PREFIT

PREFIT <- NULL
cat("PREFIT <- ", utils::capture.output(dput(prefit)), sep = "")

# ---------- ui ----------
ui <- fluidPage(
  titlePanel("Parking ticket risk explorer (Bayesian, 30-min bins)"),
  sidebarLayout(
    sidebarPanel(
      fileInput("csv", "Upload CSV", accept = c(".csv")),
      checkboxInput("active_only", "Assume no ticketing 9pm–6am", TRUE),
      numericInput("fine", "Ticket fine ($)", value = 60, min = 1, step = 1),
      numericInput("rate", "Parking rate ($/hr)", value = 5, min = 0, step = 0.5),
      numericInput("cap", "Daily max ($)", value = 25, min = 0, step = 1),
      hr(),
      sliderInput("user_start", "Your parking start (hour)", min = 0, max = 24, value = 8, step = 0.25),
      sliderInput("user_end",   "Your parking end (hour)",   min = 0, max = 24, value = 17, step = 0.25),
      helpText("Tip: quarter-hours are 0.00, 0.25, 0.50, 0.75"),
      hr(),
      actionButton("fit", "Fit Bayesian model")
    ),
    mainPanel(
      h4("Plot 1a — Exposure across time (area)"),
      plotOutput("plot_exposure", height = 240),
      h4("Plot 1b — Ticket times (dot histogram)"),
      plotOutput("plot_tickets", height = 160),
      hr(),
      h4("Plot 2 — Inferred ticketing rate by time-of-day (posterior mean & 95% CrI)"),
      plotOutput("plot_rate", height = 260),
      hr(),
      h4("Your parking window results"),
      verbatimTextOutput("results_text")
    )
  )
)

# ---------- server ----------
server <- function(input, output, session) {
  # ---- NEW: Google Sheet default + online cache ----
  # Use a disk cache so the sheet is not re-fetched for every session
  cache_dir <- file.path(tempdir(), "gsheet_cache")
  dir.create(cache_dir, showWarnings = FALSE, recursive = TRUE)
  disk_cache <- cache_disk(dir = cache_dir)
  gs4_deauth()  # public read
  
  read_sheet_cached <- memoise(function() {
    # first sheet by default; change 'sheet=' if needed
    googlesheets4::read_sheet("https://docs.google.com/spreadsheets/d/1-sohePDsvO2vwbLlC5A9_ed5ztrMxx3fnua09I4Skog", .name_repair = "minimal")
  }, cache = disk_cache)
  
  # Minimal change: previously req(input$csv). Now: use upload if provided; else Sheets.
  bins_react <- reactive({
    df <- if (!is.null(input$csv)) {
      read.csv(input$csv$datapath, check.names = FALSE)
    } else {
      read_sheet_cached()
    }
    make_bins(df, bin_minutes = 30, active_only = isTRUE(input$active_only))
  })
  
  # Plot 1a: exposure area
  output$plot_exposure <- renderPlot({
    br <- bins_react(); req(br)
    b  <- br$bins
    ggplot(b, aes(tod_mid, exposure_hours)) +
      geom_area(alpha = 0.3) +
      scale_x_continuous("Time of day (hours)", limits = if (br$active_only) c(6,21) else c(0,24),
                         breaks = seq(0,24,by=2)) +
      labs(y = "Parked hours per 15-min bin") +
      theme_minimal()
  })
  # Plot 1b: ticket times dot histogram
  output$plot_tickets <- renderPlot({
    br <- bins_react(); req(br)
    t_hr <- br$tickets_times_hr
    df_t <- data.frame(tod = t_hr)
    if (nrow(df_t) == 0) {
      ggplot() + annotate("text", x = 0.5, y = 0.5, label = "No ticket timestamps in data") + theme_void()
    } else {
      ggplot(df_t, aes(tod)) +
        geom_dotplot(binwidth = 0.25, method = "histodot", stackratio = 1.2) +
        scale_x_continuous("Time of day (hours)", limits = if (br$active_only) c(6,21) else c(0,24),
                           breaks = seq(0,24,by=2)) +
        labs(y = "Tickets (dot histogram)") +
        theme_minimal()
    }
  })
  
  # Fit Bayesian model on click (this already makes inferred outputs "permanent" until clicked again)
  fit_obj <- eventReactive(input$fit, {
    withProgress(message = "Fitting Bayesian model…", value = 0, {
      br <- bins_react(); req(br)
      b <- br$bins %>% dplyr::filter(exposure_hours > 0) %>% dplyr::arrange(tod_mid)
      validate(need(nrow(b) > 1, "Not enough nonzero-exposure bins to fit."))
      incProgress(0.1)
      fit <- fit_bayes(b)         # single-core, lighter config now
      incProgress(0.8)
      rates <- posterior_rates(fit, b)
      incProgress(0.1)
      list(fit = fit, df_bins = b, rates = rates, bin_width_h = unique(b$bin_width_h)[1])
    })
  })
  
  # Plot 2: posterior rate curve (depends ONLY on fit_obj -> sticky)
  output$plot_rate <- renderPlot({
    fr <- fit_obj()
    if (is.null(fr) && !is.null(PREFIT)) {
      br <- bins_react(); req(br)
      b  <- br$bins %>% dplyr::filter(exposure_hours > 0) %>% dplyr::arrange(tod_mid)
      validate(need(nrow(b) > 1, "Not enough nonzero-exposure bins to plot."))
      r  <- posterior_rates_prefit(PREFIT, b)
      fr <- list(df_bins = b, rates = r, bin_width_h = unique(b$bin_width_h)[1])
    }
    req(fr)
    b <- fr$df_bins; r <- fr$rates
    d <- b %>% dplyr::mutate(rate_mean = r$mean, lo = r$lo, hi = r$hi)
    ggplot(d, aes(tod_mid, rate_mean)) +
      geom_ribbon(aes(ymin = lo, ymax = hi), alpha = 0.2) +
      geom_line() +
      scale_x_continuous("Time of day (hours)",
                         limits = c(min(b$tod_mid), max(b$tod_mid)),
                         breaks = seq(floor(min(b$tod_mid)), ceiling(max(b$tod_mid)), by = 2)) +
      labs(y = "Tickets per parked-hour (posterior)") +
      theme_minimal()
  })
  
  # Text outputs for user-selected window (sticky: recalculates with sliders, but uses last fit)
  output$results_text <- renderText({
    fr <- fit_obj()
    if (is.null(fr) && !is.null(PREFIT)) {
      br0 <- bins_react(); req(br0)
      b0  <- br0$bins %>% dplyr::filter(exposure_hours > 0) %>% dplyr::arrange(tod_mid)
      validate(need(nrow(b0) > 1, "Not enough nonzero-exposure bins for results."))
      r0  <- posterior_rates_prefit(PREFIT, b0)
      fr  <- list(df_bins = b0, rates = r0, bin_width_h = unique(b0$bin_width_h)[1])
    }
    req(fr)
    br <- bins_react(); req(br)
    rate_per_hr <- input$rate; cap <- input$cap; fine <- input$fine
    
    start <- input$user_start; end <- input$user_end
    if (end <= start) return("End must be after start.")
    # Clip to modeled domain
    dom_min <- min(fr$df_bins$tod_mid); dom_max <- max(fr$df_bins$tod_mid) + fr$bin_width_h
    a <- max(start, dom_min); z <- min(end, dom_max)
    if (z <= a) return("Selected window lies entirely outside modeled active hours.")
    
    # Identify the bins that intersect [a, z)
    b <- fr$df_bins
    bw <- fr$bin_width_h
    bin_starts <- b$tod_mid - bw/2
    bin_ends   <- b$tod_mid + bw/2
    overlaps <- pmax(0, pmin(bin_ends, z) - pmax(bin_starts, a))  # hours
    sel <- overlaps > 0
    if (!any(sel)) return("No 15-min bins overlap the chosen window.")
    
    # Posterior draws matrix and mean rates for those bins
    draws <- fr$rates$draws[, sel, drop = FALSE]             # draws x bins
    mean_rates <- fr$rates$mean[sel]
    
    # Posterior distribution of total lambda over the window
    lam_draws <- as.numeric(draws %*% overlaps[sel])
    p_ticket_draws <- 1 - exp(-lam_draws)
    p_mean <- mean(p_ticket_draws)
    p_lo   <- quantile(p_ticket_draws, 0.025)
    p_hi   <- quantile(p_ticket_draws, 0.975)
    
    # "Most likely" ticket time = bin with highest posterior mean rate within the window
    idx_max <- which.max(mean_rates)
    likely_time <- fmt_hhmm(b$tod_mid[sel][idx_max])
    
    # Optimal contiguous pay window (greedy over all continuous choices)
    best <- opt_pay_window(rates_hr = mean_rates, bin_width_h = bw,
                           fine = fine, rate_per_hr = rate_per_hr, day_cap = cap)
    if (is.na(best$i)) {
      best_text <- "No payment recommended (no bins reduce expected cost)."
    } else if (best$i > best$j) {
      best_text <- "Optimal: don't pay for any time in this window."
    } else {
      pay_start <- b$tod_mid[sel][best$i] - bw/2
      pay_end   <- b$tod_mid[sel][best$j] + bw/2
      hours_paid <- best$pay_hours
      pay_cost <- min(rate_per_hr * hours_paid, cap)
      best_text <- sprintf("Optimal pay window: %s–%s (%.2f h). Expected cost: $%.2f (includes pay $%.2f; remaining ticket risk %.1f%%).",
                           fmt_hhmm(pay_start), fmt_hhmm(pay_end),
                           hours_paid, best$cost, pay_cost,
                           100*(1 - exp(-best$unpaid_lambda)))
    }
    
    paste0(
      "Your window: ", fmt_hhmm(a), "–", fmt_hhmm(z), "\n",
      sprintf("Probability of ≥1 ticket: %.1f%% (95%% CrI %.1f–%.1f%%)\n",
              100*p_mean, 100*p_lo, 100*p_hi),
      "Most likely ticket time (bin center): ", likely_time, "\n",
      best_text
    )
  })
}

shinyApp(ui, server)


