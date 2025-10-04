# -------- pre-fit: only use on local machine -----------

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



# Run the below


gs4_deauth()
df_sh <- read_sheet(
  "https://docs.google.com/spreadsheets/d/1-sohePDsvO2vwbLlC5A9_ed5ztrMxx3fnua09I4Skog",
  .name_repair = "minimal"   # keep headers EXACTLY as in the sheet
)

br   <- make_bins(df_sh, bin_minutes = 30, active_only = TRUE)
b    <- br$bins %>% dplyr::filter(exposure_hours > 0) %>% dplyr::arrange(tod_mid)

fit  <- fit_bayes(b)

pr   <- posterior_rates(fit, b)

prefit <- list(
  grid  = b$tod_mid,
  draws = pr$draws,    # draws matrix: iterations x length(grid)
  mean  = pr$mean,
  lo    = pr$lo,
  hi    = pr$hi
)

# Paste below after PREFIT <- NULL
cat("PREFIT <- ", utils::capture.output(dput(prefit)), sep = "")
