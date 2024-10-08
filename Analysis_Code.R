#############################################################################################################################
#                          Final Dissertation Cap 4
#***************************************************************************************************************************#
# Program = Allowances and Offsets California Market
# Programmer = Luca Albertini
# Date first logger: 2023 03 05
#
#            Description: ARDL Model to estimate the relation between allowances prices and offsets in Califonria CaT. 
#                         Section of the Luca Albertini Final dissertation for the master in International Politics and Economics
#                         presented on July 2023.
#
#            Input files: in_data
#            Temp files: none
#            Output files: out_dat
#
#**************************************************************************************************************************#

#set the working directory
#Luca's Macbook
setwd("~/Education/Master_Degree/Dissertation")
# set working directory
# setwd("")

#load needed packages
library("expss")
library("WDI")
library("reshape2")
require("normtest")
library("readxl")
library("reshape")
library("Hmisc")
library("tseries")
library("pastecs")
library("psych")
library("moments")
library("AER") 
library("systemfit")
library("moments") # kurtosis and skewness calculations
library("stargazer") # table format for regression results
library("MASS")
library("lmtest") # required for coefci and coeftest
library("sandwich") # required for heteroskedastic robust standard errors calculation
library("plm")
library("gridExtra") # arrange graphs
library("olsrr") # Breusch-Pagan Test
library("fBasics") # dagoTest (approximates sktest)
library("ivpack")
library("ggplot2")
library("haven") 
library("dplyr")
library("foreign")
library("broom")
library("estimatr")
library("Jmisc")
library("rccdates")
library("xts")
library("tis")
library("sos")
library("gridExtra")
library("corrgram")
library("urca")
library("dynlm")
library("tibble")
library("corrplot")
library("flexmix")
library("sos")
library("tsDyn") #VECM and VAR calculation
library("knitr")
library("vars")
library("seastests")
library("trend")
library("forecast")
library("ARDL")
library("dLagM")
library("lmtest")
library("egcm")
library("gamlss")
library("itsadug")
library("astsa")
library("pracma")
library("astsa")
library("tstools")
library("modelsummary")


###### this command might be useful to find to what package a function belongs
# findFn(function name)

# clear workspace
rm(list = ls())

###################################### USEFUL FUNCTIONS ############################################################

###### OUTLIERS
# count mild outliers
find_mild_out <- function(X) {
  iqr = IQR(X)
  lowerq = quantile(X)[2]
  upperq = quantile(X)[4]
  lowmildborder = lowerq - (iqr*1.5)
  upmildborder = upperq + (iqr*1.5)
  print(mild_outliers <- length(which( X > upmildborder | X < lowmildborder)))
}
# function to count total outliers
outliers <- function(X) {
  print(find_mild_out(X))}

###### QUANTS
quants <- function(series) {
  s <- series
  return(
    data.frame("Level" = s,
               "Logarithm" = log(s),
               "first log difference" = log(s) - lag(log(s)),
               "AnnualGrowthRate" = 100 * log(s / lag(s)),
               "1stLagAnnualGrowthRate" = lag(100 * log(s / lag(s))))
  )
}
# this command gives:
# the Xs of the series (the level--> in this case the GDP)
# the logarithm
# the annual growth rate
# the annual log rate lag

###### BIC
# Computation of the BIC
BIC2 <- function(model) {
  ssr <- sum(model$residuals^2)#sum of squared residual
  t <- length(model$residuals)#length of model residuals
  npar <- length(model$coef)#length of coefficent
  
  return(
    round(c("p" = npar - 1,
            "BIC" = log(ssr/t) + npar * log(t)/t,
            "R2" = summary(model)$r.squared), 4)
  )
}
################## population variance
var_pop <- function(X) {
  
  mean((X - mean(X))^2)}


#################### Interpreting augmented dickey fueller by Hank Roark
interp_urdf <- function(urdf, level="5pct") {
  if(class(urdf) != "ur.df") stop('parameter is not of class ur.df from urca package')
  if(!(level %in% c("1pct", "5pct", "10pct") ) ) stop('parameter level is not one of 1pct, 5pct, or 10pct')
  
  cat("========================================================================\n")
  cat( paste("At the", level, "level:\n") )
  if(urdf@model == "none") {
    cat("The model is of type none\n")
    tau1_crit = urdf@cval["tau1",level]
    tau1_teststat = urdf@teststat["statistic","tau1"]
    tau1_teststat_wi_crit = tau1_teststat > tau1_crit
    if(tau1_teststat_wi_crit) {
      cat("tau1: The null hypothesis is not rejected, unit root is present\n")
    } else {
      cat("tau1: The null hypothesis is rejected, unit root is not present\n")
    }
  } else if(urdf@model == "drift") {
    cat("The model is of type drift\n")
    tau2_crit = urdf@cval["tau2",level]
    tau2_teststat = urdf@teststat["statistic","tau2"]
    tau2_teststat_wi_crit = tau2_teststat > tau2_crit
    phi1_crit = urdf@cval["phi1",level]
    phi1_teststat = urdf@teststat["statistic","phi1"]
    phi1_teststat_wi_crit = phi1_teststat < phi1_crit
    if(tau2_teststat_wi_crit) {
      # Unit root present branch
      cat("tau2: The first null hypothesis is not rejected, unit root is present\n")
      if(phi1_teststat_wi_crit) {
        cat("phi1: The second null hypothesis is not rejected, unit root is present\n")
        cat("      and there is no drift.\n")
      } else {
        cat("phi1: The second null hypothesis is rejected, unit root is present\n")
        cat("      and there is drift.\n")
      }
    } else {
      # Unit root not present branch
      cat("tau2: The first null hypothesis is rejected, unit root is not present\n")
      if(phi1_teststat_wi_crit) {
        cat("phi1: The second null hypothesis is not rejected, unit root is present\n")
        cat("      and there is no drift.\n")
        warning("This is inconsistent with the first null hypothesis.")
      } else {
        cat("phi1: The second null hypothesis is rejected, unit root is not present\n")
        cat("      and there is drift.\n")
      }
    }
  } else if(urdf@model == "trend") {
    cat("The model is of type trend\n")
    tau3_crit = urdf@cval["tau3",level]
    tau3_teststat = urdf@teststat["statistic","tau3"]
    tau3_teststat_wi_crit = tau3_teststat > tau3_crit
    phi2_crit = urdf@cval["phi2",level]
    phi2_teststat = urdf@teststat["statistic","phi2"]
    phi2_teststat_wi_crit = phi2_teststat < phi2_crit
    phi3_crit = urdf@cval["phi3",level]
    phi3_teststat = urdf@teststat["statistic","phi3"]
    phi3_teststat_wi_crit = phi3_teststat < phi3_crit
    if(tau3_teststat_wi_crit) {
      # First null hypothesis is not rejected, Unit root present branch
      cat("tau3: The first null hypothesis is not rejected, unit root is present\n")
      if(phi3_teststat_wi_crit) {
        # Second null hypothesis is not rejected
        cat("phi3: The second null hypothesis is not rejected, unit root is present\n")
        cat("      and there is no trend\n")
        if(phi2_teststat_wi_crit) {
          # Third null hypothesis is not rejected
          # a0-drift = gamma = a2-trend = 0
          cat("phi2: The third null hypothesis is not rejected, unit root is present\n")
          cat("      there is no trend, and there is no drift\n")
        } else {
          # Third null hypothesis is rejected
          cat("phi2: The third null hypothesis is rejected, unit root is present\n")
          cat("      there is no trend, and there is drift\n")
        }
      }
      else {
        # Second null hypothesis is rejected
        cat("phi3: The second null hypothesis is rejected, unit root is present\n")
        cat("      and there is trend\n")
        if(phi2_teststat_wi_crit) {
          # Third null hypothesis is not rejected
          # a0-drift = gamma = a2-trend = 0
          cat("phi2: The third null hypothesis is not rejected, unit root is present\n")
          cat("      there is no trend, and there is no drift\n")
          warning("This is inconsistent with the second null hypothesis.")
        } else {
          # Third null hypothesis is rejected
          cat("phi2: The third null hypothesis is rejected, unit root is present\n")
          cat("      there is trend, and there may or may not be drift\n")
          warning("Presence of drift is inconclusive.")
        }
      }
    } else {
      # First null hypothesis is rejected, Unit root not present branch
      cat("tau3: The first null hypothesis is rejected, unit root is not present\n")
      if(phi3_teststat_wi_crit) {
        cat("phi3: The second null hypothesis is not rejected, unit root is present\n")
        cat("      and there is no trend\n")
        warning("This is inconsistent with the first null hypothesis.")
        if(phi2_teststat_wi_crit) {
          # Third null hypothesis is not rejected
          # a0-drift = gamma = a2-trend = 0
          cat("phi2: The third null hypothesis is not rejected, unit root is present\n")
          cat("      there is no trend, and there is no drift\n")
          warning("This is inconsistent with the first null hypothesis.")
        } else {
          # Third null hypothesis is rejected
          cat("phi2: The third null hypothesis is rejected, unit root is not present\n")
          cat("      there is no trend, and there is drift\n")
        }
      } else {
        cat("phi3: The second null hypothesis is rejected, unit root is not present\n")
        cat("      and there may or may not be trend\n")
        warning("Presence of trend is inconclusive.")
        if(phi2_teststat_wi_crit) {
          # Third null hypothesis is not rejected
          # a0-drift = gamma = a2-trend = 0
          cat("phi2: The third null hypothesis is not rejected, unit root is present\n")
          cat("      there is no trend, and there is no drift\n")
          warning("This is inconsistent with the first and second null hypothesis.")
        } else {
          # Third null hypothesis is rejected
          cat("phi2: The third null hypothesis is rejected, unit root is not present\n")
          cat("      there may or may not be trend, and there may or may not be drift\n")
          warning("Presence of trend and drift is inconclusive.")
        }
      }
    }
  } else warning('urdf model type is not one of none, drift, or trend')
  cat("========================================================================\n")
}

###################################### PREPARE DATA #########################################################

# load data from the Prices_r.csv (an excel file)
prices = read.csv("in_data/prices_raw.csv", header =  TRUE, sep = ",")
# have a quick look to the data
glimpse(prices)
# 36 observations of 10 variables

# preparation of the data set
#rename some variables
names(prices)[names(prices) == "Current.Auction.Settlement.Price"] <- "allow_price"
names(prices)[names(prices) == "Total.Current.Auction.Sold"] <- "allow_sold"
names(prices)[names(prices) == "Offsets.Supply..Total.amount.for.that.quarter."] <- "off_supp"
names(prices)[names(prices) == "Off.General.Account"] <- "gen_acc"
names(prices)[names(prices) == "Off.Compliance.Account"] <- "comp_acc"
names(prices)[names(prices) == "Date"] <- "date"
#select just the relevant variables
prices1 <- select(prices, date, allow_price, allow_sold, 
                  off_supp, gen_acc, comp_acc)
# 36 obs of 6 variables
#select just the year where there are infos (11/20113 to 08/2022)
prices1 <- dplyr::filter(prices1, date >= as.Date("2014-02-01"), date <= as.Date("2022-11-01"))
#set the right length for date
date <- prices1$date
# applying label to variables
prices1 = apply_labels (prices1,
                        allow_price = "USD",
                        allow_sold= "total allowances sold",
                        off_supp = "offsets issued",
                        gen_acc = "Total offsets in general account",
                        comp_acc = "Total offsets in compliance account")
#convert data into numeric (if not already in that format)
prices1$allow_price <- as.numeric(prices1$allow_price)
prices1$allow_sold <- as.numeric(prices1$allow_sold)
prices1$off_supp <- as.numeric(prices1$off_supp)
prices1$gen_acc<- as.numeric(prices1$gen_acc)
prices1$comp_acc <- as.numeric(prices1$comp_acc)
# save data set in a folder
write.csv(prices1, file= "out_data/prices_cleaned.csv")
########### transform all the variables into time series
ap_ts <- ts(prices1$allow_price, start = c(2014, 2), end = c(2022,4), frequency = 4)
as_ts <- ts(prices1$allow_sold, start = c(2014, 2), end = c(2022,4), frequency = 4)
offsupp_ts <- ts(prices1$off_supp, start = c(2014, 2), end = c(2022,4), frequency = 4)
genacc_ts <- ts(prices1$gen_acc, start = c(2014, 2), end = c(2022,4), frequency = 4)
compacc_ts <- ts(prices1$comp_acc, start = c(2014, 2), end = c(2022,4), frequency = 4)
#add the "date" variables
date <- prices1$date
#transform "date" into date format
date <- as.Date(date)
#add all these time series into the same dataframe
prices_ts <- data.frame(date,ap_ts, as_ts, offsupp_ts, 
                        genacc_ts, compacc_ts)
#check the database
glimpse(prices_ts)
########### transform all variables into their natural logaritm
logap <- log(prices1$allow_price)
logas <- log(prices1$allow_sold)
logoff <- log(prices1$off_supp)
loggen <- log(prices1$gen_acc)
logcomp <- log(prices1$comp_acc)
#transform natlog in time series
logap_ts <- ts(logap, start = c(2014, 2), end = c(2022,4), frequency = 4)
logas_ts <- ts(logas, start = c(2014, 2), end = c(2022,4), frequency = 4)
logoff_ts <- ts(logoff, start = c(2014, 2), end = c(2022,4), frequency = 4)
loggen_ts <- ts(loggen, start = c(2014, 2), end = c(2022,4), frequency = 4)
logcomp_ts <- ts(logcomp, start = c(2014, 2), end = c(2022,4), frequency = 4)
#merge all the variables in the same dataframe
logall <- data.frame(date, logap_ts, logas_ts, logoff_ts, 
                     loggen_ts, logcomp_ts)
#transform date into date format
logall$date <- as.Date(logall$date)
# save data set in a folder (if needed)
write.csv(logall, file= "out_data/logprices.csv")
################# create the dataset without the 0
######################## remove the NA
#select just the year where there are infos (08/20114 to 08/2022)
logall_cor <- dplyr::filter(logall, date >= as.Date("2014-08-01"), date <= as.Date("2023-12-01"))
# note that the first observation has been removed since the log of 0 is not determined
#select just the relevant variables
logall_cor <- select(logall_cor, logap_ts, logas_ts, logoff_ts, loggen_ts, logcomp_ts)
#create a variable of logcomp without the 0
logas_pure <- logall_cor$logas_ts
logap_pure <- logall_cor$logap_ts
logoff_pure <- logall_cor$logoff_ts
loggen_pure <- logall_cor$loggen_ts
logcomp_pure <- logall_cor$logcomp_ts
#transform it into time series
logas_purets <- ts(logas_pure, start = c(2014, 3), end = c(2022,4), frequency = 4)
logap_purets <- ts(logap_pure, start = c(2014, 3), end = c(2022,4), frequency = 4)
logoff_purets <- ts(logoff_pure, start = c(2014, 3), end = c(2022,4), frequency = 4)
loggen_purets <- ts(loggen_pure, start = c(2014, 3), end = c(2022,4), frequency = 4)
logcomp_purets <- ts(logcomp_pure, start = c(2014, 3), end = c(2022,4), frequency = 4)
# create a database with these variable
log_pure <- data_frame(logap_purets, logas_purets, logoff_purets, loggen_purets, logcomp_purets)
#control for COVID
covid <- create_dummy_ts(end_basic = c(2022,4), dummy_start = c(2020,1), dummy_end = c(2021,3),
                         sp = T, start_basic = c(2014,3), frequency = 4)
#add covid to the database
log_pure$covid <- covid
log_pure
####################################### DESCRIPTIVE STASTICS ###########################################################
#general info about the variables that will be analyzed

#Summarize raw variables together
summary(prices1[,c("allow_price","allow_sold","off_supp", "gen_acc", 
                   "comp_acc")])
#create a dataset
stargazer(prices1[,c("allow_price","allow_sold","off_supp", "gen_acc", 
                     "comp_acc")], type ="text", median = TRUE, digits = 2, title = "Raw Data")
# inquire more statistics about the variables 
desc1 <- describe(prices1[,c("allow_price","allow_sold","off_supp", "gen_acc", 
                             "comp_acc")], IQR = TRUE)
desc1 <- data.frame(desc1)
write.csv(desc1, "out_data/desc_stat.csv", row.names = F)
# insert the describe's results in a table
kable(desc1, digits = 2)

######################################## SINGLE VARIABLES ANALYSIS  #############################################################
# consider main variables alone.

######################### Allowances prices (ap)
# build separate dataframe for every variable to analyze it
allowances_prices <- select (prices_ts, ap_ts, date)
# look for the presence of outliers
invisible(capture.output(total_out_ap <- outliers(prices_ts$ap_ts)))
total_out_ap
# 5
# represent the allowances_prices
ap_plot <- plot.ts(ap_ts, col ="red", main ="Allowances_price",
                   xlab = "quarter", ylab = "price", axes = TRUE)
ap_plot
# put the results in the dataframe
allowances_prices$logap_ts <- logap_ts
# transform it into numeric value
# insert label
allowances_prices = apply_labels (allowances_prices,
                                  logap_ts = "log of allowances prices")
# check the structure of the dataframe 
str(allowances_prices)
# Represent the log of ap
logap_plot <- plot.ts(logap_ts, col ="red", main ="Allowances prices log", 
                      xlab = "Years", ylab = "log_price", axes = TRUE)
logap_plot
# compute the growth rate
logap_gr <- growth.rate(logap_ts, lag =1, simple = T)
# plot the ap growth rate
ap_gr_plot <- plot.ts(logap_gr, col ="red", main ="allowances price growth rate", 
                      xlab = "Years", ylab = "Growth precentage", axes = TRUE)
ap_gr_plot
# save it

######################### allowances sold (as)
# build separate dataframe for every variable to analyze it
allowances_sold <- select (prices_ts, as_ts, date)
# look for the presence of outliers
invisible(capture.output(total_out_as <- outliers(prices_ts$as_ts)))
total_out_as
# 6
# represent the allowances_prices
as_plot <- plot.ts(as_ts, col ="blue", main ="Allowances_sold",
                   xlab = "quarter", ylab = "price", axes = TRUE)
as_plot
# insert results in the dataframe
allowances_sold$logas_ts <- logas_ts
# labels
allowances_sold = apply_labels (allowances_sold,
                                logas_ts = "log of allowances sold")
# check the structure of the dataframe 
str(allowances_sold)
# save the dataframe
# Represent the log of as
logas_plot <- plot.ts(logas_ts, col ="blue", main ="Allowances sold log", 
                      xlab = "Years", ylab = "log_price", axes = TRUE)
logas_plot
# compute the growth rate
logas_gr <- growth.rate(logas_ts, lag =1, simple = T)
# plot the as growth rate
as_gr_plot <- plot.ts(logas_gr, col ="blue", main ="allowances sold growth rate", 
                      xlab = "Years", ylab = "Growth precentage", axes = TRUE)
as_gr_plot

######################### Offsets Supply (off)

# build separate dataframe for every variable to analyze it
offsets <- select (prices_ts, offsupp_ts, date)
# look for the presence of outliers
invisible(capture.output(total_out_off <- outliers(prices_ts$offsupp_ts)))
total_out_off
# 4
# represent the offsets
off_plot <- plot.ts(offsupp_ts, col ="green", main ="Number of offsets issued",
                    xlab = "quarter", ylab = "amount", axes = TRUE)
off_plot
# save it
# put the results in the dataframe
offsets$offsup_ts <- offsupp_ts
# labels
offsets = apply_labels (offsets,
                        offsupp_ts = "log of offsets issued")
# check the structure of the dataframe 
str(offsets)
# Represent the log of off
logoff_plot <- plot.ts(logoff_ts, col ="green", main ="log of offsets issued", 
                       xlab = "Years", ylab = "log_number", axes = TRUE)
logoff_plot
# save it
# compute the growth rate
logoff_gr <- growth.rate(logoff_ts, lag =1, simple = T)
# plot the off growth rate
off_gr_plot <- plot.ts(logoff_gr, col ="green", main ="Offsets issued growth rate", 
                       xlab = "Years", ylab = "Growth precentage", axes = TRUE)
off_gr_plot
# save it

######################### General account (genacc)

# build separate dataframe for every variable to analyze it
general <- select (prices_ts, genacc_ts, date)
# look for presence of outliers
invisible(capture.output(total_out_off <- outliers(prices_ts$genacc_ts)))
total_out_off
# 0
# represent the offsets
gen_plot <- plot.ts(genacc_ts, col ="orange", main ="Number of offsets in the general account",
                    xlab = "quarter", ylab = "amount", axes = TRUE)
gen_plot
# save it
# put the results in the dataframe
general$genacc_ts <- genacc_ts
# labels
offsets = apply_labels (offsets,
                        genacc_ts = "Log of offsets in general account")
# check the structure of the dataframe 
str(general)
# Represent the log of off
loggen_plot <- plot.ts(loggen_ts, col ="orange", main ="log of offsets in general account", 
                       xlab = "Years", ylab = "log_number", axes = TRUE)
loggen_plot
# save it
# compute the growth rate
loggen_gr <- growth.rate(loggen_ts, lag =1, simple = T)
# plot the off growth rate
gen_gr_plot <- plot.ts(loggen_gr, col ="orange", main ="Offsets in general account growth rate", 
                       xlab = "Years", ylab = "Growth precentage", axes = TRUE)
gen_gr_plot
# save it

######################### Compliance account (compacc)

# build separate dataframe for every variable to analyze it
compt <- select (prices_ts, compacc_ts, date)
# look for the presence of outliers
invisible(capture.output(total_out_off <- outliers(prices_ts$gcompacc_ts)))
total_out_off
# 0
# represent the offsets
comp_plot <- plot.ts(compacc_ts, col ="pink", main ="Offsets in the compliance account",
                     xlab = "quarter", ylab = "amount", axes = TRUE)
comp_plot
# save it
# put the results in the dataframe
compt$compacc_ts <- compacc_ts
# labels
offsets = apply_labels (offsets,
                        compacc_ts = "Log of offsets in compliance account")
# check the structure of the dataframe 
str(general)
# Represent the log of off
logcomp_plot <- plot.ts(logcomp_ts, col ="pink", main ="log of offsets in compliance account", 
                        xlab = "Years", ylab = "log_offset", axes = TRUE)
logcomp_plot
# save it
# compute the growth rate
logcomp_gr <- growth.rate(logcomp_ts, lag =1, simple = T)
# plot the off growth rate
comp_gr_plot <- plot.ts(logcomp_gr, col ="pink", main ="Offsets in compliance account growth rate", 
                        xlab = "Years", ylab = "Growth precentage", axes = TRUE)
comp_gr_plot
# save it

######################### Show all charts together
######### real values chart (for all the variables)
par(mfrow = c(2,3))
ap_plot <- plot.ts(ap_ts, col ="red", main ="Allowances_price",
                   xlab = "quarter", ylab = "price", axes = TRUE)
ap_plot
as_plot <- plot.ts(as_ts, col ="blue", main ="Allowances_sold",
                   xlab = "quarter", ylab = "price", axes = TRUE)
as_plot
off_plot <- plot.ts(offsupp_ts, col ="green", main ="Number of offsets issued",
                    xlab = "quarter", ylab = "price", axes = TRUE)
off_plot
gen_plot <- plot.ts(genacc_ts, col ="orange", main ="Number of offsets in the general account",
                    xlab = "quarter", ylab = "price", axes = TRUE)
gen_plot
comp_plot <- plot.ts(compacc_ts, col ="pink", main ="Offsets in the compliance account",
                     xlab = "quarter", ylab = "price", axes = TRUE)
comp_plot
#save them
pdf("img/values_plot.pdf")
par(mfrow = c(2,3))
ap_plot <- plot.ts(ap_ts, col ="red", main ="Allowances_price",
                   xlab = "quarter", ylab = "price", axes = TRUE)
ap_plot
as_plot <- plot.ts(as_ts, col ="blue", main ="Allowances_sold",
                   xlab = "quarter", ylab = "price", axes = TRUE)
as_plot
off_plot <- plot.ts(offsupp_ts, col ="green", main ="Number of offsets issued",
                    xlab = "quarter", ylab = "price", axes = TRUE)
off_plot
gen_plot <- plot.ts(genacc_ts, col ="orange", main ="Offsets in general account",
                    xlab = "quarter", ylab = "price", axes = TRUE)
gen_plot
comp_plot <- plot.ts(compacc_ts, col ="pink", main ="Offsets in compliance account",
                     xlab = "quarter", ylab = "price", axes = TRUE)
comp_plot
dev.off()

######### log charts (for all the variables)
par(mfrow = c(2, 3))
logap_plot <- plot.ts(logap_ts, col ="red", main ="Allowances prices log", 
                      xlab = "Years", ylab = "log_price", axes = TRUE)
logap_plot
logas_plot <- plot.ts(logas_ts, col ="blue", main ="Allowances sold log", 
                      xlab = "Years", ylab = "log_price", axes = TRUE)
logas_plot
logoff_plot <- plot.ts(logoff_ts, col ="green", main ="log of offsets issued", 
                       xlab = "Years", ylab = "log_number", axes = TRUE)
logoff_plot
loggen_plot <- plot.ts(loggen_ts, col ="orange", main ="log of offsets in general account", 
                       xlab = "Years", ylab = "log_number", axes = TRUE)
loggen_plot
logcomp_plot <- plot.ts(logcomp_ts, col ="pink", main ="log of offsets in compliance account", 
                        xlab = "Years", ylab = "log_offset", axes = TRUE)
logcomp_plot
# save them
pdf("img/log_plot.pdf")
par(mfrow = c(2, 3))
logap_plot <- plot.ts(logap_ts, col ="red", main ="Allowances prices log", 
                      xlab = "Years", ylab = "log_price", axes = TRUE)
logap_plot
logas_plot <- plot.ts(logas_ts, col ="blue", main ="Allowances sold log", 
                      xlab = "Years", ylab = "log_price", axes = TRUE)
logas_plot
logoff_plot <- plot.ts(logoff_ts, col ="green", main ="log of offsets issued", 
                       xlab = "Years", ylab = "log_number", axes = TRUE)
logoff_plot
loggen_plot <- plot.ts(loggen_ts, col ="orange", main ="log of offsets in general account", 
                       xlab = "Years", ylab = "log_number", axes = TRUE)
loggen_plot
logcomp_plot <- plot.ts(logcomp_ts, col ="pink", main ="log of offsets in compliance account", 
                        xlab = "Years", ylab = "log_offset", axes = TRUE)
logcomp_plot
dev.off()

######### growth rates charts (for all the variables), with a different command
par(mfrow = c(2, 3))
ap_gr_plot <- plot.ts(logap_gr, col ="red", main ="allowances price growth rate", 
                      xlab = "Years", ylab = "Growth precentage", axes = TRUE)
ap_gr_plot
as_gr_plot <- plot.ts(logas_gr, col ="blue", main ="allowances sold growth rate", 
                      xlab = "Years", ylab = "Growth precentage", axes = TRUE)
as_gr_plot
off_gr_plot <- plot.ts(logoff_gr, col ="green", main ="Offsets issued growth rate", 
                       xlab = "Years", ylab = "Growth precentage", axes = TRUE)
off_gr_plot
gen_gr_plot <- plot.ts(loggen_gr, col ="orange", main ="Offsets in general account growth rate", 
                       xlab = "Years", ylab = "Growth precentage", axes = TRUE)
gen_gr_plot
comp_gr_plot <- plot.ts(logcomp_gr, col ="pink", main ="Offsets in compliance account growth rate", 
                        xlab = "Years", ylab = "Growth precentage", axes = TRUE)
comp_gr_plot
# save it
pdf("img/diff_plot.pdf")
par(mfrow = c(2, 3))
ap_gr_plot <- plot.ts(logap_gr, col ="red", main ="allowances price growth rate", 
                      xlab = "Years", ylab = "Growth precentage", axes = TRUE)
ap_gr_plot
as_gr_plot <- plot.ts(logas_gr, col ="blue", main ="allowances sold growth rate", 
                      xlab = "Years", ylab = "Growth precentage", axes = TRUE)
as_gr_plot
off_gr_plot <- plot.ts(logoff_gr, col ="green", main ="Offsets issued growth rate", 
                       xlab = "Years", ylab = "Growth precentage", axes = TRUE)
off_gr_plot
gen_gr_plot <- plot.ts(loggen_gr, col ="orange", main ="Offsets in general account growth rate", 
                       xlab = "Years", ylab = "Growth precentage", axes = TRUE)
gen_gr_plot
comp_gr_plot <- plot.ts(logcomp_gr, col ="pink", main ="Offsets in compliance account growth rate", 
                        xlab = "Years", ylab = "Growth precentage", axes = TRUE)
comp_gr_plot
dev.off()

#clear the work space
dev.off()

########################### Plot all the logs in the same chart
# Draw first time series
logall_plot <- plot(logall$date,                              # Draw first time series
                    logall$logap_ts,
                    type = "l",
                    col = "red",
                    ylim = c(- 0, 20),
                    xlab = "Year",
                    ylab = "log") 
# Draw  the other time series
lines(logall$date,                             # Draw 2 time series
      logall$logas_ts,
      type = "l",
      col = "blue")
lines(logall$date,                             # Draw 3 time series
      logall$logoff_ts,
      type = "l",
      col = "green")
lines(logall$date,                             # Draw 4 time series
      logall$loggen_ts,
      type = "l",
      col = "orange")
lines(logall$date,                             # Draw 5 time series
      logall$logcomp_ts,
      type = "l",
      col = "pink")
title(main = "all variables log")# add the title
par(xpd = TRUE)
legend("bottomright", legend = c("logap", "logas", "logoff", "loggen", "logcomp"), 
       col = c("red", "blue", "green", "orange", "pink"), pch = 4, lty =1, cex = 0.8 )

#save it
pdf("img/all_var.pdf")
logall_plot <- plot(logall$date,                              # Draw first time series
                    logall$logap_ts,
                    type = "l",
                    col = "red",
                    ylim = c(- 0, 20),
                    xlab = "Year",
                    ylab = "log")
# Draw  the other time series
lines(logall$date,                             # Draw 2 time series
      logall$logas_ts,
      type = "l",
      col = "blue")
lines(logall$date,                             # Draw 3 time series
      logall$logoff_ts,
      type = "l",
      col = "green")
lines(logall$date,                             # Draw 4 time series
      logall$loggen_ts,
      type = "l",
      col = "orange")
lines(logall$date,                             # Draw 5 time series
      logall$logcomp_ts,
      type = "l",
      col = "pink")
title(main = "all variables log")
dev.off()

####################################### SEASONALITY and TRENDS ################################################
################  Plots to look for seasonality and trends
#ap_ts
logap_trend <- decompose(logap_ts)
plot(logap_trend)
#as_ts
logas_trend <- decompose(logas_ts)
plot(logas_trend)
#off_supp
logoff_trend <- decompose(logoff_ts)
plot(logoff_trend)
#genacc
loggen_trend <- decompose(loggen_ts)
plot(loggen_trend)
#compacc
logcomp_trend <- decompose(logcomp_purets)
plot(logcomp_trend)

################ SEASONALITY
############# Seasonality test - logged variables
isSeasonal(logas_purets, freq = 4) #FALSE
isSeasonal(logap_purets, freq = 4) #FALSE
isSeasonal(logoff_purets, freq = 4) #FALSE
isSeasonal(loggen_purets, freq = 4) #FALSE
isSeasonal(logcomp_purets, freq = 4) #FALSE
#no seasonality for any data

################### TREND
#### Use Mann-Kendall test to spot trend.
#H0: there is not a trend
#H1: a trend (positive or negative) exists
#if p-value < a reject H0
#tau is the strenght of the trend
############### natlogs
mk.test(logas_purets) #can not reject H0, no trend (0.4767)
mk.test(logap_purets) #reject H0, trend (2.431e-13)
mk.test(logoff_purets) #can not reject H0, no trend (0.8125)
mk.test(loggen_purets) #reject H0, trend (3.494e-08)
mk.test(logcomp_purets) #can not reject H0 for 0.05, no trend (0.1381)
#clear the environment
dev.off()

####################################### TREND ANALYSIS ##########################################################
#spot the trend for all the variables
trend(logap_purets) #trend
trend(logas_purets) #no trend, seasonality?
trend(logoff_purets) #no trend
trend(loggen_purets) #trend
trend(logcomp_purets) #trend?
#detrend the series

####### ATTENTION ON LOGCOMP
#it appears to have a quadratic trend
# de-trending
#set logcomp as time
t = time(logcomp_purets)
#transform it into quadratic
t2 = t^2
#(linear) model the trend
model2 = lm(logcomp_purets ~ t +t2)
#show it
summary(model2)
#extract the values
expected <- fitted.values(model2)
#change to numeric format
expectedn <- as.numeric(expected)
#change to ts object
expected_ts <- ts(expectedn, start = c(2014, 2), end = c(2022,4), frequency = 4)
#de-trend the series
detlogcomp_ts <- (logcomp_purets - expected_ts)
#show the new time series
plot(detlogcomp_ts)
#mk.test
mk.test(detlogcomp_ts)
#plot the original data and the trend
plot(ts(fitted(model2)), ylim=c(min(c(fitted(model2), as.vector(logcomp_purets))), max(c(fitted(model2), as.vector(logcomp_purets)))), 
     ylab='y', main = "logcomp")
lines(as.vector(logcomp_purets),type="o")
#compute the residuals
res.model2 = rstudent(model2)
plot(y = res.model2, x = as.vector(time(logcomp_purets)),xlab = 'Time', 
     ylab='Studentized Residuals of model2',type='p')
abline(h=0)
#histogram for the residual
hist(res.model2, xlab = 'Standardized Residuals')
#normality chart for the residuals
qqnorm(res.model2)
qqline(res.model2, col=2, lwd=1, lty=2) 
#build a datafram with the detrended variable
lognt_purets <- data.frame(logap_purets, logas_purets, logoff_purets, 
                           loggen_purets, detlogcomp_ts)
#analyze the trend
trend(detlogcomp_ts)
#remove the structural break
detlogcomp21_ts <- ts(detlogcomp_ts, start = c(2014, 2), end = c(2021,1), frequency = 4)
#show the detrended variable
trend(detlogcomp21_ts)

##### create the dummy variable for Q1 2021
dummyts <- create_dummy_ts(end_basic = c(2022,3), dummy_start = c(2022,2), dummy_end = c(2022,4),
                sp = T, start_basic = c(2014,3), frequency = 4)
# add the dummy to the database
log_pure$dummyts <- dummyts
log_pure
plot.ts(detlogcomp_ts, main ="allowances price growth rate", 
        xlab = "Years", ylab = "Growth precentage", axes = TRUE)

#######################################  CORRELATION  ###########################################################
# study the correlation among all the variables with the pearson coefficient
# to have an idea of their relation

################### NATLOGS
#create a database with the correlation of the natlogs
corrlogs <- cor(logall_cor)
#show them
corrlogs
#plot the correlogram of all the natlogs
corrplot(corrlogs, title = "Log Correlation", type = "lower", method = "color", 
         outline = T, addCoef.col = "white", tl.col = "black")
#save it
pdf("img/log_corr.pdf")
corrplot(corrlogs, type = "lower", method = "color", 
         outline = T, addCoef.col = "white", tl.col = "black")
dev.off()
################### VARIABLES
price_cor <- select(prices1, allow_price, allow_sold, 
                    off_supp, gen_acc, comp_acc)
corvar <- cor(price_cor)
#plot it
corrplot(corvar, type = "lower", method = "color", 
         outline = T, addCoef.col = "white", tl.col = "black")
#save it
pdf("img/var_corr.pdf")
corrplot(corvar, type = "lower", method = "color", 
         outline = T, addCoef.col = "white", tl.col = "black")
dev.off()
##### correlation between different loggen - logcomp and allow pric
diffacc <- (loggen_pure - logcomp_pure)
diffacc_ts <- ts(diffacc, start = c(2014, 3), end = c(2022,4), frequency = 4)
cor(diffacc_ts, logap_purets)
# correlation: 0.06826428.
#######################################  STATIONARITY  ###########################################################
# Examine Stationarity
##################### AUTOCORRELATION
#plot the autocorrelation to have an idea of the stationarity of the data
# clear the space
dev.off()
# set the plot space in a way to contain 2 charts
par(mfrow = c(3, 2))
##### Allowances price
acf(na.omit(logap_ts), lag.max = 34, plot = F)
acf(na.omit(logap_ts), lag.max = 34, main ="log allowances price autocorrelation")
##### Allowances sold
acf(na.omit(logas_ts), lag.max = 35, plot = F)
acf(na.omit(logas_ts), lag.max = 35, main ="log allowances sold autocorrelation")
##### offsets supply
# compute autocorrelation and plot it
acf(na.omit(offsupp_ts), lag.max = 35, plot = F)
acf(na.omit(offsupp_ts), lag.max = 35, main ="log of offsets supply autocorrelation")
##### offsets general account
# compute autocorrelation and plot it
acf(na.omit(genacc_ts), lag.max = 35, plot = F)
acf(na.omit(genacc_ts), lag.max = 35, main ="log levels of offsets in general account autocorrelation")
##### compliance account
# compute autocorrelation and plot it
acf(na.omit(compacc_ts), lag.max = 35, plot = F)
acf(na.omit(compacc_ts), lag.max = 35, main ="log levels of offsets in compliance account autocorrelation")
#detrended logcomp
acf(na.omit(detlogcomp21_ts), lag.max = 34, plot = F)
acf(na.omit(detlogcomp21_ts), lag.max = 34, main ="detrended log levels of offsets in compliance account autocorrelation")
# save it
pdf("img/autocorr.pdf")
par(mfrow = c(3, 3))
acf(na.omit(logap_ts), lag.max = 34, plot = F)
acf(na.omit(logap_ts), lag.max = 34, main ="Allowances price log autocorrelation")
acf(na.omit(logas_ts), lag.max = 35, plot = F)
acf(na.omit(logas_ts), lag.max = 35, main ="Allowances sold log autocorrelation")
acf(na.omit(offsupp_ts), lag.max = 35, plot = F)
acf(na.omit(offsupp_ts), lag.max = 35, main ="Offsets supply log autocorrelation")
acf(na.omit(genacc_ts), lag.max = 35, plot = F)
acf(na.omit(genacc_ts), lag.max = 35, main ="Offsets in general acc log autocorrelation")
acf(na.omit(compacc_ts), lag.max = 35, plot = F)
acf(na.omit(compacc_ts), lag.max = 35, main ="Offsets in compliance acc log autocorrelation")
acf(na.omit(detlogcomp21_ts), lag.max = 34, plot = F)
acf(na.omit(detlogcomp21_ts), lag.max = 34, main ="detrended log levels of offsets in compliance account autocorrelation")
dev.off()

# clear the space
dev.off()

##################### DICEKY-FUELLER TEST
# Run an augmented Dickey-Fueller test on the logged levels and on the first differences of the log
# Dickey-Fuller test on the logged levels
# compare the value with tau3
# H0: there is a unit root in the logged levels --> nonstationarity

######################### allowance prices
#ADF
summary(ur.df(logap_purets, 
              type = "trend", 
              lags = 8, 
              selectlags = "BIC"))
#interpret the results
interp_urdf(ur.df(logap_purets, 
                  type = "trend", 
                  lags = 8, 
                  selectlags = "BIC"))
# result: 2.3731 4.5005 5.0933
#try other tests to confirm the results
#adf test, =/ command
adf.test(logap_purets)
#pp test
pp.test(logap_purets, type = "Z(alpha)")
pp.test(logap_purets, type = "Z(t_alpha")
#kpss test
kpss.test(logap_purets, null = "Trend")
#test for unit roots variance ratio (the rho is the variance, the p-value is as usual)
bvr.test(logap_purets)

######################### allowance sold
# ADF
summary(ur.df(logas_purets, 
              type = "trend", 
              lags = 8, 
              selectlags = "BIC"))
interp_urdf(ur.df(logas_purets, 
                  type = "trend", 
                  lags = 8, 
                  selectlags = "BIC"))
# result: -4.0289 7.3448 10.355
#try other tests to confirm the results
#adf test, =/ command
adf.test(logas_purets)
adf.test(logas_purets)
#pp test
pp.test(logas_purets, type = "Z(alpha)")
pp.test(logas_purets, type = "Z(t_alpha)")
#kpss test
kpss.test(logas_purets)
#test for unit roots variance ratio (the rho is the variance, the p-value is as usual)
bvr.test(logas_purets)

######################### offsets
#ADF
summary(ur.df(logoff_purets, 
              type = "trend", 
              lags = 8, 
              selectlags = "BIC"))
interp_urdf(ur.df(logoff_purets, 
                  type = "trend", 
                  lags = 8, 
                  selectlags = "BIC"))
# result: -1.7507 2.63 3.9187
#try other tests to confirm the results
#adf test, =/ command
adf.test(logoff_purets)
#pp test
pp.test(logoff_purets, type = "Z(alpha)")
pp.test(logoff_purets, type = "Z(t_alpha)")
#kpss test
kpss.test(logoff_purets, null = "Level")
#test for unit roots variance ratio (the rho is the variance, the p-value is as usual)
bvr.test(logoff_purets)

######################### general account
# ADF
summary(ur.df(loggen_purets, 
              type = "trend", 
              lags = 8, 
              selectlags = "BIC"))
interp_urdf(ur.df(loggen_purets, 
                  type = "trend", 
                  lags = 8, 
                  selectlags = "BIC"))
# result: -1.3502 0.9872 1.3681
#try other tests to confirm the results
#adf test, =/ command
adf.test(loggen_purets)
#pp test
pp.test(loggen_purets, type = "Z(alpha)")
pp.test(loggen_purets, type = "Z(t_alpha)")
#kpss test
kpss.test(loggen_purets)
#test for unit roots variance ratio (the rho is the variance, the p-value is as usual)
bvr.test(loggen_purets)

######################### compliance account (removed 1 period)
#ADF
summary(ur.df(logcomp_purets, 
              type = "trend", 
              lags = 8, 
              selectlags = "BIC"))
interp_urdf(ur.df(logcomp_purets, 
                  type = "trend", 
                  lags = 8, 
                  selectlags = "BIC"))
# result: -3.8153 5.8072 8.7078
#try other tests to confirm the results
#adf test, =/ command
adf.test(logcomp_purets)
#pp test
pp.test(logcomp_purets, type = "Z(alpha)")
pp.test(logcomp_purets, type = "Z(t_alpha)")
#kpss test
kpss.test(logcomp_purets)
#test for unit roots variance ratio (the rho is the variance, the p-value is as usual)
bvr.test(logcomp_purets)
#detrended logcomp
#ADF
summary(ur.df(detlogcomp_ts, 
              type = "trend", 
              lags = 8, 
              selectlags = "BIC"))
#interpret the results
interp_urdf(ur.df(detlogcomp_ts, 
                  type = "trend", 
                  lags = 8, 
                  selectlags = "BIC"))
# result: 2.3731 4.5005 5.0933
#try other tests to confirm the results
#adf test, =/ command
adf.test(detlogcomp_ts)
#pp test
pp.test(detlogcomp_ts, type = "Z(alpha")
#kpss test
kpss.test(detlogcomp_ts, null = "Level")
#test for unit roots variance ratio (the rho is the variance, the p-value is as usual)
bvr.test(detlogcomp_ts)

#logcomp with no trend and no structural break
#ADF
summary(ur.df(detlogcomp21_ts, 
              type = "trend", 
              lags = 8, 
              selectlags = "BIC"))
#interpret the results
interp_urdf(ur.df(detlogcomp21_ts, 
                  type = "trend", 
                  lags = 8, 
                  selectlags = "BIC"))
# result: 2.3731 4.5005 5.0933
#try other tests to confirm the results
#adf test, =/ command
adf.test(detlogcomp21_ts)
#pp test
pp.test(detlogcomp21_ts, type = "Z(t_alpha)")
#kpss test
kpss.test(detlogcomp21_ts, null = "Level")
#test for unit roots variance ratio (the rho is the variance, the p-value is as usual)
bvr.test(detlogcomp21_ts)

################################ DIFFERENCING I(1) ###############################################
#to transform nonstationary series into stationry the techniques it so difference
#in this case a first order differencing will be made
#this is done for testing if an ARDL model can be implemented

######################### allowance prices
diffap <- diff(logap_purets)
summary(ur.df(diffap, 
              type = "trend", 
              lags = 8, 
              selectlags = "BIC"))
interp_urdf(ur.df(diffap, 
                  type = "trend", 
                  lags = 8, 
                  selectlags = "BIC"))
#try other tests to confirm the results
#adf test, =/ command
adf.test(diffap)
# p-value 0.01 so i reject the null hypothesis
pp.test(diffap, type = "Z(alpha)")
#p-value 0.01295 so i reject the null hypothesis of nonstationrairty 
pp.test(diffap, type = "Z(t_alpha)")
#p-value 0.02306 so i reject the null hypothesis of nonstationrairty
kpss.test(diffap, null = "Level")
# with the detrended data

######################### allowance sold
# ADF
diffas <- diff(logas_purets)
summary(ur.df(diffas, 
              type = "trend", 
              lags = 8, 
              selectlags = "BIC"))
interp_urdf(ur.df(diffas, 
                  type = "trend", 
                  lags = 8, 
                  selectlags = "BIC"))
#try other tests to confirm the results
#adf test, =/ command
adf.test(diffas)
# p-value 0.01 so i reject the null hypothesis
pp.test(diffas, type = "Z(alpha)")
#p-value 0.01295 so i reject the null hypothesis of nonstationrairty 
pp.test(diffas, type = "Z(t_alpha)")
#p-value 0.02306 so i reject the null hypothesis of nonstationrairty
kpss.test(diffas, null = "Level")

######################### offsets
#ADF
diffoff <- diff(logoff_purets)
summary(ur.df(diffoff, 
              type = "trend", 
              lags = 8, 
              selectlags = "BIC"))
interp_urdf(ur.df(diffoff, 
                  type = "trend", 
                  lags = 8, 
                  selectlags = "BIC"))
#try other tests to confirm the results
#adf test, =/ command
adf.test(diffoff)
# p-value 0.01 so i reject the null hypothesis
pp.test(diffoff, type = "Z(alpha)")
#p-value 0.01295 so i reject the null hypothesis of nonstationrairty 
pp.test(diffoff, type = "Z(t_alpha)")
#p-value 0.02306 so i reject the null hypothesis of nonstationrairty
kpss.test(diffoff, null = "Level")

######################### general account
diffgen <- diff(loggen_purets)
summary(ur.df(diffgen, 
              type = "trend", 
              lags = 8, 
              selectlags = "BIC"))
interp_urdf(ur.df(diffgen, 
                  type = "trend", 
                  lags = 8, 
                  selectlags = "BIC"))
#try other tests to confirm the results
#adf test, =/ command
adf.test(diffgen)
pp.test(diffgen, type = "Z(alpha)")
pp.test(diffgen, type = "Z(t_alpha)")
kpss.test(diffgen, null = "Level")

######################### compliance account (removed 1 period)
#ADF
diffcomp <- diff(logcomp_purets)
summary(ur.df(diffcomp, 
              type = "trend", 
              lags = 8, 
              selectlags = "BIC"))
interp_urdf(ur.df(diffcomp, 
                  type = "trend", 
                  lags = 8, 
                  selectlags = "BIC"))
#try other tests to confirm the results
#adf test, =/ command
adf.test(diffcomp)
pp.test(diffcomp, type = "Z(alpha)")
pp.test(diffcomp, type = "Z(t_alpha")
kpss.test(diffcomp, null = "Level")
kpss.test(diffcomp, null = "Trend")
ndiffs(logap_ts, test = "kpss")
#perform test with detrending
bvr.test(diffcomp, detrend = TRUE)
# detrended logcomp
diffdetlogcomp <- diff(detlogcomp_ts)
diffdetlogcomp <- ts(diffdetlogcomp, start = c(2014, 2), end = c(2021,1), frequency = 4)
summary(ur.df(diffdetlogcomp, 
              type = "trend", 
              lags = 8, 
              selectlags = "BIC"))
interp_urdf(ur.df(diffdetlogcomp, 
                  type = "trend", 
                  lags = 8, 
                  selectlags = "BIC"))
#try other tests to confirm the results
#adf test, =/ command
adf.test(diffdetlogcomp)
# pp-tests
pp.test(diffdetlogcomp, type = "Z(alpha)")
pp.test(diffdetlogcomp, type = "Z(t_alpha)")
# kpss test
kpss.test(diffdetlogcomp, null = "Level")

########## MODEL TESTING
##################################### EXTERNAL TREND ###############################################
#nt = no logcomp detrended mode, but trend integrated in the model
##################################### COMPUTE THE RIGHT LAG LENGTH ##################################
#compute the bound Wald test for cointegration
#this command estimated the ARDL, the related ECM, the right lag length and the cointegration test
ardlBICnt <- ardlBound(data = log_pure, logap_purets ~ logas_purets + logoff_purets + 
          loggen_purets + logcomp_purets + trend(logcomp_purets), case = 3, p = NULL,
          remove = NULL, autoOrder = FALSE, ic = "BIC" , max.p = 4, max.q = 3, 
          ECM = TRUE, stability = TRUE)
#BIC selection: 4, 4, 4,4,3
ardlAICmt <- ardlBound(data = log_pure, logap_purets ~ logas_purets + logoff_purets + 
                       loggen_purets + logcomp_purets + trend(logcomp_purets), case = 3, p = NULL,
                     remove = NULL, autoOrder = FALSE, ic = "AIC" , max.p = 4, max.q = 3, 
                     ECM = TRUE, stability = TRUE)
#AIC selection: 4, 4, 4,4,3

########################################### ARDL ###################################################
#estimate the ARDL Model with shorter lags
ardlnt <- ardl(logap_purets ~ logas_purets + logoff_purets + 
                 loggen_purets + logcomp_purets + trend(logap_purets), data = log_pure, order = c(4, 4, 4,4,3))
ardlntsum <- summary(ardlnt)
se_ardlnt <- ardlntsum$coefficients[,2]
#plot to see the difference the model together and the the real price
#fv_sh <- fitted.values(ardlsh)
#fv_sh <- ts(fv_sh, start = c(2014, 2), end = c(2020,1), frequency = 4)
#plot(fv_sh)
fv_nt <- fitted.values(ardlnt)
fv_nt <- ts(fv_nt, start = c(2014, 2), end = c(2020,1), frequency = 4)
#plot the model estimation and the real values
plot.ts(fv_nt,type="l",col="red", main ="fit_val_vs_act_val", 
        xlab = "Years", ylab = "log", axes = TRUE)
lines(logap_purets,col="green")
#lines(fv_sh, col = "blue")
###### residual analysis (long lag model)
#save the residual
resnt <- ardlnt$residuals
resnt2 <- resnt^2
#show them
summary(resnt)
# look for residuals autocorrelation
acf(ardlnt$residuals, type = "correlation")
#save it
pdf("img/res_corr.pdf")
acf(ardlnt$residuals, type = "correlation")
dev.off()
# test for it with Durban Watson Test
dwtest(ardlnt)
# no correlation among residuals

########################################## COINTEGRATION ############################################
#perform a bound test to see if there is cointegration (long-model)
# if F > I(1) -> cointegration, if F < I(0) -> no cointegration
#if I(0) < F < I(1) test is not specified 
#F bound test
bounds_f_test(ardlnt, alpha = 0.05, case = 5)
# T bounds test
bounds_t_test(ardlnt, alpha = 0.05, case = 5)

########################################### DETRENDED ANALYSIS ###########################################
#dt = logcomp already detrended, without dummy
### add covid to lognt_purets
lognt_purets$covid <- covid
##########################################################################################################
#this command estimated the ARDL, the related ECM, the right lag length and the cointegration test
ardlAICdt <- ardlBound(data = lognt_purets, logap_purets ~ logas_purets + logoff_purets + 
                       loggen_purets + detlogcomp_ts, case = 3, p = NULL,
                     remove = NULL, autoOrder = FALSE, ic = "BIC" , max.p = 4, max.q = 3, 
                     ECM = TRUE, stability = TRUE)
#BIC selection: 4,4,4,4,3
ardlAICdt <- ardlBound(data = lognt_purets, logap_purets ~ logas_purets + logoff_purets + 
                       loggen_purets + detlogcomp_ts, case = 3, p = NULL,
                     remove = NULL, autoOrder = FALSE, ic = "AIC" , max.p = 4, max.q = 3, 
                     ECM = TRUE, stability = TRUE)
#AIC selection: 4,4,4,4,3
########################################### ARDL ###################################################
ardldt <- ardl(logap_purets ~ logas_purets + logoff_purets + 
                 loggen_purets + detlogcomp_ts + covid, data = lognt_purets, order = c(4,4,4,4,3,0))
summary(ardldt)
#fitted values
fv_dt <- fitted.values(ardldt)
fv_dt <- ts(fv_dt, start = c(2014, 2), end = c(2020,1), frequency = 4)
#plot the model estimation and the real values
plot.ts(fv_dt,type="l",col="orange", main ="Offsets in general account growth rate", 
        xlab = "Years", ylab = "Growth precentage", axes = TRUE)
lines(logap_purets,col="green")
#lines(fv_sh, col = "blue")

###### residual analysis (long lag model)
#save the residual
resdt <- ardldt$residuals
resdt2 <- resdt^2
#show them
summary(resdt)
# look for residuals autocorrelation
acf(ardldt$residuals, type = "correlation")
#save it
pdf("img/res_corr.pdf")
acf(ardldt$residuals, type = "correlation")
dev.off()
# test for it with Durban Watson Test
dwtest(ardldt)
# no correlation among residuals

########################################## COINTEGRATION ############################################
#perform a bound test to see if there is cointegration (short-model)
# if F > I(1) -> cointegration, if F < I(0) -> no cointegration
#if I(0) < F < I(1) test is not specified 
ardldt
#double check the results of the bound test
bounds_f_test(ardldt, alpha = 0.05, case = 2)
# double check with the results of the t test
bounds_t_test(ardldt, alpha = 0.05, case = 3)

############################# DETRENDED AND DUMMY VARIABLE ANALYSIS #########################
#dtd: logcomp detrended and dummy vriable added for structural break
#add the dummy to the database
lognt_purets$dummyts <- dummyts
#############################################################################################
#this command estimated the ARDL, the related ECM, the right lag length and the cointegration test
ardlBICdtd <- ardlBound(data = lognt_purets, logap_purets ~ logas_purets + logoff_purets + 
                         loggen_purets + detlogcomp_ts, case = 3, p = NULL,
                       remove = NULL, autoOrder = FALSE, ic = "BIC" , max.p = 4, max.q = 3, 
                       ECM = TRUE, stability = TRUE)
#BIC selection: 4,4,4,4,3
ardlAICdtd <- ardlBound(data = lognt_purets, logap_purets ~ logas_purets + logoff_purets + 
                         loggen_purets + detlogcomp_ts, case = 3, p = NULL,
                       remove = NULL, autoOrder = FALSE, ic = "AIC" , max.p = 4, max.q = 3, 
                       ECM = TRUE, stability = TRUE)
#AIC selection: 4,4,4,4,3
########################################### ARDL ###################################################
ardldtd <- ardl(logap_purets ~ logas_purets + logoff_purets + 
                 loggen_purets + detlogcomp_ts + dummyts + covid, 
                 data = lognt_purets, order = c(4,4,4,4,3,0,0))
summary(ardldtd)
#fitted values
fv_dtd <- fitted.values(ardldtd)
fv_dtd <- ts(fv_dtd, start = c(2014, 2), end = c(2020,1), frequency = 4)
#plot the model estimation and the real values
plot.ts(fv_dtd,type="l",col="pink", main ="fit_var_vs_act_var", 
        xlab = "Years", ylab = "log", axes = TRUE)
lines(logap_purets,col="green")

###### residual analysis (long lag model)
#save the residual
resdtd <- ardldtd$residuals
resdtd2 <- resdtd^2
#show them
summary(resdtd)
# look for residuals autocorrelation
acf(ardldtd$residuals, type = "correlation")
#save it
pdf("img/res_corr.pdf")
acf(ardldtd$residuals, type = "correlation")
dev.off()
# test for it with Durban Watson Test
dwtest(ardldtd)
# no correlation among residuals

########################################## COINTEGRATION ############################################
#perform a bound test to see if there is cointegration (short-model)
# if F > I(1) -> cointegration, if F < I(0) -> no cointegration
#if I(0) < F < I(1) test is not specified 
ardldtd
#double check the results of the bound test
bounds_f_test(ardldtd, alpha = 0.05, case = 2)
# double check with the results of the t test
bounds_t_test(ardldtd, alpha = 0.05, case = 3)

########################################### WITHOUT LOGGEN ###########################################
#ng = logcomp already detrended, without dummy
##########################################################################################################
#this command estimated the ARDL, the related ECM, the right lag length and the cointegration test
ardlAICng <- ardlBound(data = lognt_purets, logap_purets ~ logas_purets + logoff_purets + 
                       detlogcomp_ts, case = 3, p = NULL,
                       remove = NULL, autoOrder = FALSE, ic = "BIC" , max.p = 4, max.q = 3, 
                       ECM = TRUE, stability = TRUE)
#BIC selection: 4,4,3,4
ardlAICng <- ardlBound(data = lognt_purets, logap_purets ~ logas_purets + logoff_purets + 
                         + detlogcomp_ts, case = 3, p = NULL,
                       remove = NULL, autoOrder = FALSE, ic = "AIC" , max.p = 4, max.q = 3, 
                       ECM = TRUE, stability = TRUE)
#AIC selection: 4,4,3,4
ardlBoundOrders(data = lognt_purets, logap_purets ~ logas_purets + logoff_purets + 
                  + detlogcomp_ts, ic = "BIC", max.q = 4, max.p =4)
########################################### ARDL ###################################################
ardlng <- ardl(logap_purets ~ logas_purets + logoff_purets  
                + detlogcomp_ts + dummyts + covid, data = lognt_purets, order = c(4,4,3,4,0,0))
summary(ardlng)
ardlngsh <- ardl(logap_purets ~ logas_purets + logoff_purets  
               + detlogcomp_ts + dummyts + covid, data = lognt_purets, order = c(1,0,1,0,0,0))
summary(ardlngsh)
#fitted values
fv_ng <- fitted.values(ardlng)
fv_ng <- ts(fv_ng, start = c(2014, 2), end = c(2020,1), frequency = 4)
fv_ngsh <- fitted.values(ardlngsh)
fv_ngsh <- ts(fv_ngsh, start = c(2014, 2), end = c(2020,1), frequency = 4)
#plot the model estimation and the real values
plot.ts(fv_ng,type="l",col="orange", main ="Offsets in general account growth rate", 
        xlab = "Years", ylab = "Growth precentage", axes = TRUE)
lines(logap_purets,col="green")
lines(fv_ngsh, col = "black")
#lines(fv_sh, col = "blue")
vif(ardlngsh)
#choice ardlngsh

###### residual analysis (long lag model)
#save the residual
resngsh <- ardlngsh$residuals
resngsh2 <- resngsh^2
#show them
summary(resngsh)
# look for residuals autocorrelation
acf(ardlngsh$residuals, type = "correlation")
#save it
pdf("img/res_corr1.pdf")
acf(ardlngsh$residuals, type = "correlation", main = "Residual Autocorrelation")
dev.off()
# test for it with Durban Watson Test
dwtest(ardlngsh)
# no correlation among residuals
#Breusch pagan test
bptest(ardlngsh)
#presence of heteroskedasticity
#compute robust standard error and re-estimate the model
ardlngsh_rob <- coeftest(ardlngsh, vcov = sandwich)
#normality of the residuals
jarque.bera.test(ardlngsh$residuals)
#residuals are normally distributed
#compute the cumsum for the residuals
library(qcc)
cusum1 <- cumsum(ardlngsh$residuals)
#cusum plot
cusum(ardlngsh$residuals)

########################################## COINTEGRATION ############################################
#perform a bound test to see if there is cointegration (short-model)
# if F > I(1) -> cointegration, if F < I(0) -> no cointegration
#if I(0) < F < I(1) test is not specified 
ardlngsh
#double check the results of the bound test
bounds_f_test(ardlngsh, alpha = 0.05, case = 2)
# double check with the results of the t test
bounds_t_test(ardlngsh, alpha = 0.05, case = 3)

########################################### WITHOUT LOGCOMP ###########################################
#nc = logcomp is not considered, since it may be determined by the cap
##########################################################################################################
#this command estimated the ARDL, the related ECM, the right lag length and the cointegration test
ardlAICnc <- ardlBound(data = lognt_purets, logap_purets ~ logas_purets + logoff_purets + 
                         loggen_purets, case = 3, p = NULL,
                       remove = NULL, autoOrder = FALSE, ic = "BIC" , max.p = 4, max.q = 3, 
                       ECM = TRUE, stability = TRUE)
#BIC selection: 3,3,2,3
ardlAICnc <- ardlBound(data = lognt_purets, logap_purets ~ logas_purets + logoff_purets + 
                         + loggen_purets, case = 3, p = NULL,
                       remove = NULL, autoOrder = FALSE, ic = "AIC" , max.p = 4, max.q = 3, 
                       ECM = TRUE, stability = TRUE)
#AIC selection: 3,3,2,3
ardlBoundOrders(data = lognt_purets, logap_purets ~ logas_purets + logoff_purets + 
                  + loggen_purets, ic = "BIC", max.q = 4, max.p =4)
########################################### ARDL ###################################################
ardlnc <- ardl(logap_purets ~ logas_purets + logoff_purets  
               + loggen_purets + covid, data = lognt_purets, order = c(3,3,2,3,0))
summary(ardlnc)
ardlncsh <- ardl(logap_purets ~ logas_purets + logoff_purets  
                 + loggen_purets + covid, data = log_pure, order = c(1,2,1,1,0))
summary(ardlncsh)
#fitted values
fv_nc <- fitted.values(ardlnc)
fv_nc <- ts(fv_nc, start = c(2014, 2), end = c(2020,1), frequency = 4)
fv_ncsh <- fitted.values(ardlncsh)
fv_ncsh <- ts(fv_ncsh, start = c(2014, 2), end = c(2020,1), frequency = 4)
#plot the model estimation and the real values
plot.ts(fv_nc,type="l",col="deeppink", main ="Offsets in general account growth rate", 
        xlab = "Years", ylab = "Growth precentage", axes = TRUE)
lines(logap_purets,col="green")
lines(fv_ncsh, col = "chocolate4")
#lines(fv_sh, col = "blue")
vif(ardlncsh)
#choice ardlngsh

###### residual analysis (long lag model)
#save the residual
resncsh <- ardlncsh$residuals
resncsh2 <- resncsh^2
#show them
summary(resncsh)
# look for residuals autocorrelation
acf(ardlncsh$residuals, type = "correlation")
#save it
pdf("img/res_corr_ncsh.pdf")
acf(ardlngsh$residuals, type = "correlation", main = "Residual Autocorrelation")
dev.off()
# test for it with Durban Watson Test
dwtest(ardlncsh)
# no correlation among residuals
#Breusch pagan test
bptest(ardlncsh)
#homoskedasticity
#normality of the residuals
jarque.bera.test(ardlncsh$residuals)
#residuals are normally distributed
#compute the cumsum for the residuals
cusumncsh <- cumsum(ardlncsh$residuals)
#cusum plot
cusum(ardlncsh$residuals)
plot(cusumncsh)

########################################## COINTEGRATION ############################################
#perform a bound test to see if there is cointegration (short-model)
# if F > I(1) -> cointegration, if F < I(0) -> no cointegration
#if I(0) < F < I(1) test is not specified 
ardlncsh
#double check the results of the bound test
bounds_f_test(ardlncsh, alpha = 0.05, case = 2)
# double check with the results of the t test
bounds_t_test(ardlncsh, alpha = 0.05, case = 3)
#no cointegration

######################################## MODELS COMPARISON #######################################
#plot the different fitted values in the same chart
plot.ts(fv_dtd,type="l",col="pink", main ="fit_var_vs_act_var", 
        xlab = "Years", ylab = "log", axes = TRUE)
lines(logap_purets,col="green")
lines(fv_nt, col = "red")
lines(fv_dt, col = "blue")
#save it
pdf("img/fit_vs_act.pdf")
plot.ts(fv_dtd,type="l",col="pink", main ="fit_var_vs_act_var", 
        xlab = "Years", ylab = "log", axes = TRUE)
lines(logap_purets,col="green")
lines(fv_nt, col = "red")
lines(fv_dt, col = "blue")
dev.off()
############# include all the model
plot.ts(fv_dtd,type="l",col="pink", main ="fit_var_vs_act_var", 
        xlab = "Years", ylab = "log", axes = TRUE)
lines(logap_purets,col="green")
lines(fv_nt, col = "red")
lines(fv_dt, col = "blue")
lines(fv_ng, col = "orange")
lines(fv_ngsh, col = "black")
lines(fv_nc,col="deeppink") 
lines(fv_ncsh, col = "chocolate4")
#save it
pdf("img/fit_vs_act.pdf")
plot.ts(fv_dtd,type="l",col="pink", main ="fit_var_vs_act_var", 
        xlab = "Years", ylab = "log", axes = TRUE)
lines(logap_purets,col="green")
lines(fv_nt, col = "red")
lines(fv_dt, col = "blue")
lines(fv_ng, col = "orange")
lines(fv_ngsh, col = "black")
lines(fv_nc,col="deeppink") 
lines(fv_ncsh, col = "chocolate4")
dev.off()
# just loggen and logcomp model
plot.ts(fv_ngsh,type="l",col="black", main ="fit_var_vs_act_var", 
        xlab = "Years", ylab = "log", axes = TRUE)
lines(logap_purets,col="green")
lines(fv_ncsh, col = "chocolate4")
#save it
pdf("img/fit_vs_act_compgen.pdf")
plot.ts(fv_ngsh,type="l",col="black", main ="fit_var_vs_act_var", 
        xlab = "Years", ylab = "log", axes = TRUE)
lines(logap_purets,col="green")
lines(fv_ncsh, col = "chocolate4")
dev.off()
#include all the models in the same table
#nt
ardlnt_sum <- summary(ardlnt)
se_nt <- (ardlnt_sum$coefficients[,2])
#dt
ardldt_sum <- summary(ardldt)
se_nt <- (ardldt_sum$coefficients[,2])
#dtd
ardldtd_sum <- summary(ardldtd)
se <- nt <- (ardldtd$coefficient[,2])
####### unify all together




################################ DETRENDED LOGAP ################################################## 
#this command estimated the ARDL, the related ECM, the right lag length and the cointegration test
detlogap <- detrend(logap_purets)
ardlAICng <- ardlBound(data = log_pure, logap_purets ~ logas_purets + logoff_purets + 
                         detlogcomp_ts, case = 3, p = NULL,
                       remove = NULL, autoOrder = FALSE, ic = "BIC" , max.p = 4, max.q = 3, 
                       ECM = TRUE, stability = TRUE)
#BIC selection: 4,4,3,4
ardlAICng <- ardlBound(data = log_pure, logap_purets ~ logas_purets + logoff_purets + 
                         + detlogcomp_ts, case = 3, p = NULL,
                       remove = NULL, autoOrder = FALSE, ic = "AIC" , max.p = 4, max.q = 3, 
                       ECM = TRUE, stability = TRUE)
#AIC selection: 4,4,3,4
########################################### ARDL ###################################################
ardlng <- ardl(logap_purets ~ logas_purets + logoff_purets  
               + detlogcomp_ts + dummyts, data = log_pure, order = c(4,4,3,4,0))
summary(ardlng)
#fitted values
fv_ng <- fitted.values(ardlng)
fv_ng <- ts(fv_ng, start = c(2014, 2), end = c(2020,1), frequency = 4)
#plot the model estimation and the real values
plot.ts(fv_ng,type="l",col="orange", main ="Offsets in general account growth rate", 
        xlab = "Years", ylab = "Growth precentage", axes = TRUE)
lines(logap_purets,col="green")
#lines(fv_sh, col = "blue")

###### residual analysis (long lag model)
#save the residual
resng <- ardlng$residuals
resng2 <- resng^2
#show them
summary(resng)
# look for residuals autocorrelation
acf(ardlng$residuals, type = "correlation")
#save it
pdf("img/res_corr.pdf")
acf(ardlng$residuals, type = "correlation")
dev.off()
# test for it with Durban Watson Test
dwtest(ardlng)
# no correlation among residuals

########################################## COINTEGRATION ############################################
#perform a bound test to see if there is cointegration (short-model)
# if F > I(1) -> cointegration, if F < I(0) -> no cointegration
#if I(0) < F < I(1) test is not specified 
ardlng
#double check the results of the bound test
bounds_f_test(ardlng, alpha = 0.05, case = 2)
# double check with the results of the t test
bounds_t_test(ardlng, alpha = 0.05, case = 3)


#############################################################################################################################
#######################################  THE END  ########################################################
###################################################################################