rm(list=ls())
library(mvtnorm)
library(boot)
library(pracma)
library(Matrix)
library(glmnet)
tmp = proc.time()


###setting
p <- 200
s <- ceiling(sqrt(p))
n <- 100
M <- 50
N <- n * M
B_type <- 1
epsi_type <- "n"
###n, t, chi, exp, heter
b <- 5

tau <- 50

R <- 100


# sigma <- matrix(0, p-1, p-1)
# for(i in 1:(p-1)){
#   for(j in 1:(p-1)){
#     sigma[i, j] <- 0.5^(abs(i - j))
#   }
# }

set.seed(1810128)
theta_0 <- c(rnorm(s), rep(0, p-s))

for(m in 1:M){
  if(m == 1){
    theta_star <- theta_0
  }
  else{
    theta_star <- c(theta_star, theta_0)
  }
}


###generate Byzantine
set.seed(1810128)
b_order <- sample(c(1:M), b)

A <- W <- matrix(0, M, M)
###generate edges
q <- 0.5
set.seed(1810128)
index <- rbinom(M*(M-1)/2, 1, q)
#compute matrix
t <- 1
for(i in 1:(M-1)){
  for(j in (i+1):M){
    A[i, j] <- A[j, i] <- index[t]
    t <- t + 1
  }
}
diag(A) <- rep(1, M)
###functions#####################################################################
#local degree weights (1/max(d_i,d_j))
rs <- rowSums(A)
for(i in 1:(M-1)){
  for(j in (i+1):M){
    if(A[i, j] != 0){
      W[i, j] <- W[j, i] <- 1 / max(c(rs[i], rs[j]))
    }
  }
}
for(i in 1:M){
  W[i, i] <- 1 - sum(W[i, ])
}


###operator
S <- function(lambda, beta){
  l <- length(beta)
  res <- rep(0, l)
  for(i in 1:l){
    if(beta[i] > lambda){
      res[i] <- beta[i] - lambda
    }
    if(beta[i] < -lambda){
      res[i] <- beta[i] + lambda
    }
  }
  return(res)
}


###screen function

###weighted average
screen <- function(vec, i, W){
  res <- rep(0, p)
  for(m in 1:M){
    res <- res + W[i, m] * vec[((m-1)*p+1):(m*p)]
  }
  return(res)
}

###Byzantine
trim <- function(mat, b){
  l1 <- nrow(mat)
  l2 <- ncol(mat)
  res <- rep(0, l1)
  if(b == 0){
    res <- apply(mat, 1, mean)
  }
  else{
    mat1 <- matrix(0, l1, l2-2*b)
    byzantine <- c(1:b, (l2-b+1):l2)
    for(i in 1:l1){
      v <- order(mat[i, ])
      mat1[i, ] <- mat[i, v[-byzantine]]
    }
    res <- apply(mat1, 1, mean)
  }
  return(res)
}
# trun <- function(mat, b){
#   l1 <- nrow(mat)
#   l2 <- ncol(mat)
#   res <- rep(0, l1)
#   mat1 <- matrix(0, l1, l2)
#   byzantine <- c(1:b, (l2-b+1):l2)
#   for(i in 1:l1){
#     a <- mat[i, ]
#     v <- order(a)
#     a[rank(a) <= b] <- a[order(a)[b+1]]
#     a[rank(a) >= l2-b+1] <- a[order(a)[l2-b]]
#     mat1[i, ] <- a
#   }
#   res <- apply(mat1, 1, mean)
#   return(res)
# }
Krum <- function(vec, b){
  D <- length(vec)
  
  res <- rep(0, D)
  #distance
  Dist <- matrix(0, D, D)
  for(j in 1:D){
    for(k in j:D){
      Dist[j, k] <- Dist[k, j] <- sum((vec[j]-vec[k])^2)
    }
  }
  
  #score
  score <- rep(0, D)
  for(m in 1:D){
    temp <- Dist[m, ]
    
    Dist_temp <- sort(temp)[1:(D-b-1)]
    score[m] <- sum(Dist_temp)
  }
  
  #argmin score
  tar <- which.min(score)
  
  res <- vec[tar]
  return(res)
}

screen_b <- function(vec, i, A, type, b){
  res <- rep(0, p)
  com <- NULL
  vec_com <- NULL
  for(m in 1:M){
    if(A[i, m] == 1){
      com <- cbind(com, vec[((m-1)*p+1):(m*p)])
      vec_com <- c(vec_com, vec[((m-1)*p+1):(m*p)])
    }
  }
  if(type == "Median"){
    res <- apply(com, 1, median)
  }
  if(type == "Trim"){
    res <- trim(com, b)
  }
  if(type == "Krum"){
    for(d in 1:p){
      res[d] <- Krum(com[d, ], b)
    }
  }
  
  return(res)
}


###find mean and sd
expectation <- function(vec, b_order){
  res <- rep(0, p)
  vec_m <- NULL
  for(m in 1:M){
    vec_m <- cbind(vec_m, vec[((m-1)*p+1):(m*p)])
  }
  vec_m <- vec_m[, -b_order]
  res <- apply(vec_m, 1, mean)
  return(res)
}
stan_d <- function(vec, b_order){
  res <- rep(0, p)
  vec_m <- NULL
  for(m in 1:M){
    vec_m <- cbind(vec_m, vec[((m-1)*p+1):(m*p)])
  }
  vec_m <- vec_m[, -b_order]
  res <- apply(vec_m, 1, sd)
  return(res)
}

###o_max
o_max <- function(vec, b_order){
  res <- rep(0, p)
  vec_m <- NULL
  for(m in 1:M){
    vec_m <- cbind(vec_m, vec[((m-1)*p+1):(m*p)])
  }
  vec_m <- vec_m[, -b_order]
  res <- -apply(vec_m, 1, max)
  return(res)
}


###Byzantine attack function
Byzantine <- function(vec, b_order, type){
  res <- vec
  ALIE <-  expectation(vec, b_order) + 1.75*stan_d(vec, b_order)
  for(i in 1:length(b_order)){
    B <- b_order[i]
    if(type == 1){
      res[((B-1)*p+1):(B*p)] <- vec[((B-1)*p+1):(B*p)] + 
        rnorm(p, 0, sqrt(10))
    }
    if(type == 2){
      res[((B-1)*p+1):(B*p)] <- - vec[((B-1)*p+1):(B*p)]
    }
    if(type == 3){
      res[((B-1)*p+1):(B*p)] <- rnorm(p)
    }
    if(type == 4){
      res[((B-1)*p+1):(B*p)] <- -0.1*expectation(vec, b_order)
    }
    if(type == 5){
      res[((B-1)*p+1):(B*p)] <- o_max(vec, b_order)
    }
    if(type == 6){
      res[((B-1)*p+1):(B*p)] <- ALIE
    }
  }
  return(res)
}


###get lambda
get_parameter <- function(Lambda, Gamma){
  loss <- matrix(0, length(Lambda), length(Gamma))
  
  ###generate data
  X_1 <- rmvnorm(N, rep(0, p-1))
  X <- cbind(1, X_1)
  epsilon <- switch(epsi_type,
                    n = rnorm(N, 0, 1),
                    t = rt(N, 3),
                    chi = rchisq(N, 1) - 1,
                    exp = rexp(N, 1) - 1,
                    heter = (0.5 + 0.5*abs(X_1[ ,1])) * rnorm(N, 0, 1))
  Y <- X %*% theta_0 + epsilon
  
  
  for(l1 in 1:length(Lambda)){
    # cat(l1)
    # cat("\n")
    
    lambda <- Lambda[l1]
    
    for(l2 in 1:length(Gamma)){
      # cat(l2)
      # cat("\n")
      
      gamma <- Gamma[l2]
      
      theta_t <- theta_t1 <- rep(0, M*p)
      grad_t <- grad_t1 <- grad_t2 <- rep(0, M*p)
      
      
      ###initial gradients
      for(i in 1:M){
        grad_t[((i-1)*p+1):(i*p)] <- 2/n*(t(X[((i-1)*n+1):(i*n), ])%*%X[((i-1)*n+1):(i*n), ]%*%theta_t[((i-1)*p+1):(i*p)] - 
                                            t(X[((i-1)*n+1):(i*n), ])%*%Y[((i-1)*n+1):(i*n)])
      }
      for(t in 1:tau){
        # cat(t)
        for(j in 1:M){
          grad_t2[((j-1)*p+1):(j*p)] <- 2/n*t(X[((j-1)*n+1):(j*n), ])%*%X[((j-1)*n+1):(j*n), ]%*%theta_t[((j-1)*p+1):(j*p)]
        }
        for(i in 1:M){
          theta_t1_tran <- Byzantine(theta_t1, b_order, B_type)
          theta_t[((i-1)*p+1):(i*p)] <- screen_b(theta_t1_tran, i, A, "Median", b)
        }
        if(t == tau){
          loss[l1, l2] <- sum((theta_t - theta_star)^2) / M
        }
        for(j in 1:M){
          grad_t1[((j-1)*p+1):(j*p)] <- grad_t[((j-1)*p+1):(j*p)] + 
            2/n*t(X[((j-1)*n+1):(j*n), ])%*%X[((j-1)*n+1):(j*n), ]%*%theta_t[((j-1)*p+1):(j*p)] - 
            grad_t2[((j-1)*p+1):(j*p)]
        }
        for(i in 1:M){
          grad_t1_tran <- Byzantine(grad_t1, b_order, B_type)
          grad_t[((i-1)*p+1):(i*p)] <- screen_b(grad_t1_tran, i, A, "Median", b)
        }
        theta_t1 <- S(lambda, theta_t - grad_t / gamma)
      }
      # for(m in 1:M){
      #   loss[l1, l2] <- loss[l1, l2] + mean((Y[((m-1)*n+1):(m*n)] - X[((m-1)*n+1):(m*n), ]%*%theta_t1[((m-1)*p+1):(m*p)])^2)
      # }
      
      
      cat("\n")
    }
  }
  
  print(loss)
  para1 <- which(loss==min(loss), arr.ind=TRUE)[1]
  para2 <- which(loss==min(loss), arr.ind=TRUE)[2]
  res <- c(Lambda[para1], Gamma[para2])
  return(res)
}


#Lambda <- 0.01
#Gamma <- 5
Lambda <- c(0.01/16, 0.01/8, 0.01/4, 0.01/2, 0.01, 0.03, 0.05)
Gamma <- c(3, 5, 7, 9, 11)
para <- matrix(0, 2, 5)
for(r in 1:5){
  cat(r)
  
  parameter <- get_parameter(Lambda, Gamma)
  para[1, r] <- parameter[1]
  para[2, r] <- parameter[2]
}
cat("\n")
lambda <- mean(para[1, ])
gamma  <- mean(para[2, ])
print(para)
print(lambda)
print(gamma)


###simulation##############################################################################
###simulation


theta_t <- theta_t1 <- matrix(0, M*p, R)
theta_t_M <- theta_t1_M <- matrix(0, M*p, R)
theta_t_T <- theta_t1_T <- matrix(0, M*p, R)
theta_t_K <- theta_t1_K <- matrix(0, M*p, R)

grad_t <- grad_t1 <- grad_t2 <- matrix(0, M*p, R)
grad_t_M <- grad_t1_M <- grad_t2_M <- matrix(0, M*p, R)
grad_t_T <- grad_t1_T <- grad_t2_T <- matrix(0, M*p, R)
grad_t_K <- grad_t1_K <- grad_t2_K <- matrix(0, M*p, R)

theta_glo <- matrix(0, p, R)
MSE <- MSE_M <- MSE_T <- MSE_K <- matrix(0, tau, R)
MSE_glo <- rep(0, R)


for(r in 1:R){
  
  cat(r)
  cat("\n")
  
  ###generate data
  set.seed(r)
  X_1 <- rmvnorm(N, rep(0, p-1))
  X <- cbind(1, X_1)
  epsilon <- switch(epsi_type,
                    n = rnorm(N, 0, 1),
                    t = rt(N, 3),
                    chi = rchisq(N, 1) - 1,
                    exp = rexp(N, 1) - 1,
                    heter = (0.5 + 0.5*abs(X_1[ ,1])) * rnorm(N, 0, 1))
  
  Y <- X %*% theta_0 + epsilon
  
  
  ###global (centralized) estimator
  global_cv_fit <- cv.glmnet(X_1, Y, family = "gaussian")
  global_fit <- glmnet(X_1, Y, family = "gaussian", 
                       lambda = global_cv_fit$lambda.min)
  theta_glo[, r] <- as.vector(coef(global_fit))
  MSE_glo[r] <- sum((theta_glo[, r] - theta_0)^2)
  
  
  ###initial gradients
  for(i in 1:M){
    grad_t[((i-1)*p+1):(i*p), r] <- 2/n*(t(X[((i-1)*n+1):(i*n), ])%*%X[((i-1)*n+1):(i*n), ]%*%theta_t[((i-1)*p+1):(i*p), r] - 
                                           t(X[((i-1)*n+1):(i*n), ])%*%Y[((i-1)*n+1):(i*n)])
    
    ###propose
    grad_t_M[((i-1)*p+1):(i*p), r] <- 2/n*(t(X[((i-1)*n+1):(i*n), ])%*%X[((i-1)*n+1):(i*n), ]%*%theta_t_M[((i-1)*p+1):(i*p), r] - 
                                             t(X[((i-1)*n+1):(i*n), ])%*%Y[((i-1)*n+1):(i*n)])
    
    grad_t_T[((i-1)*p+1):(i*p), r] <- 2/n*(t(X[((i-1)*n+1):(i*n), ])%*%X[((i-1)*n+1):(i*n), ]%*%theta_t_T[((i-1)*p+1):(i*p), r] - 
                                             t(X[((i-1)*n+1):(i*n), ])%*%Y[((i-1)*n+1):(i*n)])
    
    grad_t_K[((i-1)*p+1):(i*p), r] <- 2/n*(t(X[((i-1)*n+1):(i*n), ])%*%X[((i-1)*n+1):(i*n), ]%*%theta_t_K[((i-1)*p+1):(i*p), r] - 
                                             t(X[((i-1)*n+1):(i*n), ])%*%Y[((i-1)*n+1):(i*n)])
    
  }
  
  for(t in 1:tau){
    cat(t)
    for(j in 1:M){
      grad_t2[((j-1)*p+1):(j*p), r] <- 2/n*t(X[((j-1)*n+1):(j*n), ])%*%
        X[((j-1)*n+1):(j*n), ]%*%theta_t[((j-1)*p+1):(j*p), r]
      
      ###propose
      grad_t2_M[((j-1)*p+1):(j*p), r] <- 2/n*t(X[((j-1)*n+1):(j*n), ])%*%
        X[((j-1)*n+1):(j*n), ]%*%theta_t_M[((j-1)*p+1):(j*p), r]
      
      grad_t2_T[((j-1)*p+1):(j*p), r] <- 2/n*t(X[((j-1)*n+1):(j*n), ])%*%
        X[((j-1)*n+1):(j*n), ]%*%theta_t_T[((j-1)*p+1):(j*p), r]
      
      grad_t2_K[((j-1)*p+1):(j*p), r] <- 2/n*t(X[((j-1)*n+1):(j*n), ])%*%
        X[((j-1)*n+1):(j*n), ]%*%theta_t_K[((j-1)*p+1):(j*p), r]
      
    }
    for(i in 1:M){
      theta_t1_tran <- Byzantine(theta_t1[, r], b_order, B_type)
      theta_t[((i-1)*p+1):(i*p), r] <- screen(theta_t1_tran, i, W)
      
      ###propose
      theta_t1_M_tran <- Byzantine(theta_t1_M[, r], b_order, B_type)
      theta_t_M[((i-1)*p+1):(i*p), r] <- screen_b(theta_t1_M_tran, i, A, "Median", b)
      
      theta_t1_T_tran <- Byzantine(theta_t1_T[, r], b_order, B_type)
      theta_t_T[((i-1)*p+1):(i*p), r] <- screen_b(theta_t1_T_tran, i, A, "Trim", b)
      
      theta_t1_K_tran <- Byzantine(theta_t1_K[, r], b_order, B_type)
      theta_t_K[((i-1)*p+1):(i*p), r] <- screen_b(theta_t1_K_tran, i, A, "Krum", b)
      
    }
    
    ###MSE
    MSE[t, r] <- sum((theta_t[, r] - theta_star)^2) / M
    MSE_M[t, r] <- sum((theta_t_M[, r] - theta_star)^2) / M
    MSE_T[t, r] <- sum((theta_t_T[, r] - theta_star)^2) / M
    MSE_K[t, r] <- sum((theta_t_K[, r] - theta_star)^2) / M
    
    for(j in 1:M){
      grad_t1[((j-1)*p+1):(j*p), r] <- grad_t[((j-1)*p+1):(j*p), r] + 
        2/n*t(X[((j-1)*n+1):(j*n), ])%*%X[((j-1)*n+1):(j*n), ]%*%theta_t[((j-1)*p+1):(j*p), r] - 
        grad_t2[((j-1)*p+1):(j*p), r]
      
      ###propose
      grad_t1_M[((j-1)*p+1):(j*p), r] <- grad_t_M[((j-1)*p+1):(j*p), r] + 
        2/n*t(X[((j-1)*n+1):(j*n), ])%*%X[((j-1)*n+1):(j*n), ]%*%theta_t_M[((j-1)*p+1):(j*p), r] - 
        grad_t2_M[((j-1)*p+1):(j*p), r]
      
      grad_t1_T[((j-1)*p+1):(j*p), r] <- grad_t_T[((j-1)*p+1):(j*p), r] + 
        2/n*t(X[((j-1)*n+1):(j*n), ])%*%X[((j-1)*n+1):(j*n), ]%*%theta_t_T[((j-1)*p+1):(j*p), r] - 
        grad_t2_T[((j-1)*p+1):(j*p), r]
      
      grad_t1_K[((j-1)*p+1):(j*p), r] <- grad_t_K[((j-1)*p+1):(j*p), r] + 
        2/n*t(X[((j-1)*n+1):(j*n), ])%*%X[((j-1)*n+1):(j*n), ]%*%theta_t_K[((j-1)*p+1):(j*p), r] - 
        grad_t2_K[((j-1)*p+1):(j*p), r]
      
    }
    for(i in 1:M){
      grad_t1_tran <- Byzantine(grad_t1[, r], b_order, B_type)
      grad_t[((i-1)*p+1):(i*p), r] <- screen(grad_t1_tran, i, W)
      
      ###propose
      grad_t1_M_tran <- Byzantine(grad_t1_M[, r], b_order, B_type)
      grad_t_M[((i-1)*p+1):(i*p), r] <- screen_b(grad_t1_M_tran, i, A, "Median", b)
      
      grad_t1_T_tran <- Byzantine(grad_t1_T[, r], b_order, B_type)
      grad_t_T[((i-1)*p+1):(i*p), r] <- screen_b(grad_t1_T_tran, i, A, "Trim", b)
      
      grad_t1_K_tran <- Byzantine(grad_t1_K[, r], b_order, B_type)
      grad_t_K[((i-1)*p+1):(i*p), r] <- screen_b(grad_t1_K_tran, i, A, "Krum", b)
      
    }
    theta_t1[, r] <- S(lambda, theta_t[, r] - grad_t[, r] / gamma)
    theta_t1_M[, r] <- S(lambda, theta_t_M[, r] - grad_t_M[, r] / gamma)
    theta_t1_T[, r] <- S(lambda, theta_t_T[, r] - grad_t_T[, r] / gamma)
    theta_t1_K[, r] <- S(lambda, theta_t_K[, r] - grad_t_K[, r] / gamma)
    
  }
  
  cat("\n")
}





res1 <- cbind(mean(log(MSE_glo)), apply(log(MSE), 1, mean),
              apply(log(MSE_M), 1, mean), apply(log(MSE_T), 1, mean),
              apply(log(MSE_K), 1, mean))

res2 <- rbind(log(MSE_glo), log(MSE), 
              log(MSE_M), log(MSE_T), 
              log(MSE_K))

print(res1)

running.time = proc.time() - tmp
print(running.time)

