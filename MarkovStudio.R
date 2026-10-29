#MARKOV STUDIO  -  Analyse des chaines de Markov  (R base + tcltk, portable)
#Lancement :  Rscript MarkovStudio.R   (ou  source("MarkovStudio.R"))

if (!capabilities("tcltk") && !requireNamespace("tcltk", quietly = TRUE))
  stop("tcltk indisponible : reinstaller R avec le support Tcl/Tk.")
suppressWarnings(suppressMessages(library(tcltk)))

#1. MOTEUR MATHEMATIQUE  (R base, sparse-aware, scalable n grand)
#   Strategie : tout passe par une representation creuse (triplets + CSR par ligne),
#   les passes sont en O(V + E) et evitent toute multiplication sur des zeros.

`%||%` <- function(a, b) if (is.null(a)) b else a
.gcd <- function(a, b) { a <- abs(a); b <- abs(b); while (b) { t <- b; b <- a %% b; a <- t }; a }

# --- Representation creuse : triplets (iv, jv, vv) + acces par ligne ----------
# Pourquoi : pour une matrice de transition n x n a |E| arcs, on passe d'un
# stockage O(n^2) a O(n + |E|) et toutes les operations evitent les zeros.
build_sparse <- function(P, eps = 1e-12) {
  # === Mode SPARSE-PUR : entree est deja un objet de triplets, on saute tout ===
  if (inherits(P, "markov_sparse_input")) {
    n <- P$n
    iv <- as.integer(P$iv); jv <- as.integer(P$jv); vv <- as.numeric(P$vv)
    keep <- vv > eps
    iv <- iv[keep]; jv <- jv[keep]; vv <- vv[keep]
    ord <- order(iv, jv); iv <- iv[ord]; jv <- jv[ord]; vv <- vv[ord]
    ptr_o <- c(0L, cumsum(tabulate(iv, n)))
    empty_i <- integer(0); empty_n <- numeric(0)
    adj_out <- rep(list(empty_i), n); wt_out <- rep(list(empty_n), n)
    for (i in which(diff(ptr_o) > 0L)) { sl <- (ptr_o[i] + 1L):ptr_o[i + 1L]; adj_out[[i]] <- jv[sl]; wt_out[[i]] <- vv[sl] }
    ord2 <- order(jv, iv); jv2 <- jv[ord2]; iv2 <- iv[ord2]
    ptr_i <- c(0L, cumsum(tabulate(jv2, n)))
    adj_in <- rep(list(empty_i), n)
    for (j in which(diff(ptr_i) > 0L)) { sl <- (ptr_i[j] + 1L):ptr_i[j + 1L]; adj_in[[j]] <- iv2[sl] }
    return(list(n = n, iv = iv, jv = jv, vv = vv,
                adj_out = adj_out, wt_out = wt_out, adj_in = adj_in,
                nnz = length(iv), density = length(iv) / (as.numeric(n) * n)))
  }
  n <- nrow(P)
  # Raccourci : si parse_matrix a deja les triplets en attribut, on saute
  # le scan O(n^2) de which(P > eps) -- crucial pour n > 5000.
  tri <- attr(P, "sparse_triplets")
  if (!is.null(tri)) {
    iv <- as.integer(tri$iv); jv <- as.integer(tri$jv); vv <- as.numeric(tri$vv)
    keep <- vv > eps
    iv <- iv[keep]; jv <- jv[keep]; vv <- vv[keep]
    ord <- order(iv, jv); iv <- iv[ord]; jv <- jv[ord]; vv <- vv[ord]
    ptr_o <- c(0L, cumsum(tabulate(iv, n)))
    empty_i <- integer(0); empty_n <- numeric(0)
    adj_out <- rep(list(empty_i), n); wt_out <- rep(list(empty_n), n)
    for (i in which(diff(ptr_o) > 0L)) { sl <- (ptr_o[i] + 1L):ptr_o[i + 1L]; adj_out[[i]] <- jv[sl]; wt_out[[i]] <- vv[sl] }
    ord2 <- order(jv, iv); jv2 <- jv[ord2]; iv2 <- iv[ord2]
    ptr_i <- c(0L, cumsum(tabulate(jv2, n)))
    adj_in <- rep(list(empty_i), n)
    for (j in which(diff(ptr_i) > 0L)) { sl <- (ptr_i[j] + 1L):ptr_i[j + 1L]; adj_in[[j]] <- iv2[sl] }
    return(list(n = n, iv = iv, jv = jv, vv = vv,
                adj_out = adj_out, wt_out = wt_out, adj_in = adj_in,
                nnz = length(iv), density = length(iv) / (as.numeric(n) * n)))
  }
  nz_total <- sum(P > eps)
  density <- nz_total / (as.numeric(n) * n)
  # === chemin DENSE (densite eleve) ============================================
  # split() sur des millions d'elements est lent. On construit les vecteurs en
  # ordre ligne-major directement, et adj_out/in via lapply + which (~3x plus
  # rapide que which(P>eps, arr.ind) + order + split pour grand n dense).
  if (density > 0.5 && n >= 200L) {
    nz_per_row <- rowSums(P > eps)
    full <- nz_total == as.numeric(n) * n
    if (full) {
      adj_seq <- seq_len(n)
      adj_out <- rep(list(adj_seq), n)        # partage par reference, gratuit
      adj_in  <- adj_out
      wt_out  <- lapply(seq_len(n), function(i) P[i, ])
      iv <- rep.int(seq_len(n), rep.int(n, n))
      jv <- rep.int(adj_seq, n)
      vv <- as.numeric(t(P))
    } else {
      adj_out <- vector("list", n); wt_out <- vector("list", n); adj_in <- vector("list", n)
      iv <- integer(nz_total); jv <- integer(nz_total); vv <- numeric(nz_total)
      pos <- 1L
      for (i in seq_len(n)) {
        js <- which(P[i, ] > eps); k <- length(js)
        adj_out[[i]] <- js; wt_out[[i]] <- P[i, js]
        if (k > 0L) { sl <- pos:(pos + k - 1L); iv[sl] <- i; jv[sl] <- js; vv[sl] <- P[i, js]; pos <- pos + k }
      }
      for (j in seq_len(n)) adj_in[[j]] <- which(P[, j] > eps)
    }
    return(list(n = n, iv = iv, jv = jv, vv = vv,
                adj_out = adj_out, wt_out = wt_out, adj_in = adj_in,
                nnz = length(iv), density = density))
  }
  # === chemin CREUX (densite faible) ===========================================
  # Eviter split(factor(...)) avec beaucoup de niveaux vides : pointeur cumulatif.
  nzm <- which(P > eps, arr.ind = TRUE)
  iv <- as.integer(nzm[, 1L]); jv <- as.integer(nzm[, 2L]); vv <- P[nzm]
  ord <- order(iv, jv); iv <- iv[ord]; jv <- jv[ord]; vv <- vv[ord]
  ptr_o <- c(0L, cumsum(tabulate(iv, n)))
  empty_i <- integer(0); empty_n <- numeric(0)
  adj_out <- rep(list(empty_i), n); wt_out <- rep(list(empty_n), n)
  nz_rows <- which(diff(ptr_o) > 0L)
  for (i in nz_rows) { sl <- (ptr_o[i] + 1L):ptr_o[i + 1L]; adj_out[[i]] <- jv[sl]; wt_out[[i]] <- vv[sl] }
  # adj_in via tri par jv
  ord2 <- order(jv, iv); jv2 <- jv[ord2]; iv2 <- iv[ord2]
  ptr_i <- c(0L, cumsum(tabulate(jv2, n)))
  adj_in <- rep(list(empty_i), n)
  nz_cols <- which(diff(ptr_i) > 0L)
  for (j in nz_cols) { sl <- (ptr_i[j] + 1L):ptr_i[j + 1L]; adj_in[[j]] <- iv2[sl] }
  list(n = n, iv = iv, jv = jv, vv = vv,
       adj_out = adj_out, wt_out = wt_out, adj_in = adj_in,
       nnz = length(iv), density = density)
}

# Test rapide "graphe fortement connexe" : BFS aller depuis 1, puis BFS arriere.
# Pour les matrices denses (la plupart des cas reels), evite Tarjan complet.
.is_one_scc <- function(sp) {
  n <- sp$n
  bfs <- function(adj) {
    vis <- logical(n); vis[1L] <- TRUE
    q <- integer(n); q[1L] <- 1L; head <- 1L; tail <- 1L
    while (head <= tail) {
      u <- q[head]; head <- head + 1L
      for (v in adj[[u]]) if (!vis[v]) { vis[v] <- TRUE; tail <- tail + 1L; q[tail] <- v }
    }
    all(vis)
  }
  bfs(sp$adj_out) && bfs(sp$adj_in)
}

# --- Multiplication ligne x matrice creuse (v %*% P) --------------------------
# Vectorisee par rowsum : O(|E|), aucun calcul sur les zeros.
sparse_vTP <- function(v, sp) {
  if (!length(sp$iv)) return(numeric(sp$n))
  contrib <- v[sp$iv] * sp$vv
  agg <- rowsum(contrib, sp$jv, reorder = FALSE)
  out <- numeric(sp$n)
  out[as.integer(rownames(agg))] <- agg[, 1L]
  out
}

# --- Tarjan iteratif : SCC en O(V + E) ----------------------------------------
# Pourquoi : remplace l'ancienne fermeture transitive en O(n^3) memoire & temps.
# Implementation iterative (pile manuelle) pour ne pas saturer la pile R.
tarjan_scc <- function(adj_out, n) {
  idx   <- rep(NA_integer_, n); low <- rep(NA_integer_, n); onstk <- logical(n)
  stk   <- integer(n);          stk_top <- 0L
  cs_v  <- integer(n + 1L);     cs_p <- integer(n + 1L); cs_top <- 0L
  sccs  <- list(); index <- 0L
  for (s in seq_len(n)) {
    if (!is.na(idx[s])) next
    fv <- s; fp <- 1L
    idx[fv] <- index; low[fv] <- index; index <- index + 1L
    stk_top <- stk_top + 1L; stk[stk_top] <- fv; onstk[fv] <- TRUE
    repeat {
      succ <- adj_out[[fv]]; ls <- length(succ); descended <- FALSE
      while (fp <= ls) {
        w <- succ[fp]
        if (is.na(idx[w])) {
          cs_top <- cs_top + 1L; cs_v[cs_top] <- fv; cs_p[cs_top] <- fp + 1L
          fv <- w; fp <- 1L
          idx[fv] <- index; low[fv] <- index; index <- index + 1L
          stk_top <- stk_top + 1L; stk[stk_top] <- fv; onstk[fv] <- TRUE
          descended <- TRUE; break
        }
        if (onstk[w] && idx[w] < low[fv]) low[fv] <- idx[w]
        fp <- fp + 1L
      }
      if (descended) next
      if (low[fv] == idx[fv]) {
        comp <- integer(0L)
        repeat {
          w <- stk[stk_top]; stk_top <- stk_top - 1L; onstk[w] <- FALSE
          comp <- c(comp, w)
          if (w == fv) break
        }
        sccs[[length(sccs) + 1L]] <- sort(comp)
      }
      if (cs_top == 0L) break
      child_low <- low[fv]
      fv <- cs_v[cs_top]; fp <- cs_p[cs_top]; cs_top <- cs_top - 1L
      if (child_low < low[fv]) low[fv] <- child_low
    }
  }
  # ordre canonique : par plus petit indice de la classe
  sccs[order(vapply(sccs, `[`, integer(1L), 1L))]
}

# --- Nature d'une classe (Absorbant/Recurrente/Transitoire) en O(|E(C)|) ------
class_nature_sparse <- function(sp, C) {
  inC <- logical(sp$n); inC[C] <- TRUE
  for (i in C) {
    js <- sp$adj_out[[i]]
    if (length(js) && !all(inC[js])) return("Transitoire")
  }
  if (length(C) == 1L) {
    js <- sp$adj_out[[C]]; ws <- sp$wt_out[[C]]
    if (length(js) == 1L && js[1L] == C && isTRUE(all.equal(ws[1L], 1))) return("Absorbant")
  }
  "Recurrente"
}

# --- Periode d'une classe via BFS creux : gcd des longueurs de cycles ---------
# Court-circuit : un self-loop dans C => periode 1 (gcd(1,*) = 1). Vectorise via
# les triplets iv/jv -> evite le BFS sur de grands SCC fortement connectes.
period_class_sparse <- function(sp, C) {
  m <- length(C); pos <- integer(sp$n); pos[C] <- seq_len(m)
  # detection self-loop dans C : test O(|E|) entierement vectorise
  if (length(sp$iv)) {
    loops <- sp$iv == sp$jv
    if (any(loops & pos[sp$iv] > 0L)) return(1L)
  }
  level <- rep(-1L, m); level[1L] <- 0L
  queue <- integer(m); queue[1L] <- 1L; head <- 1L; tail <- 1L
  g <- 0L
  while (head <= tail) {
    u <- queue[head]; head <- head + 1L; gu <- C[u]
    for (vg in sp$adj_out[[gu]]) {
      v <- pos[vg]; if (v == 0L) next
      if (level[v] == -1L) {
        level[v] <- level[u] + 1L
        tail <- tail + 1L; queue[tail] <- v
      } else {
        g <- .gcd(g, abs(level[u] + 1L - level[v]))
        if (g == 1L) return(1L)   # plus de progres possible
      }
    }
  }
  g
}

# --- Stationnaire par power iteration sur la chaine paresseuse ----------------
# pi <- 0.5 * pi + 0.5 * (pi P)  partage la meme stationnaire que P et reste
# aperiodique : gere donc proprement les classes recurrentes periodiques (ex.
# chaines bipartites). Cout par iteration : O(|E(C)|), pas de solve / qr.solve.
# Branche dense (BLAS) si la classe est dense : 100x plus rapide que la boucle R.
stationary_power <- function(sp, C, tol = 1e-12, maxiter = 10000L, P_full = NULL) {
  m <- length(C)
  if (m == 1L) return(1)            # singleton (absorbant) : stationnaire triviale
  inC <- logical(sp$n); inC[C] <- TRUE
  # Densite du sous-bloc via triplets (O(|E|))
  in_sub <- inC[sp$iv] & inC[sp$jv]
  sub_nnz <- sum(in_sub)
  sub_density <- sub_nnz / (as.numeric(m) * m)
  # === Chemin DENSE : BLAS via P_full[C,C] =====================================
  if (!is.null(P_full) && m >= 200L && sub_density > 0.25) {
    Psub <- P_full[C, C, drop = FALSE]
    pi_v <- rep(1 / m, m)
    for (it in seq_len(maxiter)) {
      nxt <- 0.5 * pi_v + 0.5 * as.numeric(pi_v %*% Psub)
      s <- sum(nxt); if (s > 0) nxt <- nxt / s
      if (max(abs(nxt - pi_v)) < tol) return(nxt)
      pi_v <- nxt
    }
    return(pi_v)
  }
  # === Chemin CREUX =============================================================
  # Pour les grandes classes (m >= 300) : sparse_vTP via rowsum vectorise (C).
  # Pour les petites : R-loop simple, car la construction du sous-sp domine le gain.
  loc <- integer(sp$n); loc[C] <- seq_len(m)
  pi_v <- rep(1 / m, m)
  if (m >= 300L) {
    sub_iv <- loc[sp$iv[in_sub]]
    sub_jv <- loc[sp$jv[in_sub]]
    sub_vv <- sp$vv[in_sub]
    sub_sp <- list(n = m, iv = sub_iv, jv = sub_jv, vv = sub_vv)
    for (it in seq_len(maxiter)) {
      nxt <- 0.5 * pi_v + 0.5 * sparse_vTP(pi_v, sub_sp)
      s <- sum(nxt); if (s > 0) nxt <- nxt / s
      if (max(abs(nxt - pi_v)) < tol) return(nxt)
      pi_v <- nxt
    }
    return(pi_v)
  }
  adj_loc <- vector("list", m); wt_loc <- vector("list", m)
  for (k in seq_len(m)) {
    i <- C[k]; js <- sp$adj_out[[i]]; ws <- sp$wt_out[[i]]
    sel <- loc[js] > 0L
    adj_loc[[k]] <- loc[js[sel]]; wt_loc[[k]] <- ws[sel]
  }
  for (it in seq_len(maxiter)) {
    out <- numeric(m)
    for (k in seq_len(m)) {
      js <- adj_loc[[k]]; pv <- pi_v[k]
      if (length(js) && pv != 0) out[js] <- out[js] + pv * wt_loc[[k]]
    }
    nxt <- 0.5 * pi_v + 0.5 * out
    s <- sum(nxt); if (s > 0) nxt <- nxt / s
    if (max(abs(nxt - pi_v)) < tol) return(nxt)
    pi_v <- nxt
  }
  pi_v
}

# --- Analyse complete ---------------------------------------------------------
# opts$fast = TRUE  -> approximations (maxiter reduit, eigen() saute si grand)
analyse_markov <- function(P, opts = list()) {
  fast <- isTRUE(opts$fast)
  is_sparse_only <- inherits(P, "markov_sparse_input")
  sp <- build_sparse(P); n <- sp$n
  # Shortcut : test BFS aller/retour pour graphes fortement connexes (souvent dense).
  sccs <- if (.is_one_scc(sp)) list(seq_len(n)) else tarjan_scc(sp$adj_out, n)
  nature <- vapply(sccs, function(C) class_nature_sparse(sp, C), character(1))
  per <- integer(n)
  for (k in seq_along(sccs)) per[sccs[[k]]] <- period_class_sparse(sp, sccs[[k]])
  pi_of <- rep(NA_real_, n); class_of <- integer(n); nature_of <- character(n)
  mxit <- if (fast) 800L else 10000L
  # Pour le mode sparse-pur, P_full est NULL -> stationary_power ne tente pas BLAS.
  P_full_arg <- if (is_sparse_only) NULL else P
  for (k in seq_along(sccs)) {
    C <- sccs[[k]]; class_of[C] <- k; nature_of[C] <- nature[k]
    if (nature[k] %in% c("Recurrente", "Absorbant"))
      pi_of[C] <- stationary_power(sp, C, maxiter = mxit, P_full = P_full_arg)
  }
  m_ret <- ifelse(nature_of == "Transitoire" | is.na(pi_of) | pi_of <= 0, Inf, 1 / pi_of)
  list(P = if (is_sparse_only) NULL else P, sp = sp, n = n, classes = sccs, nature = nature,
       class_of = class_of, nature_of = nature_of, period = per,
       pi = pi_of, m_return = m_ret, density = sp$density, fast = fast,
       sparse_pure = is_sparse_only)
}

# --- Prevision mu_t = mu0 P^t : creux si possible, dense sinon ----------------
# substeps>1 : applique substeps pas de P par increment de t (utile en annuel
# pour eviter de materialiser P^12 dense quand la matrice est grande).
forecast_markov <- function(model, mu0, horizon, substeps = 1L) {
  sp <- if (is.list(model) && !is.null(model$adj_out)) model
        else if (is.list(model) && !is.null(model$sp)) model$sp else NULL
  # densite haute -> mult dense (BLAS) plus rapide que rowsum sur triplets
  use_sparse <- !is.null(sp) && sp$density < 0.25
  P_dense <- if (is.null(sp)) model
             else if (!use_sparse) sp_to_dense(sp)
             else NULL
  n  <- if (!is.null(sp)) sp$n else nrow(model)
  M  <- matrix(0, horizon + 1L, n); mu <- mu0 / sum(mu0); M[1L, ] <- mu
  for (t in seq_len(horizon)) {
    for (s in seq_len(substeps))
      mu <- if (use_sparse) sparse_vTP(mu, sp) else as.numeric(mu %*% P_dense)
    M[t + 1L, ] <- mu
  }
  M
}

# Reconstruction dense (utile pour les iterations rapides via BLAS quand
# la densite ne justifie plus la sparse).
sp_to_dense <- function(sp) {
  M <- matrix(0, sp$n, sp$n)
  if (length(sp$iv)) M[cbind(sp$iv, sp$jv)] <- sp$vv
  M
}

# --- Exponentiation rapide : O(log k) multiplications matricielles ------------
matrix_power <- function(P, k) {
  n <- nrow(P); R <- diag(n); if (k <= 0L) return(R)
  B <- P; e <- as.integer(k)
  while (e > 0L) {
    if (e %% 2L == 1L) R <- R %*% B
    e <- e %/% 2L; if (e > 0L) B <- B %*% B
  }
  R
}

# --- Absorption : iterations creuses Gauss-Seidel (pas de solve()) ------------
# t = 1 + Q t   et   B = R + Q B   convergent car rho(Q) < 1 sur les transitoires.
# Cout : O(|E_transient|) par iteration ; tout reste creux.
absorption_analysis <- function(res, tol = 1e-10, maxiter = 20000L) {
  T <- which(res$nature_of == "Transitoire")
  rec <- which(res$nature %in% c("Recurrente", "Absorbant"))
  if (length(T) == 0L) return(list(ok = FALSE, msg = "Chaine sans etat transitoire : aucune absorption a analyser."))
  sp <- res$sp; m <- length(T); pos <- integer(sp$n); pos[T] <- seq_len(m)
  Q_j <- vector("list", m); Q_w <- vector("list", m)
  R_cls <- vector("list", m); R_w <- vector("list", m)
  class_of <- res$class_of
  for (k in seq_len(m)) {
    i <- T[k]; js <- sp$adj_out[[i]]; ws <- sp$wt_out[[i]]
    is_T <- pos[js] > 0L
    Q_j[[k]] <- pos[js[is_T]]; Q_w[[k]] <- ws[is_T]
    js_R <- js[!is_T]
    R_cls[[k]] <- match(class_of[js_R], rec); R_w[[k]] <- ws[!is_T]
  }
  t_vec <- rep(1, m)
  for (it in seq_len(maxiter)) {
    nt <- rep(1, m)
    for (k in seq_len(m)) {
      js <- Q_j[[k]]
      if (length(js)) nt[k] <- nt[k] + sum(Q_w[[k]] * t_vec[js])
    }
    if (max(abs(nt - t_vec)) < tol) { t_vec <- nt; break }
    t_vec <- nt
  }
  nc <- length(rec); Rconst <- matrix(0, m, nc)
  for (k in seq_len(m)) {
    cs <- R_cls[[k]]; ws <- R_w[[k]]
    if (length(cs)) for (l in seq_along(cs)) Rconst[k, cs[l]] <- Rconst[k, cs[l]] + ws[l]
  }
  B <- Rconst
  for (it in seq_len(maxiter)) {
    nB <- Rconst
    for (k in seq_len(m)) {
      js <- Q_j[[k]]
      if (length(js)) nB[k, ] <- nB[k, ] + as.numeric(Q_w[[k]] %*% B[js, , drop = FALSE])
    }
    if (max(abs(nB - B)) < tol) { B <- nB; break }
    B <- nB
  }
  list(ok = TRUE, T = T, rec = rec, N = NULL, t = t_vec, B = B)
}

# --- Metriques spectrales : eigen() si n petit ; deflation creuse sinon -------
spectral_metrics <- function(res) {
  n <- res$n
  # Strategie : eigen via LAPACK pour dense petit-moyen (BLAS bat la power-iter),
  # power-iter sparse pour grand & creux, et abandon en mode rapide pour grand.
  if (isTRUE(res$fast) && n > 600L)
    return(list(slem = NA_real_, kemeny = NA_real_))
  # Mode sparse-pur : pas de P dense -> eigen() impossible, approximation forcee.
  use_eigen <- !isTRUE(res$sparse_pure) && (n <= 600L || (n <= 1500L && res$density > 0.15))
  if (use_eigen) {
    ev <- tryCatch(eigen(res$P, only.values = TRUE)$values, error = function(e) NA_complex_)
    mods <- sort(Mod(ev), decreasing = TRUE)
    slem <- if (length(mods) >= 2L) mods[2L] else NA_real_
    kem <- NA_real_
    if (length(res$classes) == 1L && res$nature[1L] != "Transitoire") {
      ev2 <- ev[abs(ev - 1) > 1e-8]; kem <- if (length(ev2)) Re(sum(1 / (1 - ev2))) else NA_real_
    }
    return(list(slem = slem, kemeny = kem))
  }
  # approximation creuse : |lambda_2| par puissances avec deflation contre pi
  slem <- NA_real_
  if (length(res$classes) == 1L && res$nature[1L] != "Transitoire") {
    sp <- res$sp; pi_v <- res$pi; pi_v[is.na(pi_v)] <- 0
    v <- stats::rnorm(n); v <- v - sum(v) * pi_v
    nm <- sqrt(sum(v^2)); if (nm > 0) v <- v / nm
    lam <- 0
    for (it in seq_len(400L)) {
      w <- sparse_vTP(v, sp); w <- w - sum(w) * pi_v
      nm <- sqrt(sum(w^2)); if (nm < 1e-15) break
      if (abs(nm - lam) < 1e-8) { lam <- nm; break }
      lam <- nm; v <- w / nm
    }
    slem <- lam
  }
  list(slem = slem, kemeny = NA_real_)
}

# --- Heatmap downsamplee depuis triplets sans materialiser le dense -----------
# Pour le mode sparse-pur (n > 5000) : agglomere les triplets par bloc de
# bs x bs cellules, retourne une matrice nb x nb (<= 1200x1200) prete a image().
sp_to_heatmap <- function(sp, n, max_px = 1200L) {
  bs <- max(1L, as.integer(ceiling(n / max_px)))
  nb <- as.integer(ceiling(n / bs))
  H <- matrix(0, nb, nb)
  if (length(sp$iv)) {
    iv_b <- (sp$iv - 1L) %/% bs + 1L
    jv_b <- (sp$jv - 1L) %/% bs + 1L
    lin <- (jv_b - 1L) * nb + iv_b
    agg <- rowsum(sp$vv, lin, reorder = FALSE)
    H[as.integer(rownames(agg))] <- agg[, 1L]
  }
  list(H = H, bs = bs, nb = nb)
}

# --- Reorganisation en forme canonique par blocs ------------------------------
# Reordonne les etats : transitoires d'abord, puis classes recurrentes / absorbantes.
# La matrice resultante est triangulaire par blocs et met la structure en evidence.
reorganize_by_class <- function(res) {
  ord <- order(res$nature_of != "Transitoire", res$class_of, seq_len(res$n))
  # Mode sparse-pur : pas de P dense -> on retourne uniquement la permutation et
  # un sp reordonne (que show_matrix peut afficher via heatmap).
  if (isTRUE(res$sparse_pure) || is.null(res$P)) {
    inv <- integer(res$n); inv[ord] <- seq_len(res$n)
    sp2 <- res$sp; sp2$iv <- inv[sp2$iv]; sp2$jv <- inv[sp2$jv]
    return(list(P = NULL, sp = sp2, order = ord))
  }
  list(P = res$P[ord, ord, drop = FALSE], order = ord)
}


#2. ENTREE DES DONNEES  (robuste : tout type de saisie n x n)

# parse_matrix accepte deux formats automatiquement :
# (a) DENSE : une ligne par etat, n valeurs separees par espace/virgule/point-virgule.
# (b) CREUX (triplets) : "i j p" par ligne (indices a partir de 0 ou 1, auto-detecte).
#     1ere ligne optionnelle "n nnz" -> pre-allocation.
# Le parseur utilise scan() qui est ~20x plus rapide que strsplit/lapply pour les
# grandes matrices. Pour n=2000 dense (4M valeurs) on passe de plusieurs secondes
# a < 1s, et le format creux permet d'aller bien au-dela de n=10 000.
parse_matrix <- function(txt) {
  if (is.null(txt) || !nzchar(trimws(txt))) stop("Matrice vide.")
  # Support decimal comma : "0,03 0,5" -> "0.03 0.5". Heuristique robuste :
  # si AUCUN nombre n'utilise le point comme decimal (\d.\d absent), on
  # bascule les virgules entre chiffres en points decimaux. Sinon la virgule
  # est traitee comme separateur (CSV anglais "0.5,0.3,0.2").
  has_period_decimal <- grepl("[0-9]\\.[0-9]", txt)
  if (!has_period_decimal && grepl("[0-9],[0-9]", txt))
    txt <- gsub("([0-9]),([0-9])", "\\1.\\2", txt)
  # Normalise les fins de ligne pour la portabilite (Windows CRLF, Mac CR).
  txt <- gsub("\r\n", "\n", txt, fixed = TRUE); txt <- gsub("\r", "\n", txt, fixed = TRUE)
  # detection format creux : echantillon sur ~20 premieres lignes ; tous
  # doivent avoir 3 valeurs avec cols 1-2 entieres ; max(indice) > taille
  # de l'echantillon -> evite les faux positifs sur petite matrice dense.
  smp <- head(strsplit(txt, "\n", fixed = TRUE)[[1]], 20L)
  smp <- smp[nzchar(trimws(smp))]
  is_triplet <- FALSE
  if (length(smp) >= 3L) {
    tlist <- lapply(smp, function(l)
      suppressWarnings(scan(text = gsub("[,;]", " ", l), what = numeric(), quiet = TRUE)))
    lens <- vapply(tlist, length, integer(1L))
    if (all(lens == 3L)) {
      c1 <- vapply(tlist, `[`, numeric(1L), 1L)
      c2 <- vapply(tlist, `[`, numeric(1L), 2L)
      if (all(c1 == round(c1)) && all(c2 == round(c2)) &&
          all(c1 >= 0) && all(c2 >= 0) && max(c1, c2) > length(smp))
        is_triplet <- TRUE
    }
  }
  txt2 <- gsub("[,;]", " ", txt)
  if (is_triplet) {
    nums <- suppressWarnings(scan(text = txt2, what = numeric(), quiet = TRUE, sep = ""))
    if (length(nums) %% 3L != 0L) stop("Format creux : nombre de valeurs non multiple de 3.")
    m <- matrix(nums, ncol = 3L, byrow = TRUE)
    iv <- m[, 1L]; jv <- m[, 2L]; vv <- m[, 3L]
    base <- if (min(iv, jv) >= 1) 1L else 0L
    iv <- as.integer(iv) - base + 1L; jv <- as.integer(jv) - base + 1L
    n <- max(max(iv), max(jv))
    if (any(vv < 0)) stop("Probabilites negatives.")
    # Deduplication : (i,j) en doublon -> on somme les poids.
    ord <- order(iv, jv); iv <- iv[ord]; jv <- jv[ord]; vv <- vv[ord]
    same <- c(FALSE, iv[-1] == iv[-length(iv)] & jv[-1] == jv[-length(jv)])
    if (any(same)) {
      group <- cumsum(!same)
      vv <- as.numeric(rowsum(vv, group, reorder = FALSE))
      keep <- !same; iv <- iv[keep]; jv <- jv[keep]
    }
    # === Mode SPARSE-PUR pour n grand =========================================
    # Pour n > 5000 on evite matrix(0, n, n) qui consomme O(n^2) RAM (3.2 GB
    # pour n = 20000). On retourne un objet liste de classe "markov_sparse_input"
    # que normalize_rows / build_sparse / analyse_markov reconnaissent.
    if (n > 5000L) {
      return(structure(list(n = n, iv = iv, jv = jv, vv = vv),
                       class = "markov_sparse_input"))
    }
    M <- matrix(0, n, n); M[cbind(iv, jv)] <- vv
    attr(M, "sparse_triplets") <- list(iv = iv, jv = jv, vv = vv)
    return(M)
  }
  # format dense : on utilise scan() global puis on infere le nombre de colonnes
  lines <- strsplit(txt, "\n", fixed = TRUE)[[1]]
  lines <- lines[nzchar(trimws(lines))]
  if (!length(lines)) stop("Matrice vide.")
  # compte de valeurs par ligne via scan() ligne 1, puis suppose homogene
  n_col_first <- length(suppressWarnings(scan(text = gsub("[,;]", " ", lines[1L]),
                                              what = numeric(), quiet = TRUE)))
  if (n_col_first == 0L) stop("Aucune valeur sur la 1ere ligne.")
  nums <- suppressWarnings(scan(text = txt2, what = numeric(), quiet = TRUE))
  if (any(is.na(nums))) stop("Valeurs non numeriques detectees.")
  n_total <- length(nums)
  if (n_total %% n_col_first != 0L) {
    # diagnostique ligne par ligne (chemin lent uniquement en cas d'erreur)
    nc <- vapply(lines, function(l) length(suppressWarnings(scan(text = gsub("[,;]", " ", l),
                                                                  what = numeric(), quiet = TRUE))), integer(1))
    tb <- table(nc); freq <- as.integer(names(tb)[which.max(tb)]); bad <- which(nc != freq)
    stop(sprintf("Lignes de longueurs differentes : la plupart ont %d valeurs, mais la/les ligne(s) %s en a/ont %s. Astuce : utilisez le bouton \"Charger...\" plutot que le copier-coller, ou utilisez le format creux \"i j p\" par ligne.",
                 freq, paste(head(bad, 6), collapse = ", "), paste(nc[head(bad, 6)], collapse = ", ")))
  }
  n_rows <- n_total %/% n_col_first
  if (n_rows != n_col_first) stop(sprintf("Matrice non carree (%d x %d).", n_rows, n_col_first))
  if (any(nums < 0)) stop("Les probabilites doivent etre >= 0.")
  matrix(nums, n_rows, n_col_first, byrow = TRUE)
}
normalize_rows <- function(M) {
  # === Mode SPARSE-PUR ========================================================
  if (inherits(M, "markov_sparse_input")) {
    rs <- numeric(M$n)
    if (length(M$iv)) {
      agg <- rowsum(M$vv, M$iv, reorder = FALSE)
      rs[as.integer(rownames(agg))] <- agg[, 1L]
    }
    if (any(rs == 0)) stop("Une ligne somme a 0 : impossible de normaliser (etat sans transition sortante).")
    M$vv <- M$vv / rs[M$iv]
    return(M)
  }
  tri <- attr(M, "sparse_triplets")
  # Chemin creux : evite rowSums sur 100M cellules et M/rs (copies couteuses)
  if (!is.null(tri)) {
    n <- nrow(M)
    rs <- numeric(n)
    if (length(tri$iv)) {
      agg <- rowsum(tri$vv, tri$iv, reorder = FALSE)
      rs[as.integer(rownames(agg))] <- agg[, 1L]
    }
    if (any(rs == 0)) stop("Une ligne somme a 0 : impossible de normaliser.")
    tri$vv <- tri$vv / rs[tri$iv]
    M[cbind(tri$iv, tri$jv)] <- tri$vv
    attr(M, "sparse_triplets") <- tri
    return(M)
  }
  rs <- rowSums(M); if (any(rs == 0)) stop("Une ligne somme a 0 : impossible de normaliser.")
  M / rs
}
PRESETS <- list(
  "Finance (regimes de marche)" = list(
    m = "0.6 0.3 0.1 0\n0.2 0.5 0.2 0.1\n0.1 0.3 0.4 0.2\n0 0 0 1",
    labels = "Tres rentable\nStable\nDifficulte\nFaillite"),
  "Telecommunication (reseau)" = list(
    m = "0.7 0.3 0 0\n0.2 0.5 0.3 0\n0 0.3 0.5 0.2\n0.5 0 0.2 0.3",
    labels = "Libre\nOccupe\nCongestion\nCoupure"),
  "Entreprise (cycle de vie)" = list(
    m = "0.5 0.4 0.1 0\n0.1 0.6 0.2 0.1\n0 0.2 0.5 0.3\n0 0 0 1",
    labels = "Croissance\nMaturite\nDeclin\nFermeture"),
  "Fiabilite (machine)" = list(
    m = "0.9 0.1 0\n0 0.8 0.2\n0.95 0 0.05",
    labels = "Marche\nDegrade\nPanne"),
  "Exemple memoire (4 etats)" = list(
    m = "0.5 0.5 0 0\n0.5 0.5 0 0\n0.25 0.25 0.25 0.25\n0 0 0 1",
    labels = "E0\nE1\nE2\nE3")
)

#   3. PALETTE & DESSIN DU GRAPHE / PREVISION

COL_NATURE <- c(Recurrente = "#16a34a", Transitoire = "#f59e0b", Absorbant = "#ef4444")
COL_HEAD <- "#4f46e5"; COL_P1 <- "#6366f1"; COL_P2 <- "#8b5cf6"
COL_INK  <- "#1e293b"; COL_SUB <- "#64748b"
BG <- "#eef1fb"; CARD <- "#ffffff"; BORDER <- "#dfe4f2"

.tint <- function(hex, f = 0.82) { c <- col2rgb(hex); m <- round(c * (1 - f) + 255 * f); sprintf("#%02x%02x%02x", m[1], m[2], m[3]) }
forecast_palette <- function(n) hcl(h = seq(20, 380, length.out = n + 1)[1:n], c = 75, l = 58)

# geometrie du graphe : positions sur un cercle, etats regroupes par classe,
# avec un petit ecart angulaire entre classes pour mettre en evidence la structure.
graph_geometry <- function(res) {
  n <- res$n
  ord <- order(res$class_of, seq_len(n)); posOf <- integer(n); posOf[ord] <- seq_len(n)
  sorted_class <- res$class_of[ord]
  is_bound <- c(FALSE, diff(sorted_class) != 0L)
  nB <- sum(is_bound)
  if (nB > 0L && n >= 4L) {
    gap_total <- min(0.10 * 2 * pi, nB * 0.04)     # 4% par frontiere, plafonne a 10% total
    base <- (seq_len(n) - 1) * (2 * pi - gap_total) / n - pi / 2
    ang_sorted <- base + cumsum(is_bound) * (gap_total / nB)
  } else {
    ang_sorted <- (seq_len(n) - 1) * 2 * pi / n - pi / 2
  }
  ang <- ang_sorted[posOf]
  rad <- if (n == 1) 0.16 else max(0.012, min(0.15, 0.80 * sin(pi / n)))
  list(x = cos(ang), y = sin(ang), ang = ang, rad = rad, n = n, lim = 1.62 + rad)
}
# helpers : rad = rayon du noeud en coords-monde ; tailles de trait/fleche/texte CONSTANTES (px)
.garc <- function(x1, y1, x2, y2, rad, p, show_p, col) {
  dx <- x2 - x1; dy <- y2 - y1; L <- sqrt(dx^2 + dy^2); ux <- dx / L; uy <- dy / L
  xs <- x1 + rad * ux; ys <- y1 + rad * uy; xe <- x2 - rad * ux; ye <- y2 - rad * uy
  cx <- (xs + xe) / 2 - uy * 0.16 * L; cy <- (ys + ye) / 2 + ux * 0.16 * L
  tt <- seq(0, 1, length.out = 40)
  bx <- (1 - tt)^2 * xs + 2 * (1 - tt) * tt * cx + tt^2 * xe
  by <- (1 - tt)^2 * ys + 2 * (1 - tt) * tt * cy + tt^2 * ye
  lines(bx, by, lwd = 1.5, col = col)
  arrows(bx[37], by[37], bx[40], by[40], length = 0.07, lwd = 1.5, col = col)
  if (show_p) text(bx[20], by[20], sprintf("%.2f", p), cex = 0.78, col = COL_INK, font = 2)
}
.gloop <- function(x, y, ang, rad, p, show_p, col) {
  th <- seq(0, 2 * pi, length.out = 40)
  lx <- x + cos(ang) * (rad * 1.9) + rad * 0.95 * cos(th)
  ly <- y + sin(ang) * (rad * 1.9) + rad * 0.95 * sin(th)
  lines(lx, ly, lwd = 1.5, col = col)
  if (show_p) text(x + cos(ang) * (rad * 3.1), y + sin(ang) * (rad * 3.1), sprintf("%.2f", p), cex = 0.78, col = COL_INK, font = 2)
}
# dessine la PORTION VISIBLE du graphe
# Strategie multi-niveau selon |E| :
#   - |E| petit (<= 800)  : courbes Bezier + fleches (cas peda, peu de noeuds)
#   - |E| moyen (<= 6000) : Bezier sans labels
#   - |E| grand           : segments rectilignes vectorises (un seul appel R)
#                           + echantillonnage si > EDGE_CAP pour eviter le bruit
draw_graph <- function(res, labels, geom, xlim, ylim, cw, show_edges = TRUE, show_p_allowed = TRUE) {
  n <- res$n; x <- geom$x; y <- geom$y; ang <- geom$ang
  ppu <- cw / (xlim[2] - xlim[1])
  spacing_px <- 2 * sin(pi / max(n, 2)) * ppu
  node_px <- min(26, max(2, spacing_px * 0.42))
  node_w  <- node_px / ppu
  show_num   <- node_px > 6
  show_lab   <- spacing_px > 26
  show_loops <- show_edges && node_px > 4
  ecol <- adjustcolor("#475569", alpha.f = if (spacing_px < 8) 0.13 else if (spacing_px < 20) 0.32 else 0.66)
  par(mar = c(0, 0, 0, 0), bg = "white")
  plot(NA, xlim = xlim, ylim = ylim, xaxs = "i", yaxs = "i", axes = FALSE, xlab = "", ylab = "")
  if (show_edges) {
    sp <- res$sp; if (is.null(sp)) sp <- build_sparse(res$P)
    iv <- sp$iv; jv <- sp$jv; vv <- sp$vv
    is_loop <- iv == jv; n_loops <- sum(is_loop); n_arcs <- length(iv) - n_loops
    show_p_full <- show_p_allowed && spacing_px > 52 && n_arcs <= 300L
    EDGE_CAP <- 12000L
    # Cap automatique d'aretes au-dela de 5000 noeuds : illisible et lent
    auto_skip_edges <- n > 5000L
    if (!auto_skip_edges && n_arcs > 0L) {
      ai <- iv[!is_loop]; aj <- jv[!is_loop]; av <- vv[!is_loop]
      if (n_arcs <= 800L) {
        for (e in seq_len(n_arcs))
          .garc(x[ai[e]], y[ai[e]], x[aj[e]], y[aj[e]], node_w, av[e], show_p_full, ecol)
      } else {
        if (n_arcs > EDGE_CAP) {
          # priorise les aretes de plus fort poids : carte de densite plus informative
          ord_edges <- order(av, decreasing = TRUE)[seq_len(EDGE_CAP)]
          ai <- ai[ord_edges]; aj <- aj[ord_edges]; av <- av[ord_edges]
        }
        # alpha adaptatif : haute densite -> faible alpha pour densite visuelle
        alpha <- if (length(ai) > 6000L) 0.06 else if (length(ai) > 2000L) 0.15 else 0.4
        ecol2 <- adjustcolor("#475569", alpha.f = alpha)
        dx <- x[aj] - x[ai]; dy <- y[aj] - y[ai]
        L <- sqrt(dx * dx + dy * dy); L[L == 0] <- 1
        ux <- dx / L; uy <- dy / L
        x0 <- x[ai] + node_w * ux; y0 <- y[ai] + node_w * uy
        x1 <- x[aj] - node_w * ux; y1 <- y[aj] - node_w * uy
        segments(x0, y0, x1, y1, col = ecol2, lwd = 0.5)
      }
    }
    if (show_loops && n_loops > 0L && !auto_skip_edges) {
      li <- iv[is_loop]; lv <- vv[is_loop]
      for (e in seq_len(min(n_loops, 500L))) .gloop(x[li[e]], y[li[e]], ang[li[e]], node_w, lv[e], show_p_full, ecol)
    }
  }
  # n tres grand : pas d'anneau de cercles (illisible), on dessine des points
  if (n > 3000L) {
    points(x, y, pch = 16, col = COL_NATURE[res$nature_of], cex = max(0.2, min(1.2, node_px / 8)))
  } else {
    symbols(x, y, circles = rep(node_w, n), inches = FALSE, add = TRUE, bg = COL_NATURE[res$nature_of], fg = "white", lwd = 1.5)
  }
  if (show_num && n <= 3000L) text(x, y, labels = (1:n) - 1, col = "white", font = 2, cex = min(1.5, node_px / 15))
  if (show_lab) {
    off <- (node_px + 7) / ppu                         # decalage constant en pixels
    for (i in seq_len(n)) {
      ax <- 0.5 - 0.5 * sign(round(cos(ang[i]), 3))
      text(x[i] + cos(ang[i]) * off, y[i] + sin(ang[i]) * off, labels = labels[i], cex = 0.82, font = 2, col = COL_INK, adj = c(ax, 0.5))
    }
  }
}
# --- VUE AGREGEE PAR CLASSE ----------------------------------------------------
# Geometrie : K bulles disposees en cercle, rayon ~ sqrt(taille de classe).
class_geometry <- function(res) {
  K <- length(res$classes)
  ang <- if (K == 1L) 0 else (seq_len(K) - 1) * 2 * pi / K - pi / 2
  x <- if (K == 1L) 0 else cos(ang)
  y <- if (K == 1L) 0 else sin(ang)
  sz <- vapply(res$classes, length, integer(1L))
  rad <- 0.08 + 0.18 * sqrt(sz / max(sz)) * (if (K <= 3L) 1.2 else if (K <= 8L) 1.0 else 0.75)
  list(x = x, y = y, ang = ang, rad = rad, K = K, sz = sz, lim = 1.5)
}

# Flux inter-classe : somme P[i,j] pour i in C_a, j in C_b, normalise par |C_a|.
# Calcul O(|E|) vectorise via les triplets sparse.
class_flows <- function(res) {
  K <- length(res$classes); cls_of <- res$class_of
  iv <- res$sp$iv; jv <- res$sp$jv; vv <- res$sp$vv
  if (!length(iv)) return(matrix(0, K, K))
  ca <- cls_of[iv]; cb <- cls_of[jv]
  lin <- (cb - 1L) * K + ca
  agg <- rowsum(vv, lin, reorder = FALSE)
  F <- numeric(K * K); F[as.integer(rownames(agg))] <- agg[, 1L]
  F <- matrix(F, K, K)
  # normalise par |C_a| pour avoir "flux moyen sortant par etat"
  cls_sizes <- vapply(res$classes, length, integer(1L))
  F / cls_sizes
}

# Dessine la vue par classes : O(K) noeuds + O(K^2) aretes (toujours <100 elements
# en pratique pour les chaines reelles), donc instantane meme pour n = 50 000.
draw_graph_classes <- function(res, geom_c, xlim, ylim, cw, show_edges = TRUE) {
  K <- geom_c$K; x <- geom_c$x; y <- geom_c$y; rad <- geom_c$rad
  par(mar = c(0, 0, 0, 0), bg = "white")
  plot(NA, xlim = xlim, ylim = ylim, xaxs = "i", yaxs = "i", axes = FALSE, xlab = "", ylab = "")
  if (show_edges && K > 1L) {
    F <- class_flows(res)
    fmax <- max(F[F < 1])
    if (fmax > 0) {
      for (a in seq_len(K)) for (b in seq_len(K)) if (a != b && F[a, b] > 1e-4) {
        rel <- F[a, b] / fmax
        col <- adjustcolor("#475569", alpha.f = max(0.15, min(0.9, rel)))
        .garc(x[a], y[a], x[b], y[b], rad[a], F[a, b], TRUE, col)
      }
    }
  }
  cnat <- res$nature
  symbols(x, y, circles = rad, inches = FALSE, add = TRUE,
          bg = COL_NATURE[cnat], fg = "white", lwd = 2)
  for (k in seq_len(K)) {
    txt <- paste0("C", k, "\n", geom_c$sz[k], " etats")
    text(x[k], y[k], labels = txt, col = "white", font = 2, cex = min(1.4, rad[k] * 8))
  }
}

draw_forecast_plot <- function(M, labels, unit, pistar = NULL, max_curves = 30L) {
  horizon <- nrow(M) - 1L; n <- ncol(M); pal_all <- forecast_palette(n)
  # n grand : limiter aux top max_curves courbes par amplitude (sinon hairball)
  sel <- if (n > max_curves) {
    amp <- apply(M, 2L, function(c) max(c) - min(c))
    order(amp, decreasing = TRUE)[seq_len(max_curves)]
  } else seq_len(n)
  Ms <- M[, sel, drop = FALSE]; pal <- pal_all[sel]; labs_s <- labels[sel]
  par(mar = c(4.4, 4.4, 1.2, 1), bg = "white")
  matplot(0:horizon, Ms, type = "l", lty = 1, lwd = 2.3, col = pal, ylim = c(0, 1),
          xlab = paste0("Temps (", unit, ")"), ylab = "Probabilite d'occupation de l'etat",
          cex.axis = 0.9, cex.lab = 0.95)
  grid(col = "#eef1f7"); matlines(0:horizon, Ms, lty = 1, lwd = 2.3, col = pal)
  if (!is.null(pistar)) for (k in seq_along(sel)) if (!is.na(pistar[sel[k]]))
    abline(h = pistar[sel[k]], col = adjustcolor(pal[k], alpha.f = 0.5), lty = 3)
  points(rep(horizon, length(sel)), Ms[horizon + 1L, ], pch = 19, col = pal, cex = 1)
  if (length(sel) <= 14) legend("topright", legend = labs_s, col = pal, lwd = 3, bty = "n", cex = 0.82, text.font = 2)
  else if (n > max_curves) mtext(sprintf("(%d/%d courbes affichees, classees par amplitude)", length(sel), n),
                                  side = 3, line = 0.1, adj = 1, cex = 0.75, col = COL_SUB)
}

#4. COMPOSANTS D'INTERFACE

#visualiseur d'image
image_viewer <- function(parent) {
  top <- ttkframe(parent); bar <- ttkframe(top, padding = 5); tkpack(bar, side = "top", fill = "x")
  wrap <- ttkframe(top); tkpack(wrap, side = "top", fill = "both", expand = TRUE)
  cv  <- tkcanvas(wrap, background = "white", highlightthickness = 0)
  ysc <- ttkscrollbar(wrap, orient = "vertical",   command = function(...) tkyview(cv, ...))
  xsc <- ttkscrollbar(wrap, orient = "horizontal", command = function(...) tkxview(cv, ...))
  tkconfigure(cv, yscrollcommand = function(...) tkset(ysc, ...), xscrollcommand = function(...) tkset(xsc, ...))
  tkgrid(cv, row = 0, column = 0, sticky = "nsew"); tkgrid(ysc, row = 0, column = 1, sticky = "ns"); tkgrid(xsc, row = 1, column = 0, sticky = "ew")
  tkgrid.rowconfigure(wrap, 0, weight = 1); tkgrid.columnconfigure(wrap, 0, weight = 1)

  env <- new.env()
  env$zoom <- 1; env$drawfn <- NULL; env$basew <- 1000; env$baseh <- 600; env$srcw <- 1000
  env$file <- tempfile(fileext = ".png"); env$img <- NULL; env$src <- NULL; env$pending <- NULL
  env$bar <- bar; env$cv <- cv; env$MAXPX <- 4200

  env$place <- function() {
    if (is.null(env$img)) return(invisible())
    cvw <- suppressWarnings(as.numeric(tclvalue(tkwinfo("width", cv)))); cvh <- suppressWarnings(as.numeric(tclvalue(tkwinfo("height", cv))))
    if (is.na(cvw) || cvw < 20) cvw <- 900; if (is.na(cvh) || cvh < 20) cvh <- 560
    w <- as.integer(tclvalue(tkimage.width(env$img))); h <- as.integer(tclvalue(tkimage.height(env$img)))
    rw <- max(w, cvw); rh <- max(h, cvh)
    tcl(cv, "delete", "all"); tkcreate(cv, "image", (rw - w) / 2, (rh - h) / 2, anchor = "nw", image = env$img)
    tcl(cv, "configure", "-scrollregion", paste(0, 0, rw, rh))
  }
  env$render_at <- function(w, h) {                  # rendu vectoriel NET a la taille demandee
    if (is.null(env$drawfn)) return(invisible())
    grDevices::png(env$file, width = max(60, round(w)), height = max(60, round(h)), res = 96)
    tryCatch(env$drawfn(), finally = grDevices::dev.off())
    env$img <- tkimage.create("photo", file = env$file); env$src <- env$img; env$srcw <- w; env$place()
  }
  env$crisp <- function() {
    s <- min(env$zoom, env$MAXPX / env$basew, env$MAXPX / env$baseh)
    env$render_at(env$basew * s, env$baseh * s)
  }
  env$preview <- function() {                        # apercu instantane (mise a l'echelle de la derniere image nette)
    if (is.null(env$src)) return(invisible())
    f <- env$zoom / (env$srcw / env$basew)
    disp <- tkimage.create("photo")
    if (abs(f - 1) < 0.03) tcl(disp, "copy", env$src)
    else if (f > 1) tcl(disp, "copy", env$src, "-zoom", max(1L, as.integer(round(f))))
    else tcl(disp, "copy", env$src, "-subsample", max(1L, as.integer(round(1 / f))))
    env$img <- disp; env$place()
  }
  env$schedule <- function() {
    if (!is.null(env$pending)) tcl("after", "cancel", env$pending)
    env$pending <- tclvalue(tcl("after", 170, function() { env$pending <- NULL; env$crisp() }))
  }
  env$fit <- function() {
    cvw <- suppressWarnings(as.numeric(tclvalue(tkwinfo("width", cv)))); cvh <- suppressWarnings(as.numeric(tclvalue(tkwinfo("height", cv))))
    if (is.na(cvw) || cvw < 20) cvw <- 900; if (is.na(cvh) || cvh < 20) cvh <- 560
    env$zoom <- max(0.12, min(cvw / env$basew, cvh / env$baseh)); env$crisp()
  }
  env$set <- function(drawfn, basew, baseh) { env$drawfn <- drawfn; env$basew <- basew; env$baseh <- baseh; env$fit() }
  env$zoomby <- function(f) { env$zoom <- max(0.12, min(8, env$zoom * f)); env$preview(); env$schedule() }

  tkpack(ttkbutton(bar, text = "+", width = 3, command = function() env$zoomby(1.3)),  side = "left", padx = 1)
  tkpack(ttkbutton(bar, text = "-", width = 3, command = function() env$zoomby(1 / 1.3)), side = "left", padx = 1)
  tkpack(ttkbutton(bar, text = "Ajuster", width = 8, command = function() env$fit()), side = "left", padx = 3)
  tkpack(ttklabel(bar, text = "molette: defiler  -  Ctrl+molette: zoom", foreground = COL_SUB), side = "left", padx = 6)
  tkbind(cv, "<Button-4>", function() tkyview(cv, "scroll", -3, "units"))
  tkbind(cv, "<Button-5>", function() tkyview(cv, "scroll",  3, "units"))
  tkbind(cv, "<Shift-Button-4>", function() tkxview(cv, "scroll", -3, "units"))
  tkbind(cv, "<Shift-Button-5>", function() tkxview(cv, "scroll",  3, "units"))
  tkbind(cv, "<Control-Button-4>", function() env$zoomby(1.3))
  tkbind(cv, "<Control-Button-5>", function() env$zoomby(1 / 1.3))
  tkbind(cv, "<MouseWheel>",         function(D) tkyview(cv, "scroll", if (as.numeric(D) > 0) -3 else 3, "units"))
  tkbind(cv, "<Control-MouseWheel>", function(D) env$zoomby(if (as.numeric(D) > 0) 1.3 else 1 / 1.3))
  tkbind(cv, "<Configure>", function() env$place())
  env$frame <- top; env
}

#visualiseur de GRAPHE
graph_viewer <- function(parent) {
  top <- ttkframe(parent); bar <- ttkframe(top, padding = 5); tkpack(bar, side = "top", fill = "x")
  wrap <- ttkframe(top); tkpack(wrap, side = "top", fill = "both", expand = TRUE)
  cv  <- tkcanvas(wrap, background = "white", highlightthickness = 0, cursor = "fleur")
  ysc <- ttkscrollbar(wrap, orient = "vertical",   command = function(...) env$yview(...))
  xsc <- ttkscrollbar(wrap, orient = "horizontal", command = function(...) env$xview(...))
  tkgrid(cv, row = 0, column = 0, sticky = "nsew"); tkgrid(ysc, row = 0, column = 1, sticky = "ns"); tkgrid(xsc, row = 1, column = 0, sticky = "ew")
  tkgrid.rowconfigure(wrap, 0, weight = 1); tkgrid.columnconfigure(wrap, 0, weight = 1)

  env <- new.env()
  env$res <- NULL; env$labels <- NULL; env$geom <- NULL; env$geom_c <- NULL
  env$edges <- TRUE; env$showp <- TRUE
  env$z <- 1; env$cx <- 0; env$cy <- 0; env$lim <- 1.7; env$ppu <- 1
  env$M <- 2.4; env$rcx <- 0; env$rcy <- 0; env$rhw <- 0; env$rhh <- 0; env$boffx <- 0; env$boffy <- 0; env$item <- NULL
  env$file <- tempfile(fileext = ".png"); env$img <- NULL; env$drag <- NULL; env$bar <- bar; env$busy <- FALSE
  env$pending <- NULL
  # view_mode : "auto" -> classes si zoom <= LOD_ZOOM, noeuds sinon
  # "nodes"     -> toujours noeuds individuels
  # "classes"   -> toujours bulles par classe
  env$view_mode <- "auto"; env$LOD_ZOOM <- 4
  env$set_view <- function(mode) { env$view_mode <- mode; env$render() }

  cwh <- function() {
    w <- suppressWarnings(as.numeric(tclvalue(tkwinfo("width", cv)))); h <- suppressWarnings(as.numeric(tclvalue(tkwinfo("height", cv))))
    if (is.na(w) || w < 20) w <- 900; if (is.na(h) || h < 20) h <- 560; c(w, h)
  }
  halfs <- function() { d <- cwh(); hh <- env$lim / env$z; c(hh * d[1] / d[2], hh) }  # (halfw, halfh)
  env$clamp <- function() {
    hs <- halfs()
    env$cx <- if (hs[1] >= env$lim) 0 else max(-(env$lim - hs[1]), min(env$lim - hs[1], env$cx))
    env$cy <- if (hs[2] >= env$lim) 0 else max(-(env$lim - hs[2]), min(env$lim - hs[2], env$cy))
  }
  upd_sb <- function() {
    hs <- halfs()
    tkset(xsc, max(0, (env$cx - hs[1] + env$lim) / (2 * env$lim)), min(1, (env$cx + hs[1] + env$lim) / (2 * env$lim)))
    tkset(ysc, max(0, (env$lim - (env$cy + hs[2])) / (2 * env$lim)), min(1, (env$lim - (env$cy - hs[2])) / (2 * env$lim)))
  }
  env$render <- function() {
    if (is.null(env$res) || env$busy) return(invisible())
    env$busy <- TRUE; on.exit(env$busy <- FALSE)
    d <- cwh(); cw <- d[1]; ch <- d[2]; hs <- halfs(); env$ppu <- cw / (2 * hs[1])
    M <- env$M; rhw <- hs[1] * M; rhh <- hs[2] * M
    MAXPX <- 2400L
    iw <- min(MAXPX, max(200L, round(cw * M))); ih <- min(MAXPX, max(200L, round(ch * M)))
    # Determine quelle vue rendre (LOD adaptatif si "auto")
    mode <- env$view_mode
    if (mode == "auto") mode <- if (env$z <= env$LOD_ZOOM && length(env$res$classes) > 1L) "classes" else "nodes"
    grDevices::png(env$file, width = iw, height = ih, res = 96)
    tryCatch({
      if (mode == "classes") {
        if (is.null(env$geom_c)) env$geom_c <- class_geometry(env$res)
        draw_graph_classes(env$res, env$geom_c,
                           env$cx + c(-rhw, rhw), env$cy + c(-rhh, rhh), iw, env$edges)
      } else {
        draw_graph(env$res, env$labels, env$geom,
                   env$cx + c(-rhw, rhw), env$cy + c(-rhh, rhh), iw, env$edges, env$showp)
      }
    }, finally = grDevices::dev.off())
    env$img <- tkimage.create("photo", file = env$file)
    env$boffx <- -(iw - cw) / 2; env$boffy <- -(ih - ch) / 2
    tcl(cv, "delete", "all"); env$item <- tclvalue(tkcreate(cv, "image", env$boffx, env$boffy, anchor = "nw", image = env$img))
    env$rcx <- env$cx; env$rcy <- env$cy; env$rhw <- rhw; env$rhh <- rhh
    upd_sb()
  }
  env$slide <- function() {                               # deplace l'image deja rendue (instantane)
    if (is.null(env$item)) return(invisible())
    tcl(cv, "coords", env$item, env$boffx + (env$rcx - env$cx) * env$ppu, env$boffy + (env$cy - env$rcy) * env$ppu)
    upd_sb()
  }
  env$pan_to <- function(ncx, ncy) {
    env$cx <- ncx; env$cy <- ncy; env$clamp(); hs <- halfs()
    if (!is.null(env$item) && abs(env$cx - env$rcx) <= (env$rhw - hs[1]) && abs(env$cy - env$rcy) <= (env$rhh - hs[2]))
      env$slide()                                         # reste dans la marge => glissement fluide
    else env$render()                                     # sort de la marge => re-rendu
  }
  env$xview <- function(...) {
    a <- list(...); hs <- halfs()
    if (a[[1]] == "moveto") env$pan_to(-env$lim + hs[1] + as.numeric(a[[2]]) * 2 * env$lim, env$cy)
    else env$pan_to(env$cx + sign(as.numeric(a[[2]])) * hs[1] * (if (length(a) >= 3 && a[[3]] == "pages") 1 else 0.2), env$cy)
  }
  env$yview <- function(...) {
    a <- list(...); hs <- halfs()
    if (a[[1]] == "moveto") env$pan_to(env$cx, env$lim - hs[2] - as.numeric(a[[2]]) * 2 * env$lim)
    else env$pan_to(env$cx, env$cy - sign(as.numeric(a[[2]])) * hs[2] * (if (length(a) >= 3 && a[[3]] == "pages") 1 else 0.2))
  }
  # Debounce : si plusieurs zooms se succedent, on annule le rendu en attente
  # et on en re-planifie un nouveau. Limite les re-renders couteux a 1 toutes
  # les 100ms maxi pendant un scroll/zoom continu.
  env$schedule_render <- function(delay = 100L) {
    if (!is.null(env$pending)) tcl("after", "cancel", env$pending)
    env$pending <- tclvalue(tcl("after", delay, function() { env$pending <- NULL; env$render() }))
  }
  env$zoom_at <- function(f, px, py) {
    d <- cwh(); cw <- d[1]; ch <- d[2]
    wx <- env$cx + (px - cw / 2) / env$ppu; wy <- env$cy - (py - ch / 2) / env$ppu
    env$z <- max(1, min(260, env$z * f)); hs <- halfs(); newppu <- cw / (2 * hs[1])
    env$cx <- wx - (px - cw / 2) / newppu; env$cy <- wy + (py - ch / 2) / newppu
    env$clamp(); env$schedule_render()
  }
  env$zoomby <- function(f) { d <- cwh(); env$zoom_at(f, d[1] / 2, d[2] / 2) }
  env$fit <- function() { env$z <- 1; env$cx <- 0; env$cy <- 0; env$render() }
  env$set_data <- function(res, labels, edges, showp) {
    env$res <- res; env$labels <- labels; env$edges <- edges; env$showp <- showp
    env$geom <- graph_geometry(res); env$geom_c <- NULL  # recalcul lazy
    env$lim <- env$geom$lim; env$fit()
  }

  tkpack(ttkbutton(bar, text = "+", width = 3, command = function() env$zoomby(1.4)),  side = "left", padx = 1)
  tkpack(ttkbutton(bar, text = "-", width = 3, command = function() env$zoomby(1 / 1.4)), side = "left", padx = 1)
  tkpack(ttkbutton(bar, text = "Ajuster", width = 8, command = function() env$fit()), side = "left", padx = 3)
  tkpack(ttklabel(bar, text = "molette: zoom (vers le curseur)  -  glisser (clic gauche ou droit): deplacer", foreground = COL_SUB), side = "left", padx = 6)
  startdrag <- function(x, y) env$drag <- c(as.numeric(x), as.numeric(y))
  dodrag <- function(x, y) {
    if (is.null(env$drag)) return()
    env$pan_to(env$cx - (as.numeric(x) - env$drag[1]) / env$ppu, env$cy + (as.numeric(y) - env$drag[2]) / env$ppu)
    env$drag <- c(as.numeric(x), as.numeric(y))
  }
  enddrag <- function() { env$drag <- NULL; env$render() }   # re-centre la marge a la fin
  tkbind(cv, "<ButtonPress-1>", startdrag);  tkbind(cv, "<B1-Motion>", dodrag);  tkbind(cv, "<ButtonRelease-1>", enddrag)
  tkbind(cv, "<ButtonPress-3>", startdrag);  tkbind(cv, "<B3-Motion>", dodrag);  tkbind(cv, "<ButtonRelease-3>", enddrag)
  tkbind(cv, "<Button-4>", function(x, y) env$zoom_at(1.25, as.numeric(x), as.numeric(y)))
  tkbind(cv, "<Button-5>", function(x, y) env$zoom_at(1 / 1.25, as.numeric(x), as.numeric(y)))
  tkbind(cv, "<MouseWheel>", function(x, y, D) env$zoom_at(if (as.numeric(D) > 0) 1.25 else 1 / 1.25, as.numeric(x), as.numeric(y)))
  tkbind(cv, "<Configure>", function() env$schedule_render(80L))
  env$frame <- top; env
}

#tableau defilable (ttk::treeview)
# Ajout scroll horizontal + vertical sur TOUS les tableaux.
# Permet de voir toutes les donnees meme si le tableau est grand (beaucoup de colonnes ou lignes)
# ou quand l'utilisateur etire/redimensionne la fenetre.
make_tree <- function(parent, cols, headers, widths, anchors = NULL, hscroll = TRUE, height = 16) {
  fr <- ttkframe(parent)
  tv  <- ttktreeview(fr, columns = cols, show = "headings", height = height, selectmode = "browse")
  ysc <- ttkscrollbar(fr, orient = "vertical", command = function(...) tkyview(tv, ...))
  tkconfigure(tv, yscrollcommand = function(...) tkset(ysc, ...))
  if (is.null(anchors)) anchors <- rep("center", length(cols))
  for (i in seq_along(cols)) {
    tcl(tv, "heading", cols[i], "-text", headers[i])
    tcl(tv, "column", cols[i], "-width", widths[i], "-anchor", anchors[i], "-stretch", 0L)
  }
  tcl(tv, "tag", "configure", "rec", "-background", .tint(COL_NATURE[["Recurrente"]], 0.86))
  tcl(tv, "tag", "configure", "tra", "-background", .tint(COL_NATURE[["Transitoire"]], 0.86))
  tcl(tv, "tag", "configure", "abs", "-background", .tint(COL_NATURE[["Absorbant"]], 0.86))
  tkgrid(tv, row = 0, column = 0, sticky = "nsew"); tkgrid(ysc, row = 0, column = 1, sticky = "ns")
  if (hscroll) {
    xsc <- ttkscrollbar(fr, orient = "horizontal", command = function(...) tkxview(tv, ...))
    tkconfigure(tv, xscrollcommand = function(...) tkset(xsc, ...)); tkgrid(xsc, row = 1, column = 0, sticky = "ew")
  }
  # Configuration robuste pour le redimensionnement (stretch de la fenetre)
  tkgrid.rowconfigure(fr, 0, weight = 1)
  tkgrid.columnconfigure(fr, 0, weight = 1)
  tkgrid.columnconfigure(fr, 1, weight = 0)
  if (hscroll) {
    tkgrid.rowconfigure(fr, 1, weight = 0)
  }
  list(frame = fr, tv = tv)
}
.tag_nat <- function(nature) switch(nature, Recurrente = "rec", Transitoire = "tra", Absorbant = "abs", "")
.clear_tree <- function(tv) for (it in as.character(tcl(tv, "children", ""))) tcl(tv, "delete", it)
.clear_children <- function(parent) for (w in as.character(tkwinfo("children", parent))) tcl("destroy", w)
.row <- function(tv, vals, tag = "") tkinsert(tv, "", "end", tags = tag, values = as.tclObj(as.character(vals), drop = TRUE))

#carte KPI (tableau de bord)
add_card <- function(parent, r, c, label, accent) {
  o <- tkframe(parent, background = BORDER, padx = 1, pady = 1)
  tkgrid(o, row = r, column = c, padx = 6, pady = 6, sticky = "nsew")
  cd <- tkframe(o, background = CARD); tkpack(cd, fill = "both", expand = TRUE)
  tkpack(tkframe(cd, background = accent, height = 4), side = "top", fill = "x")
  v <- tclVar("-")
  tkpack(tklabel(cd, textvariable = v, background = CARD, foreground = accent, font = "{Sans} 22 bold"), pady = c(9, 0))
  tkpack(tklabel(cd, text = label, background = CARD, foreground = COL_SUB, font = "{Sans} 12"), pady = c(0, 9))
  v
}

#5. FENETRE PRINCIPALE
launch_app <- function() {
  if (!interactive() && !nzchar(Sys.getenv("DISPLAY")) && .Platform$OS.type != "windows")
    message("Note : aucun affichage detecte (DISPLAY vide). Lancez en session graphique.")

  st <- new.env(); st$model <- NULL; st$abs <- NULL; st$spec <- NULL

  tt <- tktoplevel(); tkwm.title(tt, "Markov Studio  -  Analyse des chaines de Markov")
  tkwm.geometry(tt, "1500x920"); tkwm.minsize(tt, 1280, 800); tkconfigure(tt, background = BG)
  TABIDLE <- "#d7dcf0"
  themes <- as.character(tcl("ttk::style", "theme", "names"))
  tcl("ttk::style", "theme", "use", if ("clam" %in% themes) "clam" else "default")
  tcl("ttk::style", "configure", ".", background = BG, foreground = COL_INK, font = "{Sans} 12",
      bordercolor = BORDER, troughcolor = "#dde3f3", focuscolor = COL_P1, arrowcolor = COL_HEAD)
  for (s in c("TFrame", "TLabel", "TCheckbutton", "TRadiobutton")) tcl("ttk::style", "configure", s, background = BG)
  tcl("ttk::style", "configure", "TLabel", foreground = COL_INK)
  tcl("ttk::style", "configure", "TNotebook", background = BG, borderwidth = 0, tabmargins = c(6, 6, 6, 0))
  tcl("ttk::style", "configure", "TNotebook.Tab", padding = c(15, 7), font = "{Sans} 13 bold", background = TABIDLE, foreground = COL_SUB, borderwidth = 0)
  tcl("ttk::style", "map", "TNotebook.Tab", "-background", as.tclObj(c("selected", CARD), drop = TRUE), "-foreground", as.tclObj(c("selected", COL_HEAD), drop = TRUE))
  tcl("ttk::style", "configure", "Treeview", background = CARD, fieldbackground = CARD, foreground = COL_INK, rowheight = 26L, font = "{Sans} 12", borderwidth = 0)
  tcl("ttk::style", "configure", "Treeview.Heading", background = COL_HEAD, foreground = "white", font = "{Sans} 12 bold", relief = "flat", padding = c(5, 5))
  tcl("ttk::style", "map", "Treeview.Heading", "-background", as.tclObj(c("active", COL_P2), drop = TRUE))
  tcl("ttk::style", "map", "Treeview", "-background", as.tclObj(c("selected", "#dbe0ff"), drop = TRUE), "-foreground", as.tclObj(c("selected", COL_INK), drop = TRUE))
  tcl("ttk::style", "configure", "TButton", padding = 5, relief = "flat", background = "#e2e7f6", foreground = COL_INK)
  tcl("ttk::style", "map", "TButton", "-background", as.tclObj(c("active", "#cfd6ee"), drop = TRUE))
  tcl("ttk::style", "configure", "Go.TButton", background = COL_P1, foreground = "white", font = "{Sans} 14 bold", padding = 9, relief = "flat")
  tcl("ttk::style", "map", "Go.TButton", "-background", as.tclObj(c("active", COL_P2, "pressed", COL_P2), drop = TRUE), "-foreground", as.tclObj(c("active", "white"), drop = TRUE))

  # en-tete
  hh <- 64
  cvh <- tkcanvas(tt, height = hh, highlightthickness = 0, bd = 0); tkpack(cvh, side = "top", fill = "x")
  c1 <- col2rgb(COL_HEAD); c2 <- col2rgb(COL_P2)
  draw_header <- function() {
    w <- as.integer(tclvalue(tkwinfo("width", cvh))); if (is.na(w) || w < 10) w <- 1340
    tcl(cvh, "delete", "all")
    for (i in seq(0, w, by = 3)) { f <- i / w; rg <- round(c1 * (1 - f) + c2 * f)
      tkcreate(cvh, "rectangle", i, 0, i + 3, hh, fill = sprintf("#%02x%02x%02x", rg[1], rg[2], rg[3]), width = 0) }
    tkcreate(cvh, "text", 24, hh * 0.40, anchor = "w", text = "Markov Studio", fill = "white", font = "{Sans} 20 bold")
    tkcreate(cvh, "text", 26, hh * 0.78, anchor = "w", text = "Analyse complete des chaines de Markov  -  classification, stationnaire, absorption, prevision", fill = "#e8ebff", font = "{Sans} 12")
  }
  tkbind(cvh, "<Configure>", draw_header)

  body <- ttkframe(tt); tkpack(body, side = "top", fill = "both", expand = TRUE)

  #statusbar (bas) avec barre de progression Tk
  statusVar <- tclVar("Pret."); statusFg <- COL_SUB
  sb <- ttkframe(tt, padding = c(10, 4)); tkpack(sb, side = "bottom", fill = "x")
  statusLbl <- ttklabel(sb, textvariable = statusVar, font = "{Sans} 12 bold", foreground = COL_SUB)
  tkpack(statusLbl, side = "left")
  # Progress bar : packee EN PERMANENCE (sinon Tk n'a pas le temps de la rendre
  # avant que R reprenne la main pour le calcul lourd). Animation indeterminate.
  tkpack(ttklabel(sb, text = "Markov Studio v3  -  portable (R + tcltk)", foreground = COL_SUB), side = "right")
  progBar <- ttkprogressbar(sb, mode = "determinate", length = 160, maximum = 100)
  tkpack(progBar, side = "right", padx = 10)
  tcl(progBar, "configure", value = 0)
  prog_show <- function(msg, value = NULL) {
    tclvalue(statusVar) <- msg; tkconfigure(statusLbl, foreground = COL_HEAD)
    if (is.null(value)) {
      tcl(progBar, "configure", mode = "indeterminate")
      tcl(progBar, "start", 12)
    } else {
      tcl(progBar, "stop")
      tcl(progBar, "configure", mode = "determinate", value = max(0, min(100, value)))
    }
    tcl("update")   # tcl("update") force ALL events (rendu inclus) -- pas juste idletasks
  }
  prog_hide <- function() {
    tcl(progBar, "stop")
    tcl(progBar, "configure", mode = "determinate", value = 0)
    tcl("update", "idletasks")
  }

  #onglets
  right <- ttkframe(body, padding = 8); tkpack(right, side = "top", fill = "both", expand = TRUE)
  nb <- ttknotebook(right); tkpack(nb, fill = "both", expand = TRUE)
  tabD <- ttkframe(nb); tabR <- ttkframe(nb); tabG <- ttkframe(nb); tabC <- ttkframe(nb); tabM <- ttkframe(nb); tabS <- ttkframe(nb); tabP <- ttkframe(nb)
  tcl(nb, "add", tabD, "-text", " 1. Saisie des donnees ")
  tcl(nb, "add", tabR, "-text", " Resume ")
  tcl(nb, "add", tabG, "-text", " Graphe ")
  tcl(nb, "add", tabC, "-text", " Classification ")
  tcl(nb, "add", tabM, "-text", " Matrice  P / P^k ")
  tcl(nb, "add", tabS, "-text", " Stationnaire & absorption ")
  tcl(nb, "add", tabP, "-text", " Prevision ")

  ##onglet Saisie des donnees
  # Ajout d'un scroll vertical global pour tout l'onglet Saisie (utile quand la fenetre est petite
  # ou que le texte de la matrice + libelles + conseils est long). Le contenu interne (matTxt, labTxt)
  # garde ses propres scrolls.
  cnv <- tkcanvas(tabD, highlightthickness = 0, bd = 0, bg = BG)
  ys  <- ttkscrollbar(tabD, orient = "vertical", command = function(...) tkyview(cnv, ...))
  tkconfigure(cnv, yscrollcommand = function(...) tkset(ys, ...))

  inner <- ttkframe(cnv)   # tout l'ancien contenu (dL + dR) va ici

  # Contenu original de l'onglet (dL a gauche, dR a droite) place dans inner
  dR <- ttkframe(inner, padding = 16); tkpack(dR, side = "right", fill = "y")
  dL <- ttkframe(inner, padding = 16); tkpack(dL, side = "left", fill = "both", expand = TRUE)
  tkpack(ttklabel(dL, text = "1.  Choisir un modele ou saisir la matrice", font = "{Sans} 16 bold", foreground = COL_HEAD), anchor = "w")
  tkpack(ttklabel(dL, text = "Contexte pre-rempli :", font = "{Sans} 12", foreground = COL_SUB), anchor = "w", pady = c(12, 2))
  presetVar <- tclVar(names(PRESETS)[1])
  cbp <- ttkcombobox(dL, values = names(PRESETS), textvariable = presetVar, state = "readonly", width = 42); tkpack(cbp, anchor = "w")
  tkpack(ttklabel(dL, text = "Matrice de transition :", font = "{Sans} 13 bold", foreground = COL_INK), anchor = "w", pady = c(14, 2))
  tkpack(ttklabel(dL, text = "Formats acceptes (auto-detectes) :", font = "{Sans} 11", foreground = COL_SUB), anchor = "w")
  tkpack(ttklabel(dL, text = "  - DENSE : n lignes de n valeurs (matrice carree, sommes de lignes = 1 si normalise).", font = "{Sans} 11", foreground = COL_SUB), anchor = "w")
  tkpack(ttklabel(dL, text = "  - CREUX : triplets \"i j p\" par ligne (indices 0/1 acceptes, doublons sommes).", font = "{Sans} 11", foreground = COL_SUB), anchor = "w")
  mfr <- ttkframe(dL); tkpack(mfr, anchor = "w", fill = "both", expand = TRUE)
  matsc <- ttkscrollbar(mfr, orient = "vertical", command = function(...) tkyview(matTxt, ...))
  matxsc <- ttkscrollbar(mfr, orient = "horizontal", command = function(...) tkxview(matTxt, ...))
  matTxt <- tktext(mfr, width = 48, height = 13, font = "{Courier} 12", wrap = "none", bd = 1, relief = "solid", background = "white",
                   yscrollcommand = function(...) tkset(matsc, ...), xscrollcommand = function(...) tkset(matxsc, ...))
  tkgrid(matTxt, row = 0, column = 0, sticky = "nsew"); tkgrid(matsc, row = 0, column = 1, sticky = "ns"); tkgrid(matxsc, row = 1, column = 0, sticky = "ew")
  tkgrid.rowconfigure(mfr, 0, weight = 1); tkgrid.columnconfigure(mfr, 0, weight = 1)
  tkinsert(matTxt, "1.0", PRESETS[[1]]$m)
  tkpack(ttklabel(dL, text = "Separateurs : espace, tabulation, virgule ou point-virgule.  Decimal : \".\" ou \",\" (auto).",
                  font = "{Sans} 11", foreground = COL_SUB), anchor = "w", pady = c(3, 0))
  tkpack(ttklabel(dL, text = "EOL : LF / CRLF (Windows) / CR (Mac) - tous geres.  Pour un fichier .csv : utiliser \"Importer CSV...\".",
                  font = "{Sans} 11", foreground = COL_SUB), anchor = "w", pady = c(0, 0))
  tkpack(ttklabel(dL, text = "Libelles des etats (optionnel, un par ligne) :", font = "{Sans} 12", foreground = COL_SUB), anchor = "w", pady = c(12, 2))
  labTxt <- tktext(dL, width = 48, height = 6, font = "{Sans} 11", wrap = "none", bd = 1, relief = "solid", background = "white"); tkpack(labTxt, anchor = "w", fill = "both", expand = TRUE)
  tkinsert(labTxt, "1.0", PRESETS[[1]]$labels)

  tkpack(ttklabel(dR, text = "2.  Options", font = "{Sans} 16 bold", foreground = COL_HEAD), anchor = "w")
  normVar <- tclVar("1"); edgeVar <- tclVar("1"); showpVar <- tclVar("1"); fastVar <- tclVar("0")
  tkpack(ttkcheckbutton(dR, text = "Normaliser les lignes (somme = 1)", variable = normVar), anchor = "w", pady = c(12, 3))
  tkpack(ttkcheckbutton(dR, text = "Afficher les transitions (aretes)", variable = edgeVar), anchor = "w", pady = 3)
  tkpack(ttkcheckbutton(dR, text = "Afficher les probabilites", variable = showpVar), anchor = "w", pady = 3)
  tkpack(ttkcheckbutton(dR, text = "Mode rapide (approximations, grandes matrices)", variable = fastVar), anchor = "w", pady = 3)
  goBtn <- ttkbutton(dR, text = "Analyser", style = "Go.TButton", command = function() analyser()); tkpack(goBtn, anchor = "w", pady = c(18, 6), fill = "x")
  tkpack(ttklabel(dR, text = "3.  Fichier", font = "{Sans} 16 bold", foreground = COL_HEAD), anchor = "w", pady = c(16, 0))
  fbtn <- ttkframe(dR); tkpack(fbtn, anchor = "w", fill = "x", pady = c(8, 0))
  tkgrid(ttkbutton(fbtn, text = "Charger...", width = 17, command = function() charger()), row = 0, column = 0, padx = 2, pady = 3)
  tkgrid(ttkbutton(fbtn, text = "Importer CSV...", width = 17, command = function() importer_csv()), row = 0, column = 1, padx = 2, pady = 3)
  tkgrid(ttkbutton(fbtn, text = "Enregistrer...", width = 17, command = function() enregistrer()), row = 1, column = 0, padx = 2, pady = 3)
  tkgrid(ttkbutton(fbtn, text = "Export CSV...", width = 17, command = function() export_csv()), row = 1, column = 1, padx = 2, pady = 3)
  tkpack(ttklabel(dR, text = paste(
    "Conseils :",
    "  - Charger... : .txt avec matrice dense ou format \"i j p\".",
    "  - Importer CSV... : auto-detecte sep (, ; tab espace) et decimal.",
    "  - Mode rapide : recommande des n > 1500 (approxime spectre).",
    "  - n > 5000 : utiliser le format triplet (\"i j p\"). Le mode sparse-pur",
    "    s'active automatiquement -> jusqu'a n = 50 000.",
    "  - Onglet Graphe : les exports PNG du graphe (vue courante détaillée ou par classes) se font dans l'onglet Graphe.",
    sep = "\n"), font = "{Sans} 11", foreground = COL_SUB, justify = "left"), anchor = "w", pady = c(20, 0))

  # Placer le inner dans le canvas et configurer le scroll vertical
  cnv_win <- tcl(cnv, "create", "window", 0, 0, "-anchor", "nw", "-window", inner)
  tkbind(inner, "<Configure>", function() {
    bbox <- tcl(cnv, "bbox", "all")
    tcl(cnv, "configure", "-scrollregion", bbox)
  })
  # Optionnel : faire suivre la largeur du canvas
  tkbind(cnv, "<Configure>", function() {
    w <- as.integer(tclvalue(tkwinfo("width", cnv)))
    if (w > 10) tcl(inner, "configure", "-width", w)
  })

  tkpack(ys, side = "right", fill = "y")
  tkpack(cnv, side = "left", fill = "both", expand = TRUE)

  ##onglet Resume (tableau de bord)
  cardsF <- ttkframe(tabR, padding = 8); tkpack(cardsF, side = "top", fill = "x")
  for (cc in 0:3) tkgrid.columnconfigure(cardsF, cc, weight = 1)
  cv_n   <- add_card(cardsF, 0, 0, "Etats", COL_HEAD)
  cv_cl  <- add_card(cardsF, 0, 1, "Classes", COL_P2)
  cv_rec <- add_card(cardsF, 0, 2, "Recurrents", COL_NATURE[["Recurrente"]])
  cv_tra <- add_card(cardsF, 0, 3, "Transitoires", COL_NATURE[["Transitoire"]])
  cv_abs <- add_card(cardsF, 1, 0, "Absorbants", COL_NATURE[["Absorbant"]])
  cv_irr <- add_card(cardsF, 1, 1, "Irreductible", COL_HEAD)
  cv_ape <- add_card(cardsF, 1, 2, "Aperiodique", COL_P2)
  cv_mix <- add_card(cardsF, 1, 3, "2e val. propre", COL_P1)
  synF <- ttkframe(tabR, padding = c(12, 6)); tkpack(synF, side = "top", fill = "both", expand = TRUE)
  tkpack(ttklabel(synF, text = "Synthese", font = "{Sans} 14 bold", foreground = COL_HEAD), anchor = "w")
  synLbl <- ttklabel(synF, text = "", wraplength = 820, justify = "left", font = "{Sans} 13")
  tkpack(synLbl, anchor = "w", pady = 6)

  ##onglet Graphe
  leg <- ttkframe(tabG, padding = c(10, 6)); tkpack(leg, side = "top", fill = "x")
  tkpack(ttklabel(leg, text = "Nature :", font = "{Sans} 12 bold", foreground = COL_HEAD), side = "left", padx = c(0, 4))
  for (k in names(COL_NATURE)) {
    tkpack(tklabel(leg, text = "   ", background = COL_NATURE[[k]], relief = "solid", borderwidth = 1), side = "left")
    tkpack(ttklabel(leg, text = paste0(" ", k, " "), font = "{Sans} 12"), side = "left")
  }
  tkpack(ttklabel(leg, text = "    Mode :", font = "{Sans} 12 bold", foreground = COL_HEAD), side = "left", padx = c(8, 4))
  viewVar <- tclVar("auto")
  set_view <- function() gv$set_view(tclvalue(viewVar))
  tkpack(ttkradiobutton(leg, text = "Auto (LOD)", variable = viewVar, value = "auto", command = set_view), side = "left", padx = 2)
  tkpack(ttkradiobutton(leg, text = "Detail",     variable = viewVar, value = "nodes", command = set_view), side = "left", padx = 2)
  tkpack(ttkradiobutton(leg, text = "Classes",    variable = viewVar, value = "classes", command = set_view), side = "left", padx = 2)

  # Pack rightmost first for correct right alignment in the bar
  tkpack(ttkbutton(leg, text = "Export PNG (vue courante)", command = function() export_current_graph_view()), side = "right", padx = 4)
  kpiVar <- tclVar("")
  tkpack(ttklabel(leg, textvariable = kpiVar, font = "{Sans} 12 bold", foreground = COL_HEAD), side = "right", padx = 8)

  gv <- graph_viewer(tabG); tkpack(gv$frame, fill = "both", expand = TRUE)

  ##onglet Classification
  r2 <- ttkframe(tabC, padding = 6); tkpack(r2, side = "right", fill = "both")
  l2 <- ttkframe(tabC, padding = 6); tkpack(l2, side = "left", fill = "both", expand = TRUE)
  tkpack(ttklabel(l2, text = "Resultats par etat", font = "{Sans} 13 bold", foreground = COL_HEAD), anchor = "w")
  stTree <- make_tree(l2, c("e", "c", "n", "p", "pc"), c("Etat", "Classe", "Nature", "Periode", "Periodicite"),
                      c(190, 60, 110, 70, 110), anchors = c("w", "c", "c", "c", "c"), hscroll = TRUE, height = 20)
  tkpack(stTree$frame, fill = "both", expand = TRUE)
  tkpack(ttklabel(r2, text = "Classes de communication", font = "{Sans} 13 bold", foreground = COL_HEAD), anchor = "w")
  clTree <- make_tree(r2, c("c", "e", "t", "n"), c("Cl.", "Etats", "Taille", "Nature"),
                      c(40, 200, 60, 110), anchors = c("c", "w", "c", "c"), hscroll = TRUE, height = 11)
  tkpack(clTree$frame, fill = "both", expand = TRUE)
  interpLbl <- ttklabel(r2, text = "", wraplength = 400, justify = "left", font = "{Sans} 12"); tkpack(interpLbl, anchor = "w", pady = 8)

  ##onglet Matrice P / P^k
  mctrl <- ttkframe(tabM, padding = c(8, 6)); tkpack(mctrl, side = "top", fill = "x")
  mviewVar <- tclVar("P"); kVar <- tclVar("2")
  tkpack(ttklabel(mctrl, text = "Afficher :", font = "{Sans} 12"), side = "left")
  tkpack(ttkradiobutton(mctrl, text = "P (1 pas)", variable = mviewVar, value = "P", command = function() show_matrix()), side = "left", padx = 4)
  tkpack(ttkradiobutton(mctrl, text = "P^k (k pas)", variable = mviewVar, value = "Pk", command = function() show_matrix()), side = "left", padx = 4)
  tkpack(ttkradiobutton(mctrl, text = "P reorganisee (par classe)", variable = mviewVar, value = "Pord", command = function() show_matrix()), side = "left", padx = 4)
  tkpack(ttklabel(mctrl, text = "k =", font = "{Sans} 12"), side = "left", padx = c(8, 2))
  tkpack(ttkentry(mctrl, textvariable = kVar, width = 5), side = "left")
  tkpack(ttkbutton(mctrl, text = "Calculer", command = function() show_matrix()), side = "left", padx = 6)
  tkpack(ttklabel(mctrl, text = "(cellules nulles laissees vides)", font = "{Sans} 11", foreground = COL_SUB), side = "left", padx = 8)
  matHost <- ttkframe(tabM, padding = 6); tkpack(matHost, fill = "both", expand = TRUE)

  ##onglet Stationnaire & absorption
  r3 <- ttkframe(tabS, padding = 6); tkpack(r3, side = "right", fill = "both", expand = TRUE)
  l3 <- ttkframe(tabS, padding = 6); tkpack(l3, side = "left", fill = "both")
  tkpack(ttklabel(l3, text = "Distribution stationnaire & temps de retour", font = "{Sans} 13 bold", foreground = COL_HEAD), anchor = "w")
  statTree <- make_tree(l3, c("e", "pi", "mr"), c("Etat", "Proba pi", "Temps retour"),
                        c(170, 95, 100), anchors = c("w", "c", "c"), hscroll = TRUE, height = 22)
  tkpack(statTree$frame, fill = "both", expand = TRUE)
  tkpack(ttklabel(l3, text = "pi normalisee par classe recurrente ; m(i)=1/pi(i).", font = "{Sans} 11", foreground = COL_SUB, wraplength = 340, justify = "left"), anchor = "w", pady = 3)
  tkpack(ttklabel(r3, text = "Analyse d'absorption (etats transitoires)", font = "{Sans} 13 bold", foreground = COL_HEAD), anchor = "w")
  absHost <- ttkframe(r3); tkpack(absHost, fill = "both", expand = TRUE)
  absNote <- ttklabel(r3, text = "", wraplength = 560, justify = "left", font = "{Sans} 12"); tkpack(absNote, anchor = "w", pady = 6)

  ##onglet Prevision
  pctrl <- ttkframe(tabP, padding = 8); tkpack(pctrl, side = "top", fill = "x")
  startVar <- tclVar(""); horizonVar <- tclVar("12"); unitVar <- tclVar("mois")
  tkpack(ttklabel(pctrl, text = "Etat initial :", font = "{Sans} 12"), side = "left", padx = 2)
  startCb <- ttkcombobox(pctrl, textvariable = startVar, state = "readonly", width = 22); tkpack(startCb, side = "left", padx = 2)
  tkpack(ttklabel(pctrl, text = "Horizon :", font = "{Sans} 12"), side = "left", padx = c(8, 2))
  tkpack(ttkentry(pctrl, textvariable = horizonVar, width = 6), side = "left", padx = 2)
  tkpack(ttkradiobutton(pctrl, text = "Mensuel", variable = unitVar, value = "mois",   command = function() previsionner()), side = "left", padx = 4)
  tkpack(ttkradiobutton(pctrl, text = "Annuel",  variable = unitVar, value = "annees", command = function() previsionner()), side = "left", padx = 4)
  tkpack(ttkbutton(pctrl, text = "Prevoir", style = "Go.TButton", command = function() previsionner()), side = "left", padx = 8)
  tkpack(ttkbutton(pctrl, text = "Exporter PNG...", command = function() export_forecast_png()), side = "left", padx = 4)
  pr <- ttkframe(tabP, padding = 6); tkpack(pr, side = "right", fill = "y")
  tkpack(ttklabel(pr, text = "Distribution (couleur = courbe)", font = "{Sans} 13 bold", foreground = COL_HEAD), anchor = "w")
  foreTree <- make_tree(pr, c("e", "t0", "fin", "tend"), c("Etat", "t=0", "final", "Tendance"),
                        c(150, 70, 70, 80), anchors = c("w", "c", "c", "c"), hscroll = TRUE, height = 22)
  tkpack(foreTree$frame, fill = "both", expand = TRUE)
  pl <- ttkframe(tabP); tkpack(pl, side = "left", fill = "both", expand = TRUE)
  fv <- image_viewer(pl); tkpack(fv$frame, fill = "both", expand = TRUE)

  setstatus <- function(txt, col) { tclvalue(statusVar) <- txt; tkconfigure(statusLbl, foreground = col) }

  #logique : matrice P / P^k
  show_matrix <- function() {
    if (is.null(st$model)) return(invisible())
    r <- st$model$res; labs <- st$model$labels
    perm <- seq_len(r$n)
    # === Mode sparse-pur : pas de matrice dense, heatmap directe depuis triplets
    if (isTRUE(r$sparse_pure)) {
      sp_view <- r$sp; titre <- "P (vue heatmap creuse, mode sparse-pur)"
      if (tclvalue(mviewVar) == "Pord") {
        reo <- reorganize_by_class(r); sp_view <- reo$sp; perm <- reo$order
        titre <- "P reorganisee par classe (creux)"
      } else if (tclvalue(mviewVar) == "Pk") {
        .clear_children(matHost)
        tkpack(ttklabel(matHost, text = paste0("Mode sparse-pur (n=", r$n, ") : P^k necessiterait O(n^2) memoire et n'est pas calcule."),
                        foreground = COL_NATURE[["Transitoire"]], font = "{Sans} 12"), anchor = "w")
        return(invisible())
      }
      .clear_children(matHost)
      tkpack(ttklabel(matHost, text = paste0("Matrice ", titre), font = "{Sans} 12 bold", foreground = COL_HEAD), anchor = "w")
      tkpack(ttklabel(matHost, text = sprintf("n=%d, %d arcs (densite %.4f%%) - heatmap downsamplee", r$n, length(sp_view$iv), r$density * 100),
                      font = "{Sans} 11", foreground = COL_SUB), anchor = "w", pady = c(0, 4))
      hm <- sp_to_heatmap(sp_view, r$n, max_px = 1200L)
      tf <- tempfile(fileext = ".png")
      grDevices::png(tf, width = 900, height = 900, res = 96)
      par(mar = c(3.2, 3.2, 1, 1), bg = "white")
      image(seq_len(hm$nb), seq_len(hm$nb), t(hm$H[hm$nb:1, , drop = FALSE]),
            col = c("white", hcl.colors(63, "Blues 3", rev = TRUE)),
            zlim = c(0, max(hm$H)), xlab = "Etat destination j", ylab = "Etat source i",
            cex.axis = 0.85, cex.lab = 0.95)
      grDevices::dev.off()
      cvm <- tkcanvas(matHost, background = "white", highlightthickness = 0); tkpack(cvm, fill = "both", expand = TRUE)
      img <- tkimage.create("photo", file = tf); tkcreate(cvm, "image", 0, 0, anchor = "nw", image = img)
      return(invisible())
    }
    if (tclvalue(mviewVar) == "Pk") {
      k <- suppressWarnings(as.integer(tclvalue(kVar))); if (is.na(k) || k < 1) k <- 1
      M <- matrix_power(r$P, k); titre <- sprintf("P^%d", k)
    } else if (tclvalue(mviewVar) == "Pord") {
      reo <- reorganize_by_class(r); M <- reo$P; perm <- reo$order
      titre <- "P reorganisee par classe (forme triangulaire par blocs)"
    } else { M <- r$P; titre <- "P" }
    .clear_children(matHost); n <- r$n
    tkpack(ttklabel(matHost, text = paste0("Matrice ", titre),
                    font = "{Sans} 12 bold", foreground = COL_HEAD), anchor = "w")
    # n grand : Treeview avec n^2 cellules inutilisable -> heatmap PNG.
    # Pour n tres grand (>1500), on downsample par moyennage de blocs pour
    # garder le PNG raisonnable et lisible (sinon 10000x10000 px serait inutile).
    if (n > 200L) {
      Mview <- M; tag_ds <- ""
      MAX_PX <- 1200L
      if (n > MAX_PX) {
        bs <- ceiling(n / MAX_PX)         # taille de bloc
        nb <- ceiling(n / bs)              # nb de blocs
        # padding par 0 pour multiplication exacte
        pad <- matrix(0, nb * bs, nb * bs); pad[seq_len(n), seq_len(n)] <- M
        # moyenne par bloc : 2 reshapes + rowSums
        a <- array(pad, dim = c(bs, nb, bs, nb))
        Mview <- apply(a, c(2, 4), mean)
        tag_ds <- sprintf(" (downsamplee %dx%d -> %dx%d)", n, n, nb, nb)
      }
      tkpack(ttklabel(matHost, text = sprintf(
        "n=%d : heatmap (intensite = probabilite)%s. Tableau exact desactive au-dela de 200 etats.",
        n, tag_ds),
        font = "{Sans} 11", foreground = COL_SUB), anchor = "w", pady = c(0, 4))
      tf <- tempfile(fileext = ".png")
      grDevices::png(tf, width = 900, height = 900, res = 96)
      par(mar = c(3.2, 3.2, 1, 1), bg = "white")
      nv <- nrow(Mview)
      image(seq_len(nv), seq_len(nv), t(Mview[nv:1, , drop = FALSE]),
            col = c("white", hcl.colors(63, "Blues 3", rev = TRUE)),
            zlim = c(0, max(Mview)), xlab = "Etat destination j", ylab = "Etat source i",
            cex.axis = 0.85, cex.lab = 0.95)
      grDevices::dev.off()
      cvm <- tkcanvas(matHost, background = "white", highlightthickness = 0)
      tkpack(cvm, fill = "both", expand = TRUE)
      img <- tkimage.create("photo", file = tf)
      tkcreate(cvm, "image", 0, 0, anchor = "nw", image = img)
      return(invisible())
    }
    cols <- c("e", paste0("c", seq_len(n))); headers <- c("Etat", as.character(perm - 1L))
    tr <- make_tree(matHost, cols, headers, c(150, rep(58, n)), anchors = c("w", rep("center", n)), hscroll = TRUE, height = 18)
    tkpack(tr$frame, fill = "both", expand = TRUE)
    for (i in seq_len(n)) {
      vals <- ifelse(M[i, ] < 1e-6, "", sprintf("%.3f", M[i, ]))
      orig <- perm[i]
      .row(tr$tv, c(paste0(orig - 1L, " - ", labs[orig]), vals), .tag_nat(r$nature_of[orig]))
    }
  }

  # Prevision : iteration creuse v %*% P, avec 12 sous-pas par increment en
  # mode annuel (evite de materialiser P^12 dense pour les grandes matrices).
  .forecast_compute <- function() {
    r <- st$model$res; labs <- st$model$labels
    choices <- paste0(0:(r$n - 1), " - ", labs)
    s <- match(tclvalue(startVar), choices); if (is.na(s)) s <- 1
    h <- suppressWarnings(as.integer(tclvalue(horizonVar))); if (is.na(h) || h < 1) h <- 12
    mu0 <- rep(0, r$n); mu0[s] <- 1
    sub <- if (tclvalue(unitVar) == "annees") 12L else 1L
    list(M = forecast_markov(r$sp, mu0, h, substeps = sub),
         pistar = if (length(r$classes) == 1L && r$nature[1] != "Transitoire") r$pi else NULL,
         labs = labs, r = r)
  }
  #logique : prevision
  previsionner <- function() {
    if (is.null(st$model)) return(invisible())
    fc <- .forecast_compute(); r <- fc$r; labs <- fc$labs; M <- fc$M
    fv$set(function() draw_forecast_plot(M, labs, tclvalue(unitVar), fc$pistar), 1040, 600)
    pal <- forecast_palette(r$n); .clear_tree(foreTree$tv)
    # cap : top par amplitude (etats qui evoluent le plus)
    TBL_CAP <- 1000L
    idx_fc <- if (r$n > TBL_CAP) order(abs(M[nrow(M), ] - M[1L, ]), decreasing = TRUE)[seq_len(TBL_CAP)] else seq_len(r$n)
    for (i in idx_fc) tcl(foreTree$tv, "tag", "configure", paste0("f", i), "-background", .tint(pal[i], 0.80))
    for (i in idx_fc) {
      d <- M[nrow(M), i] - M[1, i]
      tend <- if (abs(d) < 1e-4) "=" else if (d > 0) "hausse" else "baisse"
      .row(foreTree$tv, c(paste0(i - 1, " - ", labs[i]), sprintf("%.3f", M[1, i]), sprintf("%.3f", M[nrow(M), i]), tend), paste0("f", i))
    }
    if (r$n > TBL_CAP)
      .row(foreTree$tv, c(sprintf("... (top %d / %d)", TBL_CAP, r$n), "", "", ""), "")
  }

  #logique : analyse complete
  analyser <- function(goResume = TRUE) {
    prog_show("Lecture & normalisation de la matrice...", value = 5)
    on.exit(prog_hide(), add = TRUE)
    res_try <- tryCatch({
      M <- parse_matrix(tclvalue(tkget(matTxt, "1.0", "end-1c")))
      prog_show("Normalisation des lignes...", value = 15)
      if (tclvalue(normVar) == "1") M <- normalize_rows(M)
      else if (!inherits(M, "markov_sparse_input") && any(abs(rowSums(M) - 1) > 1e-8))
        stop("Les lignes ne somment pas a 1 (cochez Normaliser).")
      n <- if (inherits(M, "markov_sparse_input")) M$n else nrow(M)
      labs <- strsplit(tclvalue(tkget(labTxt, "1.0", "end-1c")), "\n", fixed = TRUE)[[1]]
      labs <- trimws(labs); labs <- labs[nzchar(labs)]
      if (length(labs) == 0L)      labs <- paste0("S", 0:(n - 1))
      else if (length(labs) < n)   labs <- c(labs, paste0("S", seq.int(length(labs), n - 1L)))
      else if (length(labs) > n)   labs <- labs[seq_len(n)]
      prog_show(sprintf("SCC + periodicite + stationnaires (n=%d)...", n), value = 35)
      list(res = analyse_markov(M, opts = list(fast = tclvalue(fastVar) == "1")), labels = labs)
    }, error = function(e) e)
    if (inherits(res_try, "error")) {
      setstatus(paste("Erreur :", conditionMessage(res_try)), COL_NATURE[["Absorbant"]])
      tkmessageBox(title = "Markov Studio - saisie invalide", message = conditionMessage(res_try), icon = "error", type = "ok")
      return(invisible())
    }
    st$model <- res_try; r <- res_try$res; labs <- res_try$labels
    tryCatch({
    prog_show("Analyse d'absorption (Gauss-Seidel)...", value = 60)
    st$abs <- absorption_analysis(r)
    prog_show("Calcul du spectre (eigen / power iter)...", value = 75)
    st$spec <- spectral_metrics(r)
    prog_show("Rendu interface (tableaux, graphe, heatmap)...", value = 90)
    setstatus(sprintf("Analyse OK : %d etats, %d classe(s), %d transitoire(s).", r$n, length(r$classes), sum(r$nature_of == "Transitoire")), COL_NATURE[["Recurrente"]])

    nat <- table(factor(r$nature_of, levels = names(COL_NATURE)))
    irr <- if (length(r$classes) == 1) "Oui" else "Non"
    aper <- if (all(r$period[r$nature_of %in% c("Recurrente", "Absorbant")] == 1)) "Oui" else "Non"
    tclvalue(cv_n) <- r$n; tclvalue(cv_cl) <- length(r$classes); tclvalue(cv_rec) <- nat["Recurrente"]
    tclvalue(cv_tra) <- nat["Transitoire"]; tclvalue(cv_abs) <- nat["Absorbant"]
    tclvalue(cv_irr) <- irr; tclvalue(cv_ape) <- aper
    tclvalue(cv_mix) <- if (is.na(st$spec$slem)) "-" else sprintf("%.3f", st$spec$slem)
    tclvalue(kpiVar) <- sprintf("Etats %d  |  Classes %d  |  Rec %d  |  Trans %d  |  Abs %d  |  Irreductible %s", r$n, length(r$classes), nat["Recurrente"], nat["Transitoire"], nat["Absorbant"], irr)

    syn <- c(
      if (irr == "Oui") "La chaine est IRREDUCTIBLE : tous les etats communiquent et partagent le meme comportement asymptotique."
      else sprintf("La chaine est REDUCTIBLE : %d classes de communication.", length(r$classes)),
      if (nat["Absorbant"] > 0) sprintf("%d etat(s) absorbant(s) : une fois atteint, le systeme y reste indefiniment.", nat["Absorbant"]),
      if (nat["Transitoire"] > 0) sprintf("%d etat(s) transitoire(s) : quittes definitivement a terme (voir onglet absorption).", nat["Transitoire"]),
      if (sum(r$nature == "Recurrente") > 0) sprintf("%d classe(s) recurrente(s) fermee(s) : zones de stabilite a long terme.", sum(r$nature == "Recurrente")),
      sprintf("Periodicite : chaine %s.", if (aper == "Oui") "aperiodique (convergence vers le regime stationnaire)" else "periodique (oscillations persistantes)"),
      if (!is.na(st$spec$slem)) sprintf("Vitesse de melange : 2e valeur propre |lambda2| = %.3f (proche de 1 = convergence lente).", st$spec$slem),
      if (!is.na(st$spec$kemeny)) sprintf("Constante de Kemeny = %.2f (temps moyen pour atteindre un etat tire selon pi).", st$spec$kemeny),
      sprintf("Representation creuse : %d arcs non-nuls sur %d (densite %.2f%%)%s.",
              r$sp$nnz, r$n * r$n, r$density * 100,
              if (isTRUE(r$fast)) " - mode rapide actif (iterations limitees, spectre approche)" else ""))
    tkconfigure(synLbl, text = paste(syn, collapse = "\n\n"))

    sp <- tclvalue(showpVar) == "1"; ed <- tclvalue(edgeVar) == "1"
    gv$set_data(r, labs, ed, sp)

    # n grand : limiter les insertions Treeview a TBL_CAP lignes (sinon
    # > 30s d'overhead Tk pour rien). Tri par classe puis indice : on garde
    # un echantillon coherent par classe.
    TBL_CAP <- 1000L
    .clear_tree(stTree$tv)
    idx_show <- if (r$n > TBL_CAP) order(r$class_of, seq_len(r$n))[seq_len(TBL_CAP)] else seq_len(r$n)
    for (i in idx_show) {
      per <- if (r$period[i] == 0) "0" else as.character(r$period[i])
      pc <- if (r$period[i] == 0) "-" else if (r$period[i] == 1) "Aperiodique" else paste0("Periode ", r$period[i])
      .row(stTree$tv, c(paste0(i - 1, " - ", labs[i]), r$class_of[i], r$nature_of[i], per, pc), .tag_nat(r$nature_of[i]))
    }
    if (r$n > TBL_CAP)
      .row(stTree$tv, c(sprintf("... (%d / %d affiches)", TBL_CAP, r$n), "", "", "", ""), "")
    .clear_tree(clTree$tv)
    for (k in seq_along(r$classes)) {
      et <- paste0("{", paste(r$classes[[k]] - 1, collapse = ", "), "}")
      .row(clTree$tv, c(k, et, length(r$classes[[k]]), r$nature[k]), .tag_nat(r$nature[k]))
    }
    abs_n <- nat["Absorbant"]; rec_n <- sum(r$nature == "Recurrente")
    tkconfigure(interpLbl, text = paste(c(
      if (irr == "Oui") "- Chaine irreductible." else sprintf("- Chaine reductible en %d classes.", length(r$classes)),
      if (abs_n > 0) sprintf("- %d etat(s) absorbant(s).", abs_n),
      if (rec_n > 0) sprintf("- %d classe(s) recurrente(s) fermee(s).", rec_n),
      "- Les etats transitoires sont quittes a terme."), collapse = "\n"))

    .clear_tree(statTree$tv)
    # cap : top par pi decroissant pour montrer les etats dominants en regime
    idx_stat <- if (r$n > TBL_CAP) {
      pi_for_sort <- ifelse(is.na(r$pi), -Inf, r$pi)
      order(pi_for_sort, decreasing = TRUE)[seq_len(TBL_CAP)]
    } else seq_len(r$n)
    for (i in idx_stat) {
      ps <- if (is.na(r$pi[i])) "-" else sprintf("%.4f", r$pi[i])
      mr <- if (is.infinite(r$m_return[i])) "Infini" else sprintf("%.3f", r$m_return[i])
      .row(statTree$tv, c(paste0(i - 1, " - ", labs[i]), ps, mr), .tag_nat(r$nature_of[i]))
    }
    if (r$n > TBL_CAP)
      .row(statTree$tv, c(sprintf("... (top %d par pi sur %d)", TBL_CAP, r$n), "", ""), "")
    update_absorption(r, labs)
    tclvalue(mviewVar) <- "P"; show_matrix()
    choices <- paste0(0:(r$n - 1), " - ", labs)
    tkconfigure(startCb, values = choices); tclvalue(startVar) <- choices[1]
    previsionner()
    if (goResume) tcl(nb, "select", tabR)
    }, error = function(e) {
      setstatus(paste("Erreur d'affichage :", conditionMessage(e)), COL_NATURE[["Absorbant"]])
      tkmessageBox(title = "Markov Studio", message = paste("Erreur lors de l'affichage :", conditionMessage(e)), icon = "error", type = "ok")
    })
  }

  update_absorption <- function(r, labs) {
    .clear_children(absHost); a <- st$abs
    if (!isTRUE(a$ok)) { tkconfigure(absNote, text = a$msg); return(invisible()) }
    recnames <- vapply(a$rec, function(c) paste0("Cl.", c, " {", paste(r$classes[[c]] - 1, collapse = ","), "} ", r$nature[c]), character(1))
    cols <- c("e", "t", paste0("b", seq_along(a$rec)))
    headers <- c("Etat transitoire", "E[etapes]", paste0("P->", a$rec))
    tr <- make_tree(absHost, cols, headers, c(160, 90, rep(90, length(a$rec))),
                    anchors = c("w", "c", rep("c", length(a$rec))), hscroll = TRUE, height = 16)
    tkpack(tr$frame, fill = "both", expand = TRUE)
    for (ii in seq_along(a$T)) {
      i <- a$T[ii]
      .row(tr$tv, c(paste0(i - 1, " - ", labs[i]), sprintf("%.2f", a$t[ii]), sprintf("%.3f", a$B[ii, ])), "tra")
    }
    tkconfigure(absNote, text = paste0("Colonnes P->c : probabilite d'etre absorbe dans la classe recurrente c. Classes cibles : ",
                                       paste(recnames, collapse = " ; "), ".\nE[etapes] : nombre moyen de pas avant absorption (matrice fondamentale N=(I-Q)^-1)."))
  }

  # import / export
  # Import CSV "intelligent" : auto-detection du separateur, du decimal,
  # des en-tetes de ligne/colonne et du BOM. Accepte virgule, point-virgule,
  # tabulation ou espace comme separateur ; "." ou "," comme decimal.
  importer_csv <- function() {
    f <- tclvalue(tkgetOpenFile(filetypes = "{{CSV/TSV} {.csv .tsv .txt}} {{Tous} *}"))
    if (!nzchar(f)) return(invisible())
    # Lit le fichier en binaire pour gerer BOM + tout encodage
    raw <- tryCatch({
      bytes <- readBin(f, "raw", n = file.info(f)$size)
      iconv(rawToChar(bytes), from = "", to = "UTF-8", sub = "")
    }, error = function(e) NULL)
    if (is.null(raw) || !nzchar(raw)) {
      setstatus("Lecture du CSV impossible.", COL_NATURE[["Absorbant"]]); return(invisible())
    }
    # Strip BOM UTF-8 (EF BB BF) si present
    raw <- sub("^﻿", "", raw)
    raw <- gsub("\r\n", "\n", raw, fixed = TRUE); raw <- gsub("\r", "\n", raw, fixed = TRUE)
    lines <- strsplit(raw, "\n", fixed = TRUE)[[1]]
    lines <- lines[nzchar(trimws(lines))]
    if (!length(lines)) { setstatus("CSV vide.", COL_NATURE[["Absorbant"]]); return(invisible()) }

    # Strategie : on essaie toutes les combinaisons (sep, dec) plausibles et on
    # garde la 1ere qui produit une matrice carree numerique. Beaucoup plus
    # robuste que de deviner le separateur quand virgules-decimal et
    # points-virgules-separateur coexistent ("0,5;0,3" -> 4 virgules, 2 ;).
    tries <- list(
      list(sep = ";",  dec = ",", name = ";"),       # FR standard
      list(sep = "\t", dec = ".", name = "tab"),     # TSV
      list(sep = "\t", dec = ",", name = "tab"),     # TSV FR
      list(sep = ",",  dec = ".", name = ","),       # US standard
      list(sep = ";",  dec = ".", name = ";"),       # CSV ;-separe + . decimal
      list(sep = "",   dec = ".", name = "espace"),  # white-space sep
      list(sep = "",   dec = ",", name = "espace")   # white-space + virgule decimal
    )
    best <- NULL; has_header <- FALSE
    for (tr in tries) {
      for (hdr in c(FALSE, TRUE)) {
        df_try <- tryCatch(read.table(text = raw, header = hdr, sep = tr$sep, dec = tr$dec,
                                      comment.char = "", check.names = FALSE,
                                      stringsAsFactors = FALSE, fill = TRUE),
                           error = function(e) NULL)
        if (is.null(df_try)) next
        is_num <- vapply(df_try, is.numeric, logical(1))
        # drop 1ere col texte (label de ligne) si presente seule
        if (sum(!is_num) == 1L && !is_num[1L]) {
          df_try <- df_try[, -1L, drop = FALSE]
          is_num <- vapply(df_try, is.numeric, logical(1))
        }
        if (length(is_num) > 0L && all(is_num) && nrow(df_try) == ncol(df_try) &&
            nrow(df_try) >= 2L && !any(is.na(df_try))) {
          best <- list(df = df_try, sep = tr$name, dec = tr$dec); has_header <- hdr; break
        }
      }
      if (!is.null(best)) break
    }
    if (is.null(best)) {
      setstatus("CSV illisible : impossible de detecter un format carre numerique.",
                COL_NATURE[["Absorbant"]]); return(invisible())
    }
    df <- best$df; sep_name <- best$sep; dec <- best$dec
    M <- as.matrix(df); storage.mode(M) <- "numeric"
    if (any(is.na(M))) {
      setstatus("CSV contient des valeurs manquantes (NA).", COL_NATURE[["Absorbant"]]); return(invisible())
    }
    # Push dans matTxt en format dense compact
    txt <- paste(apply(M, 1L, function(row) paste(sprintf("%.6f", row), collapse = " ")), collapse = "\n")
    tkdelete(matTxt, "1.0", "end"); tkinsert(matTxt, "1.0", txt)
    tkdelete(labTxt, "1.0", "end")
    # Si en-tete : utiliser comme labels
    if (has_header) {
      hdr <- names(df)
      if (length(hdr) == nrow(M)) tkinsert(labTxt, "1.0", paste(hdr, collapse = "\n"))
    }
    setstatus(sprintf("CSV importe : %dx%d  (sep='%s', dec='%s'%s)",
                      nrow(M), ncol(M), sep_name, dec,
                      if (has_header) ", en-tete detectee" else ""),
              COL_NATURE[["Recurrente"]])
    analyser()
  }

  charger <- function() {
    f <- tclvalue(tkgetOpenFile(filetypes = "{{Texte/CSV} {.txt .csv .dat}} {{Tous} *}"))
    if (!nzchar(f)) return(invisible())
    # Lecture binaire + normalisation des fins de ligne (CR, CRLF, LF tous geres).
    txt <- tryCatch({
      raw <- readChar(f, file.info(f)$size, useBytes = TRUE)
      raw <- gsub("\r\n", "\n", raw, fixed = TRUE)
      gsub("\r", "\n", raw, fixed = TRUE)
    }, error = function(e) NULL)
    if (is.null(txt)) { setstatus("Lecture du fichier impossible.", COL_NATURE[["Absorbant"]]); return(invisible()) }
    tkdelete(matTxt, "1.0", "end"); tkinsert(matTxt, "1.0", txt)
    tkdelete(labTxt, "1.0", "end"); analyser()
  }
  enregistrer <- function() {
    f <- tclvalue(tkgetSaveFile(defaultextension = ".txt", filetypes = "{{Texte} {.txt}} {{Tous} *}"))
    if (!nzchar(f)) return(invisible())
    writeLines(strsplit(tclvalue(tkget(matTxt, "1.0", "end-1c")), "\n")[[1]], f)
    setstatus(paste("Matrice enregistree :", f), COL_NATURE[["Recurrente"]])
  }
  export_csv <- function() {
    if (is.null(st$model)) { setstatus("Analysez d'abord une matrice.", COL_NATURE[["Transitoire"]]); return(invisible()) }
    f <- tclvalue(tkgetSaveFile(defaultextension = ".csv", filetypes = "{{CSV} {.csv}} {{Tous} *}"))
    if (!nzchar(f)) return(invisible())
    r <- st$model$res; labs <- st$model$labels
    df <- data.frame(Etat = 0:(r$n - 1), Libelle = labs, Classe = r$class_of, Nature = r$nature_of,
                     Periode = r$period, Proba_stationnaire = r$pi, Temps_retour = r$m_return, check.names = FALSE)
    tryCatch({ write.csv(df, f, row.names = FALSE); setstatus(paste("Resultats exportes :", f), COL_NATURE[["Recurrente"]]) },
             error = function(e) setstatus(paste("Echec export :", conditionMessage(e)), COL_NATURE[["Absorbant"]]))
  }
  export_png <- function() {
    if (is.null(st$model)) { setstatus("Analysez d'abord une matrice.", COL_NATURE[["Transitoire"]]); return(invisible()) }
    f <- tclvalue(tkgetSaveFile(defaultextension = ".png", filetypes = "{{Image PNG} {.png}} {{Tous} *}"))
    if (!nzchar(f)) return(invisible())
    r <- st$model$res; labs <- st$model$labels; g <- graph_geometry(r)
    sz <- max(1200, min(3200, 32 * r$n + 700)); band <- round(sz * 0.11)   # bande titre + legende
    nat <- table(factor(r$nature_of, levels = names(COL_NATURE)))
    tryCatch({ grDevices::png(f, width = sz, height = sz + band, res = 110)
      layout(matrix(c(1, 2), 2, 1), heights = c(band, sz))
      par(mar = c(0, 0, 0, 0), bg = "white")           # bandeau : titre + legende
      plot(NA, xlim = c(0, 1), ylim = c(0, 1), axes = FALSE, xlab = "", ylab = "", xaxs = "i", yaxs = "i")
      text(0.5, 0.74, "Classification des etats d'une chaine de Markov", font = 2, cex = 1.7, col = COL_HEAD)
      cnt <- c(nat[["Recurrente"]], nat[["Transitoire"]], nat[["Absorbant"]]); nm <- names(COL_NATURE)
      lx <- c(0.26, 0.46, 0.68)
      for (k in 1:3) {
        points(lx[k], 0.30, pch = 21, bg = COL_NATURE[[k]], col = "white", cex = 3, lwd = 2)
        text(lx[k] + 0.018, 0.30, sprintf("%s (%d)", nm[k], cnt[k]), adj = c(0, 0.5), cex = 1.15, font = 2, col = COL_INK)
      }
      draw_graph(r, labs, g, c(-g$lim, g$lim), c(-g$lim, g$lim), sz, tclvalue(edgeVar) == "1", tclvalue(showpVar) == "1")
      grDevices::dev.off()
      setstatus(paste("Graphe + legende exportes :", f), COL_NATURE[["Recurrente"]]) },
      error = function(e) setstatus(paste("Echec export :", conditionMessage(e)), COL_NATURE[["Absorbant"]]))
  }

  # Nouvelle fonction : export de la vue agrégée par classes (respecte la logique de draw_graph_classes + class_geometry)
  export_graph_classes_png <- function() {
    if (is.null(st$model)) { setstatus("Analysez d'abord une matrice.", COL_NATURE[["Transitoire"]]); return(invisible()) }
    f <- tclvalue(tkgetSaveFile(defaultextension = ".png", filetypes = "{{Image PNG} {.png}} {{Tous} *}"))
    if (!nzchar(f)) return(invisible())
    r <- st$model$res; labs <- st$model$labels
    geom_c <- class_geometry(r)
    K <- geom_c$K
    # Taille raisonnable pour la vue classes (K petit en pratique)
    sz <- max(900, min(2400, 180 * max(K, 3) + 500))
    band <- round(sz * 0.11)
    nat <- table(factor(r$nature_of, levels = names(COL_NATURE)))
    tryCatch({ grDevices::png(f, width = sz, height = sz + band, res = 110)
      layout(matrix(c(1, 2), 2, 1), heights = c(band, sz))
      par(mar = c(0, 0, 0, 0), bg = "white")           # bandeau : titre + legende
      plot(NA, xlim = c(0, 1), ylim = c(0, 1), axes = FALSE, xlab = "", ylab = "", xaxs = "i", yaxs = "i")
      text(0.5, 0.74, "Vue par classes de communication", font = 2, cex = 1.7, col = COL_HEAD)
      cnt <- c(nat[["Recurrente"]], nat[["Transitoire"]], nat[["Absorbant"]]); nm <- names(COL_NATURE)
      lx <- c(0.26, 0.46, 0.68)
      for (k in 1:3) {
        points(lx[k], 0.30, pch = 21, bg = COL_NATURE[[k]], col = "white", cex = 3, lwd = 2)
        text(lx[k] + 0.018, 0.30, sprintf("%s (%d)", nm[k], cnt[k]), adj = c(0, 0.5), cex = 1.15, font = 2, col = COL_INK)
      }
      # Toujours afficher les flux inter-classes (comme dans la vue interactive "Classes")
      draw_graph_classes(r, geom_c, c(-geom_c$lim, geom_c$lim), c(-geom_c$lim, geom_c$lim), sz, TRUE)
      grDevices::dev.off()
      setstatus(paste("Vue par classes exportee :", f), COL_NATURE[["Recurrente"]]) },
      error = function(e) setstatus(paste("Echec export :", conditionMessage(e)), COL_NATURE[["Absorbant"]]))
  }

  # Export de la vue courante de l'onglet Graphe (respecte le mode choisi : Detail ou Classes,
  # ainsi que les toggles edges/showp stockés dans le viewer).
  # C'est maintenant le point d'entrée unique pour les exports PNG du graphe (tous dans l'onglet Graphe).
  export_current_graph_view <- function() {
    if (is.null(st$model) || is.null(gv$res)) {
      setstatus("Analysez d'abord une matrice et consultez l'onglet Graphe.", COL_NATURE[["Transitoire"]])
      return(invisible())
    }
    f <- tclvalue(tkgetSaveFile(defaultextension = ".png", filetypes = "{{Image PNG} {.png}} {{Tous} *}"))
    if (!nzchar(f)) return(invisible())

    r <- gv$res
    labs <- gv$labels
    edges <- gv$edges
    showp <- gv$showp

    # Résolution du mode exactement comme dans le viewer (render)
    mode <- gv$view_mode
    if (mode == "auto") {
      mode <- if (gv$z <= gv$LOD_ZOOM && length(r$classes) > 1L) "classes" else "nodes"
    }

    if (mode == "classes") {
      geom <- class_geometry(r)
      sz <- max(900, min(2400, 180 * max(geom$K, 3) + 500))
      band <- round(sz * 0.11)
      nat <- table(factor(r$nature_of, levels = names(COL_NATURE)))
      tryCatch({
        grDevices::png(f, width = sz, height = sz + band, res = 110)
        layout(matrix(c(1, 2), 2, 1), heights = c(band, sz))
        par(mar = c(0, 0, 0, 0), bg = "white")
        plot(NA, xlim = c(0, 1), ylim = c(0, 1), axes = FALSE, xlab = "", ylab = "", xaxs = "i", yaxs = "i")
        text(0.5, 0.74, "Vue courante - Par classes de communication", font = 2, cex = 1.6, col = COL_HEAD)
        cnt <- c(nat[["Recurrente"]], nat[["Transitoire"]], nat[["Absorbant"]]); nm <- names(COL_NATURE)
        lx <- c(0.26, 0.46, 0.68)
        for (k in 1:3) {
          points(lx[k], 0.30, pch = 21, bg = COL_NATURE[[k]], col = "white", cex = 3, lwd = 2)
          text(lx[k] + 0.018, 0.30, sprintf("%s (%d)", nm[k], cnt[k]), adj = c(0, 0.5), cex = 1.1, font = 2, col = COL_INK)
        }
        draw_graph_classes(r, geom, c(-geom$lim, geom$lim), c(-geom$lim, geom$lim), sz, edges)
        grDevices::dev.off()
        setstatus(paste("Vue courante (classes) exportée :", f), COL_NATURE[["Recurrente"]])
      }, error = function(e) setstatus(paste("Echec export :", conditionMessage(e)), COL_NATURE[["Absorbant"]]))
    } else {
      g <- graph_geometry(r)
      sz <- max(1200, min(3200, 32 * r$n + 700))
      band <- round(sz * 0.11)
      nat <- table(factor(r$nature_of, levels = names(COL_NATURE)))
      tryCatch({
        grDevices::png(f, width = sz, height = sz + band, res = 110)
        layout(matrix(c(1, 2), 2, 1), heights = c(band, sz))
        par(mar = c(0, 0, 0, 0), bg = "white")
        plot(NA, xlim = c(0, 1), ylim = c(0, 1), axes = FALSE, xlab = "", ylab = "", xaxs = "i", yaxs = "i")
        text(0.5, 0.74, "Vue courante - Graphe détaillé", font = 2, cex = 1.6, col = COL_HEAD)
        cnt <- c(nat[["Recurrente"]], nat[["Transitoire"]], nat[["Absorbant"]]); nm <- names(COL_NATURE)
        lx <- c(0.26, 0.46, 0.68)
        for (k in 1:3) {
          points(lx[k], 0.30, pch = 21, bg = COL_NATURE[[k]], col = "white", cex = 3, lwd = 2)
          text(lx[k] + 0.018, 0.30, sprintf("%s (%d)", nm[k], cnt[k]), adj = c(0, 0.5), cex = 1.1, font = 2, col = COL_INK)
        }
        draw_graph(r, labs, g, c(-g$lim, g$lim), c(-g$lim, g$lim), sz, edges, showp)
        grDevices::dev.off()
        setstatus(paste("Vue courante (détaillée) exportée :", f), COL_NATURE[["Recurrente"]])
      }, error = function(e) setstatus(paste("Echec export :", conditionMessage(e)), COL_NATURE[["Absorbant"]]))
    }
  }

  export_forecast_png <- function() {
    if (is.null(st$model)) { setstatus("Analysez d'abord une matrice.", COL_NATURE[["Transitoire"]]); return(invisible()) }
    f <- tclvalue(tkgetSaveFile(defaultextension = ".png", filetypes = "{{Image PNG} {.png}} {{Tous} *}"))
    if (!nzchar(f)) return(invisible())
    fc <- .forecast_compute(); r <- fc$r; labs <- fc$labs; M <- fc$M
    horizon <- nrow(M) - 1L; unit <- tclvalue(unitVar)
    tryCatch({
      grDevices::png(f, width = 1600, height = 900, res = 130)
      par(oma = c(0, 0, 2.4, 0))
      draw_forecast_plot(M, labs, unit, fc$pistar)
      etat <- labs[which.max(M[1, ])]
      mtext(sprintf("Prevision (%s) - %d pas - depart : %s", unit, horizon, etat),
            outer = TRUE, side = 3, line = 0.4, cex = 1.3, font = 2, col = COL_HEAD)
      grDevices::dev.off()
      setstatus(paste("Prevision exportee :", f), COL_NATURE[["Recurrente"]])
    }, error = function(e) setstatus(paste("Echec export :", conditionMessage(e)), COL_NATURE[["Absorbant"]]))
  }

  tkbind(cbp, "<<ComboboxSelected>>", function() {
    p <- PRESETS[[tclvalue(presetVar)]]
    tkdelete(matTxt, "1.0", "end"); tkinsert(matTxt, "1.0", p$m)
    tkdelete(labTxt, "1.0", "end"); tkinsert(labTxt, "1.0", p$labels); analyser(FALSE)
  })
  tkbind(startCb, "<<ComboboxSelected>>", function() previsionner())
  tkwm.protocol(tt, "WM_DELETE_WINDOW", function() tkdestroy(tt))

  draw_header(); analyser(FALSE); tcl(nb, "select", tabD)
  if (!interactive()) tkwait.window(tt)
  invisible(tt)
}

#   6. TESTS INTERNES (lancer via : Rscript MarkovStudio.R --test)
.run_tests <- function() {
  ok <- TRUE
  expect <- function(cond, msg) {
    if (isTRUE(cond)) cat(sprintf("  [PASS] %s\n", msg))
    else { cat(sprintf("  [FAIL] %s\n", msg)); ok <<- FALSE }
  }
  cat("=== Tests internes Markov Studio ===\n")

  P <- matrix(c(0.6,0.3,0.1,0, 0.2,0.5,0.2,0.1, 0.1,0.3,0.4,0.2, 0,0,0,1), 4, 4, byrow = TRUE)
  r <- analyse_markov(P)
  expect(length(r$classes) == 2L && identical(sort(r$nature), c("Absorbant", "Transitoire")),
         "4x4 absorbante : 2 classes (Transitoire + Absorbant)")
  expect(r$nature_of[4] == "Absorbant", "etat 4 absorbant")

  P2 <- matrix(c(0, 1, 1, 0), 2, 2)
  r2 <- analyse_markov(P2)
  expect(r2$period[1L] == 2L, "bipartite 2x2 periode 2")
  expect(abs(r2$pi[1L] - 0.5) < 1e-6, "bipartite stationnaire pi = (0.5, 0.5)")

  expect(all.equal(parse_matrix("0,5 0,3 0,2\n0,1 0,8 0,1\n0,2 0,2 0,6"),
                   parse_matrix("0.5 0.3 0.2\n0.1 0.8 0.1\n0.2 0.2 0.6")),
         "decimales virgule == decimales point")
  expect(nrow(parse_matrix("0,5 0,5\r\n0,5 0,5\r\n")) == 2L, "Windows CRLF lu correctement")
  expect(nrow(parse_matrix("0,5 0,5\r0,5 0,5\r")) == 2L,     "Mac CR lu correctement")

  Mtri <- parse_matrix("3 5 0.5\n3 5 0.3\n3 8 0.2\n5 8 1.0\n8 3 1.0")
  expect(Mtri[3L, 5L] == 0.8, "format triplet : deduplication par somme")

  P_one <- matrix(c(0.5, 0.5, 0.5, 0.5), 2, 2)
  r_one <- analyse_markov(P_one)
  expect(length(r_one$classes) == 1L, "matrice dense fortement connexe -> 1 classe")

  sp_in <- structure(list(n = 6000L,
                          iv = rep(seq_len(6000L), each = 3L),
                          jv = sample(6000L, 6000L * 3L, replace = TRUE),
                          vv = rep(1, 6000L * 3L)), class = "markov_sparse_input")
  sp_in <- normalize_rows(sp_in)
  r_sp <- analyse_markov(sp_in)
  expect(is.null(r_sp$P) && isTRUE(r_sp$sparse_pure), "mode sparse-pur : r$P = NULL")
  expect(r_sp$n == 6000L, "mode sparse-pur : n preserve")

  P_per <- matrix(c(0, 0.5, 0.5, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0), 5, 5, byrow = TRUE)
  expect(matrix_power(diag(3), 5)[1L, 1L] == 1, "matrix_power(I, k) = I")

  cat(if (ok) "\n=== TOUS LES TESTS PASSENT ===\n" else "\n=== ECHEC ===\n")
  invisible(ok)
}

#   7. LANCEMENT
if (sys.nframe() == 0L) {
  args <- commandArgs(trailingOnly = TRUE)
  if (length(args) && "--test" %in% args) {
    ok <- .run_tests()
    quit(status = if (isTRUE(ok)) 0L else 1L)
  } else launch_app()
}
