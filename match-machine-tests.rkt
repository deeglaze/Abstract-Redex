#lang racket

(require "match-machine-data.rkt"
         "match-machine.rkt")

(define (sexp->term t)
  (match t
    ['hole *t:hole]
    [(or (? symbol? t) (? number? t) (? null? t)) (term:atom t)]
    [`(left ,t₀ ,t₁) (term:left (sexp->term t₀) (sexp->term t₁))]
    [`(right ,t₀ ,t₁) (term:right (sexp->term t₀) (sexp->term t₁))]
    [(cons t₀ t₁) (term:cons (sexp->term t₀) (sexp->term t₁))]))

(define λG
  (hash 'var (set (pattern:datum symbol?))
        'rho (set (pattern:atom '())
                  (pattern:cons (pattern:cons (pattern:nt 'var) (pattern:nt 'closure))
                                (pattern:nt 'rho)))
        'expr (set (pattern:nt 'var)
                   (pattern:cons (pattern:nt 'expr) (pattern:nt 'expr))
                   (pattern:nt 'lam))
        'lam (set (pattern:cons (pattern:atom 'λ)
                                (pattern:cons (pattern:cons (pattern:nt 'var) (pattern:atom '()))
                                              (pattern:nt 'expr))))
        'E (set *p:hole
                (pattern:cons (pattern:nt 'E) (pattern:nt 'closure))
                (pattern:cons (pattern:nt 'value) (pattern:nt 'E)))
        'closure (set (pattern:cons (pattern:nt 'expr) (pattern:nt 'rho))
                      (pattern:cons (pattern:nt 'closure) (pattern:nt 'closure)))
        'value (set (pattern:cons (pattern:nt 'lam) (pattern:nt 'rho)))))

(define (ρ-lookup ρ×x)
  (match-term ρ×x
    [(cons (term:atom '()) _) (raise 'oops)]
    [(cons (term:cons (term:cons (term:atom y) v) ρ) 
           (and (term:atom x) xa))
     (if (eq? x y)
         v
         (ρ-lookup (term:cons ρ xa)))]))

(define λS
  ;; lookup x in ρ
  (set (rewrite (pattern:in-hole (pattern:name 'E (pattern:nt 'E))
                                 (pattern:cons (pattern:name 'x (pattern:nt 'var))
                                               (pattern:name 'ρ (pattern:nt 'rho))))
                (r:in-hole (r:var 'E) (r:app ρ-lookup (r:cons (r:var 'ρ) (r:var 'x)))))
       ;; distribute ρs
       (rewrite (pattern:in-hole (pattern:name 'E (pattern:nt 'E))
                                 (pattern:cons
                                  (pattern:cons (pattern:name 'e₀ (pattern:nt 'expr))
                                                (pattern:name 'e₁ (pattern:nt 'expr)))
                                  (pattern:name 'ρ (pattern:nt 'rho))))
                (r:in-hole (r:var 'E) (r:cons (r:cons (r:var 'e₀) (r:var 'ρ))
                                              (r:cons (r:var 'e₁) (r:var 'ρ)))))
       ;; apply function
       (rewrite (pattern:in-hole (pattern:name 'E (pattern:nt 'E))
                                 (pattern:cons
                                  (pattern:cons
                                   (pattern:cons (pattern:atom 'λ)
                                                 (pattern:cons (pattern:cons (pattern:name 'x (pattern:nt 'var)) (pattern:atom '()))
                                                               (pattern:name 'e (pattern:nt 'expr))))
                                   (pattern:name 'ρ (pattern:nt 'rho)))
                                  (pattern:name 'v (pattern:nt 'value))))
                (r:in-hole (r:var 'E) (r:cons (r:var 'e)
                                              (r:cons (r:cons (r:var 'x) (r:var 'v))
                                                      (r:var 'ρ)))))))
(define id-id
  (sexp->term (cons (cons '(λ (x) . x) 
                          '(λ (y) . y))
                    ;; starting ρ
                    '())))
(printf "program: ~a~%~%" id-id)

(with-language-semantics (λG λS)
  (pretty-print (apply-reduction-relation* id-id)))
