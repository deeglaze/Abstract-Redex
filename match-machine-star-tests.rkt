#lang racket

(require "match-machine-star-data.rkt"
         "match-machine-star.rkt"
         racket/trace)

(define (sexp->term t)
  (define (classify t)
    (match t
      [`(left ,t₀ ,t₁) (list make-term:left t₀ t₁)]
      [`(right ,t₀ ,t₁) (list make-term:right t₀ t₁)]
      [(cons t₀ t₁) (list make-term:cons t₀ t₁)]))
  (match t
    ['hole *t:hole]
    [(or (? symbol? t) (? number? t) (? null? t) (? hash? t)) 
     (term:atom t)]
    [(app classify (list k t₀ t₁))
     (define ta₀ (tℓ (gensym)))
     (define ta₁ (tℓ (gensym)))
     (σ-bind ta₀ (sexp->term t₀))
     (σ-bind ta₁ (sexp->term t₁))
     (k ta₀ ta₁)]))

(define ρ? hash?)

(define λG
  (hash 'var (set (pattern:datum symbol?))
        'expr (set (pattern:nt 'var)
                   (pattern:cons (pattern:nt 'expr) (pattern:nt 'expr))
                   (pattern:nt 'lam))
        'lam (set (pattern:cons (pattern:atom 'λ)
                                (pattern:cons (pattern:cons (pattern:nt 'var) (pattern:atom '()))
                                              (pattern:nt 'expr))))
        'E (set *p:hole
                (pattern:cons (pattern:nt 'E) (pattern:nt 'closure))
                (pattern:cons (pattern:nt 'value) (pattern:nt 'E)))
        'closure (set (pattern:cons (pattern:nt 'expr) (pattern:datum ρ?))
                      (pattern:cons (pattern:nt 'closure) (pattern:nt 'closure)))
        'value (set (pattern:cons (pattern:nt 'lam) (pattern:datum ρ?)))))

(define (ρ-lookup ρ×x)
  (match ρ×x
    [(term:cons (term:atom ρ) (term:atom x)) 
     (hash-ref ρ x (λ () (raise 'oops)))]))

(define (ρ-add ρ×x×v)
  (match ρ×x×v
    [(term:cons (term:atom ρ) (term:cons (term:atom x) v))
     (make-term:atom (hash-set ρ x v))]))

(define λS
  ;; lookup x in ρ
  (set (rewrite (pattern:in-hole (pattern:name 'E (pattern:nt 'E))
                                 (pattern:cons (pattern:name 'x (pattern:nt 'var))
                                               (pattern:name 'ρ (pattern:datum ρ?))))
                (r:in-hole (r:var 'E) (r:app ρ-lookup (r:cons (r:var 'ρ) (r:var 'x)))))
       ;; distribute ρs
       (rewrite (pattern:in-hole (pattern:name 'E (pattern:nt 'E))
                                 (pattern:cons
                                  (pattern:cons (pattern:name 'e₀ (pattern:nt 'expr))
                                                (pattern:name 'e₁ (pattern:nt 'expr)))
                                  (pattern:name 'ρ (pattern:datum ρ?))))
                (r:in-hole (r:var 'E) (r:cons (r:cons (r:var 'e₀) (r:var 'ρ))
                                              (r:cons (r:var 'e₁) (r:var 'ρ)))))
       ;; apply function
       (rewrite (pattern:in-hole (pattern:name 'E (pattern:nt 'E))
                                 (pattern:cons
                                  (pattern:cons
                                   (pattern:cons (pattern:atom 'λ)
                                                 (pattern:cons (pattern:cons (pattern:name 'x (pattern:nt 'var)) (pattern:atom '()))
                                                               (pattern:name 'e (pattern:nt 'expr))))
                                   (pattern:name 'ρ (pattern:datum ρ?)))
                                  (pattern:name 'v (pattern:nt 'value))))
                (r:in-hole (r:var 'E) (r:cons (r:var 'e)
                                              (r:app ρ-add (r:cons (r:var 'ρ) (r:cons (r:var 'x) (r:var 'v)))))))))
(define id-id
  (cons (cons '(λ (x) . x) 
              '(λ (y) . y))
        ;; starting ρ
        ⊥eq))

(with-language-semantics (λG λS)
  (pretty-print (apply-reduction-relation* (sexp->term id-id))))
