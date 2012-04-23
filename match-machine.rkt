#lang racket

(require "macros.rkt"
         "match-machine-data.rkt"
         racket/trace)
(provide with-language-semantics inject
         apply-reduction-relation apply-reduction-relation*)

;; ⊔ : b/c b/c -> b/c + #f
;; Hash extension where overlap is tolerated only when the dictionaries agree.
(define (⊔ b₀ b₁)
  (let/ec bad
    (for*/fold ([res b₀]) ([(x t) (in-hash b₁)])
      (cond [(andit (hash-ref b₀ x #f) (not (equal? t it))) (bad #f)]
            [else (hash-set res x t)]))))

(define (context->term C)
  (match-context C
    [(hole) *t:hole]
    [(left C t) (make-term:left (context->term C) t)]
    [(right t C) (make-term:right t (context->term C))]))

;; Term -> (Context + #f)
(define (term->context-or-f t)
  (match-term t
    [(hole) *c:hole]
    [(left tC t)
     (andit (term->context-or-f tC) (make-context:left it t))]
    [(right t tC)
     (andit (term->context-or-f tC) (make-context:right t it))]
    [_ #f]))

;; do same as above, but do no construction
(define (term-is-context-like? t)
  (match-term t
    [(hole) #t]
    [(left tC t) (term-is-context-like? tC)]
    [(right t tC) (term-is-context-like? tC)]
    [_ #f]))

(define (no-contexts? t)
  (match-term t
    [(atom _) #t]
    [(cons car cdr) (and (no-contexts? car) (no-contexts? cdr))]
    [_ #f]))

;; dispatch to different step functions to keep sanity.
(define (step s)
  (cond [(state:Meval? s)  (step-match-eval s)]
        [(state:Mapply? s) (step-match-apply s)]
        [(state:Aeval? s)  (step-append-eval s)]
        [(state:Aapply? s) (step-append-apply s)]
        [(state:Ieval? s)  (step-inst-eval s)]
        [(state:Iapply? s) (step-inst-apply s)]
        [(state:Peval? s)  (step-plug-eval s)]
        [(state:Papply? s) (step-plug-apply s)]))

(define (final-state? s)
  (match-state s
    [(Iapply _ _ (? I:mt?)) #t] ;; finished an instantiation of a rule.
    [_ #f]))
(define (stuck-state? s) #f)

;; non-recursive helper used to get (k tl tr) from the paper.
(define (classify-constructor t)
  (match-term t
    [(left tl tr) (list 'left tl tr)]
    [(right tl tr) (list 'right tl tr)]
    [(cons tl tr) (list 'cons tl tr)]
    [_ '()]))

;; get ALL next steps to flatten out nondeterminism.
;; step-match-eval : Meval → (setof State)
(define (step-match-eval s)
  (match-define (state:Meval p t M) s)
  (define (mk-done db) (make-state:Mapply db M))
  (define (mk-step p t M) (make-state:Meval p t M))
  (match* (p t)
    [((pattern:hole) t)
     (∪ (set (mk-done (make-m (d:context *c:hole t) ⊥eq)))
        (cond [(term:hole? t) (set (mk-done (make-m *d:· ⊥eq)))]
              [else ∅]))]
    [((pattern:atom a) (term:atom a))
     (set (mk-done (make-m *d:· ⊥eq)))]
    [((pattern:datum f) (term:atom a)) ;; cheap way to get symbol?, number? etc.
     (cond [(f a) (set (mk-done (make-m *d:· ⊥eq)))]
           [else ∅])]
    [((pattern:cons pl pr) (app classify-constructor (list k tl tr)))
     (set (mk-step pl tl (make-M:right pr tl tr k M)))]
    [((pattern:in-hole pc ph) t)
     (set (mk-step pc t (make-M:hole ph M)))]
    [((pattern:name x p) t)
     (set (mk-step p t (make-M:name x t M)))]
    [((pattern:nt n) t)
     (for/set ([p (hash-ref (G) n (λ () (error 'step-match-eval "Unknown nonterminal ~a" n)))])
       (mk-step p t (make-M:nt M)))]
    [(_ _) ∅]))

(define (do-select tl dl tr dr)
  (match-d dl
    [(·) (match-d dr
           [(·) (set *d:·)]
           [(context C tr′) (set (make-d:context (make-context:right tl C) tr′))])]
    [(context C tl′) (match-d dr
                       [(·) (set (make-d:context (make-context:left C tr) tl′))]
                       [_ ∅])]))

(define (do-named d t)
  (match-d d
    [(·) t]
    [(context C _) (context->term C)]))

;; step-match-apply : Mapply → (setof State)
(define (step-match-apply s)
  (match-define (state:Mapply (and (m d b) db) M) s)
  (define (mk-done db M) (make-state:Mapply db M))
  (define (mk-step p t M) (make-state:Meval p t M))
  (match-M M
    [(mt r)
     (match-d d
       [(·) (printf "WOOO MATCH! ~a~%~%" b)
        (set (make-state:Ieval r b (make-I:mt)))] ;; found a full match
       [(context _ _) ∅])] ;; incomplete match. Toss.
    [(right pr tl tr k M)
     (set (mk-step pr tr (make-M:select tl tr k db M)))]
    [(select tl tr k (m dl bl) M) ;; b = br from paper
     ;; ⊔ partial! Make sure we don't allow bad bindings.
     (define b′ (⊔ bl b))
     (cond [b′ (for/set ([d (do-select tl dl tr d)])
                (mk-done (make-m d b′) M))]
           [else ∅])]
    [(hole ph M)
     (match-d d
       [(context C tc) (set (mk-step ph tc (make-M:combine C b M)))]
       [_ ∅])]
    [(combine Cl bc M) ;; b = bh from paper
     (define b′ (⊔ bc b))
     (cond [b′ (match-d d
                [(·) (set (mk-done (make-m *d:· b′) M))]
                [(context Cr t) (set (make-state:Aeval Cl Cr t b′ (make-A:mt M)))])]
           [else ∅])]
    [(name x t M)
     (define b′ (⊔ b (hash x (do-named d t))))
     (cond [b′ (set (mk-done (make-m d b′) M))]
           [else ∅])]
    ;; drop db's bindings since they were "intermediate"
    [(nt M) (set (mk-done (make-m d ⊥eq) M))]))

(define (step-append-eval s)
  (match-define (state:Aeval Cl Cr t b A) s)
  (set
    (match-context Cl
      [(hole) (make-state:Aapply Cr t b A)]
      [(left C t′) (make-state:Aeval C Cr t b (make-A:left t′ A))]
      [(right t′ C) (make-state:Aeval C Cr t b (make-A:right t′ A))])))

(define (step-append-apply s)
  (match-define (state:Aapply C t b A) s)
  (set
   (match-A A
      [(mt M) (make-state:Mapply (make-m (make-d:context C t) b) M)]
      [(left t′ A) (make-state:Aapply (make-context:left C t′) t b A)]
      [(right t′ A) (make-state:Aapply (make-context:right t′ C) t b A)])))

(define (step-inst-eval s)
  (match-define (state:Ieval r b I) s)
  (define (mk-done t) (make-state:Iapply t b I))
  (define (mk-step r I) (make-state:Ieval r b I))
  (match-r r
    [(hole) (set (mk-done *t:hole))]
    [(atom a) (set (mk-done (make-term:atom a)))]
    [(var x)
     (define xterm (hash-ref b x #f))
     (cond [xterm (set (mk-done xterm))]
           [else ∅])] ;; XXX: raise error?
    [(in-hole rc rh) (set (mk-step rc (make-I:plug-right rh I)))]
    [(cons rl rr) (set (mk-step rl (make-I:join-right rr I)))]
    [(app f r) (set (mk-step r (make-I:meta-app f I)))]))

(define (step-inst-apply s)
  (match-define (state:Iapply t b I) s)
  (match-I I
    ;;; Outer evaluator will stop on these states.
    ;;; We can call step to start another object language step.
    [(mt) (for/set ([rule (in-set (S))])
                (match-define (rewrite p r) rule)
                (make-state:Meval p t (M:mt r)))]
    [(plug-right r I) (set (make-state:Ieval r b (make-I:do-plug t I)))]
    [(join-right r I) (set (make-state:Ieval r b (make-I:do-join t I)))]
    [(do-plug tc I) 
     (define C (term->context-or-f tc))
     (cond [C (set (make-state:Peval C t (make-P:mt b I)))]
           [else ∅])] ;; XXX: raise error
    [(do-join tl I)
     (cond [(and (term-is-context-like? tl) (no-contexts? t))
            (set (make-state:Iapply (make-term:left tl t) b I))]
           [(and (term-is-context-like? t) (no-contexts? tl))
            (set (make-state:Iapply (make-term:right tl t) b I))]
           [else (set (make-state:Iapply (make-term:cons tl t) b I))])]
    ;; TODO: break into several steps if we know the metafunction
    ;; is just another reduction relation (but a functional one)
    [(meta-app f I) (set (make-state:Iapply (f t) b I))]))

(define (step-plug-eval s)
  (match-define (state:Peval C t P) s)
  (match-context C
    [(hole) (set (make-state:Papply t P))]
    [(left Cl tr)
     (cond [(term-is-context-like? t)
            (set (make-state:Peval Cl t (make-P:left-context tr P)))]
           [else (set (make-state:Peval Cl t (make-P:left-term tr P)))])]
    [(right tl Cr)
     (cond [(term-is-context-like? t)
            (set (make-state:Peval Cr t (make-P:right-context tl P)))]
           [else (set (make-state:Peval Cr t (make-P:right-term tl P)))])]))

(define (step-plug-apply s)
  (match-define (state:Papply t P) s)
  (match-P P
    [(mt b I) (set (make-state:Iapply t b I))]
    [(left-context tr P)  (set (make-state:Papply (make-term:left  t tr) P))]
    [(left-term tr P)     (set (make-state:Papply (make-term:cons  t tr) P))]
    [(right-context tl P) (set (make-state:Papply (make-term:right tl t) P))]
    [(right-term tl P)    (set (make-state:Papply (make-term:cons  tl t) P))]))

;; get all starting terms.
(define (inject term)
  (define ΔW (make-hash))
  (for ([ς (step-inst-apply (make-state:Iapply term ⊥eq (make-I:mt)))])
    (hash-set! ΔW ς #t))
  ΔW)

(define-syntax-rule (with-language-semantics (grammar semantics) expr1 exprs ...)
  (parameterize ([G grammar] [S semantics]) expr1 exprs ...))

(define (apply-reduction-relation ΔW [W (make-hash)])
  (define Final (make-hash))

  ;; Add ς to the work set (and the seen set)
  (define (todo ς)
    (unless (hash-has-key? W ς)
      (hash-set! W ς #t)
      (hash-set! ΔW ς #t)))

  (let loop () ;; for monotone state updates. Doesn't work for GC.
    (define ς (for/first ([(k _) (in-hash ΔW)]) k))
    (cond [ς
           (cond [(final-state? ς) (hash-set! Final ς #t)]
                 [else (for ([ς′ (in-set (step ς))])
                         (todo ς′))])
           (hash-remove! ΔW ς)
           (loop)]
          [else Final])))

(define (apply-reduction-relation* term)
  (define ΔW (inject term))
  (define W (hash-copy ΔW))
  (define steps (make-hash))

  (let loop ()
    (define final (apply-reduction-relation ΔW W))
    ;; loop if there is a step we haven't taken yet.
    (cond [(for/or ([(ς _) (in-hash final)] 
                    #:unless (hash-has-key? steps ς))
             (hash-set! steps ς #t)
             (for ([ς′ (step-inst-apply ς)])
               (hash-set! ΔW ς′ #t)
               (hash-set! W ς′ #t))) 
           (loop)]
          [else steps])))
