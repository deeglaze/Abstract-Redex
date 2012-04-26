#lang racket

(require "macros.rkt"
         "match-machine-star-data.rkt"
         "env-to-recursive.rkt")
(provide with-language-semantics inject
         apply-reduction-relation apply-reduction-relation*)

;; ⊔ : b/c b/c -> b/c + #f
;; Hash extension where overlap is tolerated only when the dictionaries agree.
(define (⊔ b₀ b₁)
  (let/ec bad
    (for*/fold ([res b₀]) ([(x t) (in-hash b₁)])
      (cond [(andit (hash-ref b₀ x #f)
                    (not (equal? t it))) ;; TODO: fix equality.
             (bad #f)]
            [else (hash-set res x t)]))))

;; Address -> (setof Storable)
(define (resolve-term/context tc)
  (match tc
    [(or (? termℓ?) (? contextℓ?)) (σ-lookup tc)]
    [_ (set tc)]))

(define (context-flat->term-flat C)
  (match C
    [(context:hole) *t:hole]
    [(cℓ a)
     (define ts (for/set ([Ca (in-set (σ-lookup C))])
                  (context->term Ca)))
     (σ-flat-bind (tℓ a) ts)]
    [err (error 'context-flat->term-flat "bad match ~a" err)]))

(define (context->term C)
  (match C
    [(context:left Cf tf)
     (make-term:left (context-flat->term-flat Cf) tf)]
    [(context:right tf Cf)
     (make-term:right tf (context-flat->term-flat Cf))]
    [_ (context-flat->term-flat C)]))

(define (term-flat->context-flat-or-f t)
  (match t
    [(term:hole) *c:hole]
    [(tℓ a)
     (define Cs (for*/set ([ta (in-set (σ-lookup t))]
                           [Ca (in-value (term->context-or-f ta))]
                           #:unless (false? Ca))
                  Ca))
     (cond [(set-empty? Cs) #f]
           [else (σ-flat-bind (cℓ a) Cs)])]
    [_ #f]))

;; Term -> (Context + #f)
(define (term->context-or-f t)
  (match t
    [(term:left tC t)
     (andit (term-flat->context-flat-or-f tC) (make-context:left it t))]
    [(term:right t tC)
     (andit (term-flat->context-flat-or-f tC) (make-context:right t it))]
    [_ (term-flat->context-flat-or-f t)]))

;; do same as above, but do no construction
;; term -> (set #t #f)
(define (term-is-context-like? t)
  (match t
    [(term:hole) (set #t)]
    [(? tℓ?)
     (for/fold ([res ∅]) ([t (in-set (σ-lookup t))])
       (∪ res (term-is-context-like? t)))]
    [(term:left tC t) (term-is-context-like? tC)]
    [(term:right t tC) (term-is-context-like? tC)]
    [_ (set #f)]))

;; term -> (set #t #f)
(define (no-contexts? t)
  (match t
    [(? term:atom?) (set #t)]
    [(? tℓ?) ;; XXX: should this be and?
     (for/fold ([res ∅]) ([t (in-set (σ-lookup t))])
       (∪ res (no-contexts? t)))]
    [(term:cons car cdr)
     (define nc-car (no-contexts? car))
     (define nc-cdr (no-contexts? cdr))
     (cond [(and (set-member? nc-car #t) (set-member? nc-cdr #t))
            (∪ nc-car nc-cdr)]
           [else (set #f)])]
    [_ (set #f)]))

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
  (match s
    [(state:Iapply _ _ a)
     (set-member? (σ-lookup a) *I:mt)] ;; finished an instantiation of a rule.
    [_ #f]))
(define (stuck-state? s) #f)

;; get ALL next steps to flatten out nondeterminism.
;; step-match-eval : Meval → (setof State)
(define (step-match-eval s)
  (match-define (state:Meval p t Ma) s)
  (define (mk-done db) (make-state:Mapply db Ma))
  (define (mk-step p t Ma) (make-state:Meval p t Ma))
  (for/fold ([ςs ∅]) ([t (resolve-term/context t)])
    (define Mb ((alloc) s t))
    (match* (p t)
      [((pattern:hole) t)
       (∪ (set-add ςs (mk-done (make-m (d:context *c:hole t) ⊥eq)))
          (cond [(set-member? (resolve-term/context t) *t:hole)
                 (set (mk-done base-m))]
                [else ∅]))]
      [((pattern:atom a) (term:atom a))
       (set-add ςs (mk-done (make-m *d:· ⊥eq)))]
      [((pattern:datum f) (term:atom a)) ;; cheap way to get symbol?, number? etc.
       (cond [(f a) (set-add ςs (mk-done base-m))]
             [else ςs])]
      [((pattern:cons pl pr) (or (term:cons tl tr)
                                 (term:left tl tr)
                                 (term:right tl tr)))
       (set-add ςs (mk-step pl tl (σ-bind Mb (make-M:right pr tl tr Ma))))]
      [((pattern:in-hole pc ph) t)
       (set-add ςs (mk-step pc t (σ-bind Mb (make-M:hole ph Ma))))]
      [((pattern:name x p) t)
       (set-add ςs (mk-step p t (σ-bind Mb (make-M:name x t Ma))))]
      [((pattern:nt n) t)
       (σ-bind Mb (make-M:nt Ma))
       (for/fold ([ςs ςs]) ([p (follow-nt n)])
         (set-add ςs (mk-step p t Mb)))]
      [(_ _) ςs])))

(define (do-select addr tl dl tr dr)
  (match-d dl
    [(·) (match-d dr
           [(·) (set *d:·)]
           [(context C tr′)
            (set (make-d:context (alloc-context-right addr tl C) tr′))])]
    [(context C tl′) (match-d dr
                       [(·)
                        (set (make-d:context (alloc-context-left addr C tr) tl′))]
                       [_ ∅])]))

(define (do-named d t)
  (match-d d
    [(·) t]
    [(context C _) (context->term C)]))

;; step-match-apply : Mapply → (setof State)
(define (step-match-apply s)
  (match-define (state:Mapply (and (m d b) db) Ma) s)
  (define (mk-done db Ma) (make-state:Mapply db Ma))
  (define (mk-step p t Ma) (make-state:Meval p t Ma))
  (for/fold ([ςs ∅]) ([M (σ-lookup Ma)])
    (define addr ((alloc) s M))
    (match M
      [(M:mt r)
       (match-d d
         [(·) (printf "WOO MATCH! ~a~%~%" b)
          (set-add ςs (make-state:Ieval r b (σ-bind addr *I:mt)))] ;; found a full match
         [(context _ _) ςs])] ;; incomplete match. Toss.
      [(M:right pr tl tr Mb)
       (set-add ςs (mk-step pr tr (σ-bind addr (make-M:select tl tr db Mb))))]
      [(M:select tl tr (m dl bl) Mb) ;; b = br from paper
       ;; ⊔ partial! Make sure we don't allow bad bindings.
       (define b′ (⊔ bl b))
       (cond [b′ (for/fold ([ςs ςs]) ([d (do-select addr tl dl tr d)])
                   (set-add ςs (mk-done (make-m d b′) Mb)))]
             [else ςs])]
      [(M:hole ph Mb)
       (match-d d
         [(context C tc)
          (set-add ςs (mk-step ph tc (σ-bind addr (make-M:combine C b Mb))))]
         [_ ςs])]
      [(M:combine Cl bc Mb) ;; b = bh from paper
       (define b′ (⊔ bc b))
       (cond [b′ (match-d d
                   [(·) (set-add ςs (mk-done (make-m *d:· b′) Mb))]
                   [(context Cr t)
                    (σ-bind addr (make-A:mt Mb))
                    (set-add ςs (make-state:Aeval Cl Cr t b′ addr))])]
             [else ςs])]
      [(M:name x t Mb)
       (define b′ (⊔ b (hash x (do-named d t))))
       (cond [b′ (set-add ςs (mk-done (make-m d b′) Mb))]
             [else ςs])]
      ;; drop db's bindings since they were "intermediate"
      [(M:nt Mb) (set-add ςs (mk-done (make-m d ⊥eq) Mb))]
      [err (error 'step-match-apply "bad match ~a" err)])))

(define (step-append-eval s)
  (match-define (state:Aeval Cl Cr t b Aa) s)
  (for/set ([Cl* (resolve-term/context Cl)])
    (define Ab ((alloc) s Cl*))
    (match Cl*
      [(context:hole) (set (make-state:Aapply Cr t b Aa))]
      [(context:left Cf tf′)
       (make-state:Aeval Cf Cr t b (σ-bind Ab (make-A:left tf′ Aa)))]
      [(context:right tf′ Cf)
       (make-state:Aeval Cf Cr t b (σ-bind Ab (make-A:right tf′ Aa)))]
      [err (error 'step-append-eval "bad match ~a" err)])))

(define (step-append-apply s)
  (match-define (state:Aapply C t b Aa) s)
  (for/set ([A (σ-lookup Aa)])
    (define addr ((alloc) s A))
    (match A
      [(A:mt Ma) (make-state:Mapply (make-m (make-d:context C t) b) Ma)]
      [(A:left t′ Ab)
       (σ-bind addr (alloc-context-left addr C t′))
       (make-state:Aapply addr t b Ab)]
      [(A:right t′ Ab)
       (σ-bind addr (alloc-context-right addr t′ C))
       (make-state:Aapply addr t b Ab)]
      [err (error 'step-append-apply "bad match ~a" err)])))

(define (step-inst-eval s)
  (match-define (state:Ieval r b Ia) s)
  (define (mk-done t) (make-state:Iapply t b Ia))
  (define (mk-step r Ib) (make-state:Ieval r b Ib))
  (define Ib ((alloc) s))
  (match r
    [(r:hole) (set (mk-done *t:hole))]
    [(r:atom a) (set (mk-done (make-term:atom a)))]
    [(r:var x)
     (define xterm (hash-ref b x #f))
     (cond [xterm (set (mk-done xterm))]
           [else ∅])] ;; XXX: raise error?
    [(r:in-hole rc rh) (set (mk-step rc (σ-bind Ib (make-I:plug-right rh Ia))))]
    [(r:cons rl rr) (set (mk-step rl (σ-bind Ib (make-I:join-right rr Ia))))]
    [(r:app f '()) (set (mk-done (f)))]
    [(r:app f (cons r rs)) (set (mk-step r (σ-bind Ib (make-I:meta-app f rs '() Ia))))]
    [err (error 'step-inst-eval "bad match ~a" err)]))

(define (step-inst-apply s)
  (match-define (state:Iapply t b Ia) s)
  (for/fold ([ςs ∅]) ([I (σ-lookup Ia)])
    (match I
      ;; Outer evaluator will stop on these states.
      ;; We can call step to start another object language step.
      [(I:mt)
       (for/fold ([ςs ςs]) ([rule (in-set (S))])
         (match-define (rewrite p r) rule)
         (set-add ςs (make-state:Meval p t (σ-bind ((alloc) s rule) (M:mt r)))))]
      [(I:plug-right r Ib)
       (set-add ςs (make-state:Ieval r b (σ-bind ((alloc) s I) (make-I:do-plug t Ib))))]
      [(I:join-right r Ib)
       (set-add ςs (make-state:Ieval r b (σ-bind ((alloc) s I) (make-I:do-join t Ib))))]
      [(I:do-plug tc Ib)
       (define C (term->context-or-f tc))
       (cond [C (set-add ςs (make-state:Peval C t (σ-bind ((alloc) s I) (make-P:mt b Ib))))]
             [else ςs])] ;; XXX: raise error
      [(I:do-join tl Ib)
       (define cl-l (term-is-context-like? tl))
       (define cl-r (term-is-context-like? t))
       (define nc-l (no-contexts? tl))
       (define nc-r (no-contexts? t))
       (define addr ((alloc) s I))
       ;; C t  ^ no-ctxts t
       (when (and (set-member? cl-l #t) (set-member? nc-r #t))
         (σ-bind addr (alloc-term addr make-term:left tl t)))
       ;; t C  ^ no-ctxts t
       (when (and (set-member? cl-r #t) (set-member? nc-l #t))
         (σ-bind addr (alloc-term addr make-term:right tl t)))
       ;; otherwise
       (when (and (or (set-member? cl-r #f) (set-member? nc-l #f))
                  (or (set-member? cl-l #f) (set-member? nc-r #f)))
         (σ-bind addr (alloc-term addr make-term:cons tl t)))
       (set-add ςs (make-state:Iapply addr b Ib))]
      ;; TODO: break into several steps if we know the metafunction
      ;; is just another reduction relation (but a functional one)
      [(I:meta-app f '() tdone I)
       (set-add ςs (make-state:Iapply (apply f (reverse (cons t tdone))) b I))]
      [(I:meta-app f (cons r rs) tdone Ib)
       (define Ic ((alloc) s I))
       (define I′ (make-I:meta-app f rs (cons t tdone) Ib))
       (set-add ςs (make-state:Ieval r b (σ-bind Ic I′)))]
      [err (error 'step-inst-apply "bad match ~a" err)])))

(define (step-plug-eval s)
  (match-define (state:Peval C t Pa) s)
  (for/set ([C* (resolve-term/context C)])
    (define Pb ((alloc) s C*))
    (match C*
      [(context:hole) (make-state:Papply t Pa)]
      [(context:left Cl tr)
       (define cl-t (term-is-context-like? t))
       (when (set-member? cl-t #t) (σ-bind Pb (make-P:left-context tr Pa)))
       (when (set-member? cl-t #f) (σ-bind Pb (make-P:left-term tr Pa)))
       (make-state:Peval Cl t Pb)]
      [(context:right tl Cr)
       (define cl-t (term-is-context-like? t))
       (when (set-member? cl-t #t) (σ-bind Pb (make-P:right-context tl Pa)))
       (when (set-member? cl-t #f) (σ-bind Pb (make-P:right-term tl Pa)))
       (make-state:Peval Cr t Pb)]
      [err (error 'step-plug-eval "bad match ~a" err)])))

(define (step-plug-apply s)
  (match-define (state:Papply t Pa) s)
  (for/set ([P (σ-lookup Pa)])
    (define ta ((alloc) s P))
    (match P
      [(P:mt b Ia) (make-state:Iapply t b Ia)]
      [_
       (match P
         [(P:left-context tr P)  (σ-bind ta (alloc-term ta make-term:left t tr))]
         [(P:left-term tr P)     (σ-bind ta (alloc-term ta make-term:cons t tr))]
         [(P:right-context tl P) (σ-bind ta (alloc-term ta make-term:right tl t))]
         [(P:right-term tl P)    (σ-bind ta (alloc-term ta make-term:cons tl t))]
         [err (error 'step-plug-apply "bad match ~a" err)])
       (make-state:Papply ta Pa)])))

;; concrete allocation
(define (base-alloc s [extra #f])
  (match s
    [(? state:Meval?) (Mℓ (gensym))]
    [(? state:Mapply?)
     (match extra
       [(? M:mt?) (Iℓ (gensym))]
       [(? M:combine?) (Aℓ (gensym))]
       [(? M:select?) (cℓ (gensym))]
       [_ (Mℓ (gensym))])]
    [(? state:Aeval?) (Aℓ (gensym))]
    [(? state:Aapply?) (cℓ (gensym))]
    [(? state:Ieval?) (Iℓ (gensym))]
    [(? state:Iapply?)
     (match extra
       [(? rewrite?) (Mℓ (gensym))]
       [(? I:do-plug?) (Pℓ (gensym))]
       [(? I:do-join?) (tℓ (gensym))]
       [_ (Iℓ (gensym))])]
    [(? state:Peval?) (Pℓ (gensym))]
    [(? state:Papply?) (tℓ (gensym))]
    [err (error 'base-alloc "bad match ~a" err)]))

;; get all starting terms.
(define (inject term)
  (define ΔW (make-hash))
  (define Ia₀ (Iℓ (gensym)))
  (σ-bind Ia₀ *I:mt)
  (for ([ς (step-inst-apply (make-state:Iapply term ⊥eq Ia₀))])
    (hash-set! ΔW ς #t))
  ΔW)

(define-syntax-rule (with-language-semantics (grammar semantics) expr1 exprs ...)
  (parameterize ([G grammar] [S semantics] [σ ⊥] [alloc base-alloc]) expr1 exprs ...))

(define (apply-reduction-relation ΔW [W (make-hash)])
  (define Final (make-hash))
  (define Stuck (make-hash))

  ;; Add ς to the work set (and the seen set)
  (define (todo ς)
    (unless (hash-has-key? W ς)
      (hash-set! W ς #t)
      (hash-set! ΔW ς #t)))

  (let loop () ;; for monotone state updates. Doesn't work for GC.
    (define ς (for/first ([(k _) (in-hash ΔW)]) k))
    (cond [ς
           (cond [(final-state? ς) (hash-set! Final ς #t)]
                 [else (define succ (step ς))
                       (cond [(set-empty? succ)
                              (hash-set! Stuck ς #t)]
                             [else (for ([ς′ (in-set succ)])
                                     (todo ς′))])])
           (hash-remove! ΔW ς)
           (loop)]
          [else (list Final Stuck)])))

(define (apply-reduction-relation* term)
  (define ΔW (inject term))
  (define W (hash-copy ΔW))
  (define steps (make-hash))
  (define all-stuck (make-hash))

  (let loop ()
    (match-define (list final stuck) (apply-reduction-relation ΔW W))
    (for ([(k _ ) (in-hash stuck)])
      (hash-set! all-stuck k #t))
    ;; loop if there is a step we haven't taken yet.
    (cond [(for/or ([(ς _) (in-hash final)]
                    #:unless (hash-has-key? steps ς))
             (hash-set! steps ς #t)
             (for ([ς′ (step-inst-apply ς)])
               (printf "Next step:~%") (pretty-print (translate-state ς′))
               (hash-set! ΔW ς′ #t)
               (hash-set! W ς′ #t)))
           (loop)]
          [else (list all-stuck steps)])))
