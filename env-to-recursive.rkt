#lang racket

;; translate final results into more readable,
;; recursive data structures here. 
;; (Will only work for concrete semantics since abstract can introduce
;; cycles in the data)
(require "core-match.rkt"
         "match-machine-star-data.rkt"
         (prefix-in o: "match-machine-data.rkt")
         racket/trace)
(provide translate-state translate-term)

(define-syntax match-λ (make-rename-transformer #'match-lambda))

;; concrete semantics should only have one mapping
(define (σ-lookup1 addr)
  (for/first ([k (in-set (σ-lookup addr))]) k))

(define (translate-term t)
  (match t
    [(term:hole) o:*t:hole]
    [(term:atom a) (o:term:atom a)]
    [(or (? tℓ? t) (? tℓ-left? t) (? tℓ-right? t)) 
     (translate-term (σ-lookup1 t))]
    [(app (match-λ [(term:left tl tr) (list o:term:left tl tr)]
                   [(term:right tl tr) (list o:term:right tl tr)]
                   [(term:cons tl tr) (list o:term:cons tl tr)]
                   [_ '()]) 
          (list k tl tr)) 
     (k (translate-term tl) (translate-term tr))]
    [err (error' translate-term "bad match ~a" err)]))

(define (translate-context C)
  (match C
  [(context:hole) o:*c:hole]
  [(context:left C t) 
   (o:context:left (translate-context C) (translate-term t))]
  [(context:right t C)
   (o:context:right (translate-term t) (translate-context C))]
  [(? cℓ? C) (translate-context (σ-lookup1 C))]
  [err (error 'translate-context "bad match ~a" err)]))

(define translate-d
  (match-λ [(d:·) o:*d:·]
           [(d:context C t) 
            (o:d:context (translate-context C) (translate-term t))]
           [err (error 'translate-d "bad match ~a" err)]))

(define (translate-binding b)
  (for/hash ([(var t) (in-hash b)]) (values var (translate-term t))))

(define translate-match-result
  (match-λ [(m d b) (o:m (translate-d d) (translate-binding b))]
           [err (error 'translate-match-result "bad match ~a" err)]))

(define (translate-match M)
  (match M
    [(M:mt r) (o:M:mt r)]
    [(M:right pr tl tr Ma)
     (o:M:right pr (translate-term tl) (translate-term tr) (translate-match Ma))]
    [(? Mℓ? Ma) (translate-match (σ-lookup1 Ma))]
    [(M:select tl tr db Ma)
     (o:M:select (translate-term tl) (translate-term tr) 
                 (translate-match-result db) (translate-match Ma))]
    [(M:hole ph Ma) (o:M:hole ph (translate-match Ma))]
    [(M:combine C b Ma) 
     (o:M:combine (translate-context C) (translate-binding b) (translate-match Ma))]
    [(M:name x t Ma) (o:M:name x (translate-term t) (translate-match Ma))]
    [(M:nt Ma) (o:M:nt (translate-match Ma))]
    [err (error 'translate-match "bad match ~a" err)]))

(define (translate-append A)
  (match A
    [(A:mt Ma) (o:A:mt (translate-match Ma))]
    [(A:left t Aa) (o:A:left (translate-term t) (translate-append Aa))]
    [(A:right t Aa) (o:A:right (translate-term t) (translate-append Aa))]
    [(? Aℓ? A) (translate-append (σ-lookup1 A))]
    [err (error 'translate-append "bad match ~a" err)]))

(define (translate-inst I)
  (match I
    [(? Iℓ? I) (translate-inst (σ-lookup1 I))]
    [(I:mt) o:*I:mt]
    [(I:plug-right r Ia) (o:I:plug-right r (translate-inst Ia))]
    [(I:do-plug tc Ia) (o:I:do-plug (translate-term tc) (translate-inst Ia))]
    [(I:join-right r Ia) (o:I:join-right r (translate-inst Ia))]
    [(I:do-join tl Ia) (o:I:do-join (translate-term tl) (translate-inst Ia))]
    [(I:meta-app f rs ts Ia) 
     (o:I:meta-app f rs (map translate-term ts) (translate-inst Ia))]
    [err (error 'translate-inst "bad match ~a" err)]))

(define (translate-plug P)
  (match P
    [(? Pℓ? P) (translate-plug (σ-lookup1 P))]
    [(P:mt b Ia)
     (o:P:mt (translate-binding b) (translate-inst Ia))]
    [(P:left-context tr Pa) 
     (o:P:left-context (translate-term tr) (translate-plug Pa))]
    [(P:left-term tr Pa)
     (o:P:left-term (translate-term tr) (translate-plug Pa))]
    [(P:right-context tl Pa)
     (o:P:right-context (translate-term tl) (translate-plug Pa))]
    [(P:right-term tl Pa)
     (o:P:right-term (translate-term tl) (translate-plug Pa))]
    [err (error 'translate-plug "bad match ~a" err)]))

(define translate-state
  (match-λ
    [(state:Meval p t Ma) (o:state:Meval p (translate-term t) (translate-match Ma))]
    [(state:Mapply db Ma) (o:state:Mapply (translate-match-result db)
                                          (translate-match Ma))]
    [(state:Aeval Cl Cr t b Aa)
     (o:state:Aeval (translate-context Cl) (translate-context Cr)
                    (translate-term t) (translate-binding b)
                    (translate-append Aa))]
    [(state:Aapply C t b Aa) 
     (o:state:Aapply (translate-context C) (translate-term t)
                     (translate-binding b) (translate-append Aa))]
    [(state:Ieval r b Ia)
     (o:state:Ieval r (translate-binding b) (translate-inst Ia))]
    [(state:Iapply t b Ia)
     (o:state:Iapply (translate-term t) (translate-binding b) (translate-inst Ia))]
    [(state:Peval C t Pa)
     (o:state:Peval (translate-context C) (translate-term t) (translate-plug Pa))]
    [(state:Papply t Pa)
     (o:state:Papply (translate-term t) (translate-plug Pa))]
    [err (error 'translate-state "bad match ~a" err)]))
#;
(trace translate-state translate-plug translate-inst translate-append translate-match
       translate-d translate-binding translate-match-result 
       translate-term
       translate-context)