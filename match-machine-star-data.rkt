#lang racket

(require "macros.rkt")
(provide (all-defined-out))

(define nonterminal? symbol?)
(define variable? symbol?)
(define atom/c any/c)
(define ∅ (set))
(define ⊥eq #hasheq())
(define ⊥ #hash())
(define ∪ set-union)

;; Grammar and semantics of the language don't change, so
;; don't include them in the machine states.
(define G (make-parameter #f))
(define S (make-parameter #f))
;; global store grows monotonically.
(define σ (make-parameter #f))
;; alloc : state [extra ...] -> addr + #f
(define alloc (make-parameter #f))

(define (follow-nt n)
  (hash-ref (G) n (λ () (error 'follow-nt "Unknown nonterminal ~a" n))))
(define (σ-lookup addr)
  (hash-ref (σ) addr (λ () (error 'σ-lookup "Address not found ~a" addr))))
(define (σ-bind addr v)
  (σ (hash-set (σ) addr (set-add (hash-ref (σ) addr ∅) v))))

(define-ADT pattern
  [hole ()]
  [name ([x variable?] [p pattern])]
  [nt ([n nonterminal?])]
  [cons ([p₀ pattern] [p₁ pattern])]
  [in-hole ([pc pattern] [ph pattern])]
  [atom ([a atom/c])]
  [datum ([f (-> any/c boolean?)])])
(define *p:hole (pattern:hole))
;; Language Grammar : Relation (Nonterminal × Pattern)
(define language/c (hash/c nonterminal? (set/c pattern/c)))

;; different address spaces. This separation allows us to create "fresh" but
;; still related addresses. e.g. terms that get reinterpreted as contexts may
;; change their addresses from (tℓ a) to (cℓ a).
(define-struct/contract tℓ ([addr any/c]) #:transparent)
  (define-struct/contract tℓ-left ([addr any/c]) #:transparent)
  (define-struct/contract tℓ-right ([addr any/c]) #:transparent)
(define termℓ? (or/c tℓ? tℓ-left? tℓ-right?))
(define-struct/contract cℓ ([addr any/c]) #:transparent)
  (define-struct/contract cℓ-left ([addr any/c]) #:transparent)
  (define-struct/contract cℓ-right ([addr any/c]) #:transparent)
(define contextℓ? (or/c cℓ? cℓ-left? cℓ-right?))
(define-struct/contract Mℓ ([addr any/c]) #:transparent)
(define-struct/contract Aℓ ([addr any/c]) #:transparent)
(define-struct/contract Iℓ ([addr any/c]) #:transparent)
(define-struct/contract Pℓ ([addr any/c]) #:transparent)

(define-struct/contract term:hole () #:transparent)
(define-struct/contract term:atom ([a atom/c]) #:transparent)
(define term-flat/c (or/c term:hole? termℓ? term:atom?))

(define-struct/contract term:left ([C term-flat/c] [t term-flat/c]) #:transparent)
(define-struct/contract term:right ([C term-flat/c] [t term-flat/c]) #:transparent)
(define-struct/contract term:cons ([car term-flat/c] [cdr term-flat/c]) #:transparent)
(define term/c (or/c term-flat/c term:left? term:right? term:cons?))

(define *t:hole (term:hole))
;; bindings : Var ↦ Term
(define b/c (hash/c variable? term/c))

(define-struct/contract context:hole () #:transparent)
(define context-flat/c (or/c context:hole? contextℓ?))
(define-struct/contract context:left ([C context-flat/c] [t term/c]) #:transparent)
(define-struct/contract context:right ([t term/c] [C context-flat/c]) #:transparent)
(define context/c (or/c context-flat/c context:left? context:right?))
(define *c:hole (context:hole))

(define-ADT d;ecomposition
  [context ([C context/c] [t term/c])]
  [· ()])
(define *d:· (d:·))

(define-ADT r;ewrite rule
  [hole ()]
  [atom ([a atom/c])]
  [var ([x variable?])]
  [app ([f (-> term/c term/c)]
        [r r])]
  [in-hole ([rc r] [rh r])]
  [cons ([car r] [cdr r])])

;; a semantics is a set of rewrite rules.
;; a rewrite rule applies to a term if a pattern in the matches it,
;; and that pattern's corresponding rewrite is defined on the match's result.
(define-struct/contract rewrite ([p pattern/c] [r r/c]))
(define semantics/c (set/c rewrite?))
;; a match result can have further decomposition (intermediate) or a complete term,
;; along with the bound names of matched subterms.
(define-struct/contract m #;atch-result ([d d/c] [b b/c]) #:transparent)
(define base-m (make-m *d:· ⊥eq))

;; MATCH CONTEXTS
;; finitely many rewrite rhses for a semantics, so this is fine.
;; when done, apply this rewrite rule (starts instantiation)
(define-struct/contract M:mt ([r r/c]) #:transparent)
;; same for patterns
;; delayed match for right of cons since matching left of cons.
(define-struct/contract M:right ([pr pattern/c]
                                 [tl term/c]
                                 [tr term/c]
                                 [M Mℓ?]) #:transparent)
  ;; delayed selection of match results since matching right of cons.
(define-struct/contract M:select ([tl term/c]
                                  [tr term/c]
                                  [leftdb m?]
                                  [M Mℓ?]) #:transparent)
;; delayed matching of hole since matching context.
(define-struct/contract M:hole ([ph pattern/c] [M Mℓ?]) #:transparent)
;; delayed combining results because matching term in hole.
(define-struct/contract M:combine ([C context/c] [b b/c] [M Mℓ?]) #:transparent)
;; delayed binding name for pattern since matching pattern.
(define-struct/contract M:name ([x variable?] [t term/c] [M Mℓ?]) #:transparent)
;; delay throwing away intermediate bindings since recursively parsing.
(define-struct/contract M:nt ([M Mℓ?]) #:transparent)

;; APPEND CONTEXTS
;; done appending, go back to matching
(define-struct/contract A:mt ([M Mℓ?]) #:transparent)
  ;; delaying creating left context frame since appending left contexts.
(define-struct/contract A:left ([t term/c] [A Aℓ?]) #:transparent)
  ;; delaying creating right context frame since appending right contexts.
(define-struct/contract A:right ([t term/c] [A Aℓ?]) #:transparent)

;; INSTANTIATE CONTEXTS
;; Plug it back in to start matching after instantiation is done.
(define-struct/contract I:mt () #:transparent) (define *I:mt (I:mt))
(define-struct/contract I:plug-right ([r r/c] [I Iℓ?]) #:transparent)
(define-struct/contract I:do-plug ([tc term/c] [I Iℓ?]) #:transparent)
(define-struct/contract I:join-right ([r r/c] [I Iℓ?]) #:transparent)
(define-struct/contract I:do-join ([tl term/c] [I Iℓ?]) #:transparent)
(define-struct/contract I:meta-app ([f (-> term/c term/c)] [I Iℓ?]) #:transparent)

;; PLUG CONTEXTS
;; when done plugging, we go back to instantiation
(define-struct/contract P:mt ([b b/c] [I Iℓ?]) #:transparent)
(define-struct/contract P:left-context ([tr term/c] [P Pℓ?]) #:transparent)
(define-struct/contract P:left-term ([tr term/c] [P Pℓ?]) #:transparent)
(define-struct/contract P:right-context ([tl term/c] [P Pℓ?]) #:transparent)
(define-struct/contract P:right-term ([tl term/c] [P Pℓ?]) #:transparent)

;; Redex's semantics follows a match/instantiate pattern that
;; use two recursive helper functions (append & plug).
;; We flatten out this recursion and implement each recursive function
;; with eval/apply states.
(define-struct/contract state:Meval ([p pattern/c] [t term/c] [M Mℓ?]) #:transparent)
(define-struct/contract state:Mapply ([db m?] [M Mℓ?]) #:transparent)
(define-struct/contract state:Aeval ([Cl context/c]
                                     [Cr context/c]
                                     [t term/c]
                                     [b b/c]
                                     [A Aℓ?]) #:transparent)
(define-struct/contract state:Aapply ([C context/c]
                                      [t term/c]
                                      [b b/c]
                                      [A Aℓ?]) #:transparent)
(define-struct/contract state:Ieval ([r r/c]
                                     [b b/c]
                                     [I Iℓ?]) #:transparent)
(define-struct/contract state:Iapply ([t term/c]
                                      [b b/c]
                                      [I Iℓ?]) #:transparent)
(define-struct/contract state:Peval ([C context/c]
                                     [t term/c]
                                     [P Pℓ?]) #:transparent)
(define-struct/contract state:Papply ([t term/c] [P Pℓ?]) #:transparent)
