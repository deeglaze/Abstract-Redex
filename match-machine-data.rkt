#lang racket

(require "macros.rkt")
(provide (all-defined-out))

(define nonterminal? symbol?)
(define variable? symbol?)
(define atom/c (or/c symbol? number? null?))
(define ∅ (set))
(define ⊥eq #hasheq())
(define ∪ set-union)

;; Grammar and semantics of the language don't change, so
;; don't include them in the machine states.
(define G (make-parameter #f))
(define S (make-parameter #f))

(define-ADT pattern
  [hole ()]
  [name ([x variable?] [p pattern])]
  [nt ([n nonterminal?])]
  [cons ([p₀ pattern] [p₁ pattern])]
  [in-hole ([pc pattern] [ph pattern])]
#;[finite-map ([pdom pattern]
               [pcodom pattern])]
  [atom ([a atom/c])]
  [datum ([f (-> any/c boolean?)])])
(define *p:hole (pattern:hole))
;; Language Grammar : Relation (Nonterminal × Pattern)
(define language/c (hash/c nonterminal? (set/c pattern/c)))

(define-ADT term
  [hole ()]
  [left  ([C term] [t term])]
  [right ([C term] [t term])]
  [cons  ([C term] [t term])]
#;[finite-map ([f (hash/c term term)])]
  [atom ([a atom/c])])
(define *t:hole (term:hole))
;; bindings : Var ↦ Term
(define b/c (hash/c variable? term/c))

(define-ADT context
  [hole ()]
  [left ([C context] [t term/c])]
  [right ([t term/c] [C context])])
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
  [map-add ([rmap r] [rkey r] [rval r])]
  [map-lookup ([rmap r] [rkey r])]
  [cons ([car r] [cdr r])])
;; a semantics is a set of rewrite rules.
;; a rewrite rule applies to a term if a pattern in the matches it,
;; and that pattern's corresponding rewrite is defined on the match's result.
(define-struct/contract rewrite ([p pattern/c] [r r/c]))
(define semantics/c (set/c rewrite?))
;; a match result can have further decomposition (intermediate) or a complete term,
;; along with the bound names of matched subterms.
(define-struct/contract m #;atch-result ([d d/c] [b b/c]) #:transparent)
(define term-constructor/c (or/c 'cons 'left 'right)) ;; following the APLOS paper

(define-ADT M;atch context
  ;; when done, apply this rewrite rule (starts instantiation)
  [mt ([r r/c])]
  ;; delayed match for right of cons since matching left of cons.
  [right ([pr pattern/c]
          [tl term/c]
          [tr term/c]
          [k term-constructor/c]
          [M M])]
  ;; delayed selection of match results since matching right of cons.
  [select ([tl term/c]
           [tr term/c]
           [k term-constructor/c]
           [leftdb m?]
           [M M])]
  ;; delayed matching of hole since matching context.
  [hole ([ph pattern/c] [M M])]
  ;; delayed combining results because matching term in hole.
  [combine ([C context/c] [b b/c] [M M])]
  ;; delayed binding name for pattern since matching pattern.
  [name ([x variable?] [t term/c] [M M])]
  ;; delayed matching a finite function
#;  [codomain]
  ;; delay throwing away intermediate bindings since recursively parsing.
  [nt ([M M])])

(define-ADT A;ppend context
  ;; done appending, go back to matching
  [mt ([M M/c])]
  ;; delaying creating left context frame since appending left contexts.
  [left ([t term/c] [A A])]
  ;; delaying creating right context frame since appending right contexts.
  [right ([t term/c] [A A])])

(define-ADT I;nstantiate context
  ;; instantiation doesn't need to know the language.
  ;; Plug it back in to start matching after instantiation is done.
  [mt ()]
  [plug-right ([r r/c]
               [I I])]
  [do-plug ([tc term/c]
            [I I])]
  [join-right ([r r/c]
               [I I])]
  [do-join ([tl term/c]
            [I I])]
#|
  [add-key/value ([rkey r/c]
                  [rval r/c]
                  [I I])]
  [add-value ([tmap term/c]
              [rval r/c]
              [I I])]
  [add ([tmap term/c]
        [tkey term/c]
        [I I])]
  [lookup-key ([rkey r/c]
               [I I])]
  [lookup ([tmap term/c]
           [I I])]
|#
  [meta-app ([f (-> term/c term/c)]
             [I I])])

(define-ADT P;lug context
  ;; when done plugging, we go back to instantiation
  [mt ([b b/c] [I I/c])]
  [left-context ([tr term/c] [P P])]
  [left-term ([tr term/c] [P P])]
  [right-context ([tl term/c] [P P])]
  [right-term ([tl term/c] [P P])])

;; Redex's semantics follows a match/instantiate pattern that
;; use two recursive helper functions (append & plug).
;; We flatten out this recursion and implement each recursive function
;; with eval/apply states.
(define-ADT state
  [Meval ([p pattern/c]
          [t term/c]
          [M M/c])]
  [Mapply ([db m?]
           [M M/c])]
  [Aeval ([Cl context/c]
          [Cr context/c]
          [t term/c]
          [b b/c]
          [A A/c])]
  [Aapply ([C context/c]
           [t term/c]
           [b b/c]
           [A A/c])]
  [Ieval ([r r/c]
          [b b/c]
          [I I/c])]
  [Iapply ([t term/c]
           [b b/c]
           [I I/c])]
  [Peval ([C context/c]
          [t term/c]
          [P P/c])]
  [Papply ([t term/c]
           [P P/c])])