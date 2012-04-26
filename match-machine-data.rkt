#lang racket

(require "macros.rkt"
         "core-match.rkt")
(provide (all-defined-out)
         (all-from-out "core-match.rkt"))

(define-ADT term
  [hole ()]
  [left  ([C term] [t term])]
  [right ([C term] [t term])]
  [cons  ([C term] [t term])]
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

;; a match result can have further decomposition (intermediate) or a complete term,
;; along with the bound names of matched subterms.
(define-struct/contract m #;atch-result ([d d/c] [b b/c]) #:transparent)

(define-ADT M;atch context
  ;; when done, apply this rewrite rule (starts instantiation)
  [mt ([r r/c])]
  ;; delayed match for right of cons since matching left of cons.
  [right ([pr pattern/c]
          [tl term/c]
          [tr term/c]
          [M M])]
  ;; delayed selection of match results since matching right of cons.
  [select ([tl term/c]
           [tr term/c]
           [leftdb m?]
           [M M])]
  ;; delayed matching of hole since matching context.
  [hole ([ph pattern/c] [M M])]
  ;; delayed combining results because matching term in hole.
  [combine ([C context/c] [b b/c] [M M])]
  ;; delayed binding name for pattern since matching pattern.
  [name ([x variable?] [t term/c] [M M])]
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
  [meta-app ([f procedure?]
             [args-left (listof r/c)]
             [args-done (listof term/c)]
             [I I])])
(define *I:mt (I:mt))

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
