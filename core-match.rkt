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

(define-ADT r;ewrite rule
  [hole ()]
  [atom ([a atom/c])]
  [var ([x variable?])]
  ;; a distinguishing feature of this semantics from the APLOS paper
  ;; is that metafunctions may take multiple arguments. This allows
  ;; us to have non-lossy treatments of a designated number of arguments.
  [app ([f procedure?]
        [rs (listof r)])]
  [in-hole ([rc r] [rh r])]
  [cons ([car r] [cdr r])])

;; a semantics is a set of rewrite rules.
;; a rewrite rule applies to a term if a pattern in the matches it,
;; and that pattern's corresponding rewrite is defined on the match's result.
(define-struct/contract rewrite ([p pattern/c] [r r/c]))
(define semantics/c (set/c rewrite?))
