#lang racket

(require (for-syntax racket/syntax
                     syntax/parse)
         racket/stxparam
         racket/splicing)
(provide it andit define-ADT)

(define-syntax-parameter it (λ (stx) (raise-syntax-error #f "must be used in andit context" stx)))
(define-syntax-rule (andit e es ...)
  (let ([x e])
    (syntax-parameterize ([it (make-rename-transformer #'x)])
      (and x es ...))))
;; hide "recursive-contract" and a bunch of cruft
(define-syntax (define-ADT stx)
  (define-syntax-class ADT
    (pattern name:id
             #:with shallow (format-id stx "~a?" #'name)
             #:with contract (format-id stx "~a/c" #'name)
             #:with matcher (format-id stx "match-~a" #'name)))
  (syntax-parse stx
    [(_ adt:ADT
        [variant:id ([field:id field/c:expr] ...)] ...)
     (define variants (syntax->list #'(variant ...)))
     (define variant-structs (map (λ (id) (format-id stx "~a:~a" (attribute adt.name) id)) variants))
     (define variant? (map (λ (id) (format-id stx "~a?" id)) variant-structs))
     (with-syntax ([(variant-structs ...) variant-structs]
                   [(variant? ...) variant?])
       (syntax/loc stx
         (begin (define adt.contract (recursive-contract (or/c variant? ...) #:chaperone))
                (define-syntax-parameter adt.name (λ (stx) (raise-syntax-error #f "To be used only in define-ADT" stx)))
                (splicing-syntax-parameterize ([adt.name (λ _ #'(recursive-contract adt.contract #:chaperone))])
                  (define-struct/contract variant-structs ([field field/c] ...) #:transparent) ...)
                ;; for quick recognition
                (define (adt.shallow x) (or (variant? x) ...))
                (define-syntax (adt.matcher stx2)
                  (define-syntax-class a-variant
                    #:description "Name of an ADT variant"
                    #:attributes (struct-name)
                    (pattern name:id
                             #:attr struct-name
                                    (cond [(free-identifier=? (attribute name) #'variant)
                                           #'variant-structs] ...
                                           [else #f])
                             #:when (attribute struct-name)))
                  (...
                   (define-splicing-syntax-class match-clauses
                     #:description "Legal match clauses for an ADT"
                     #:attributes ((pats 1))
                     (pattern (~seq [(v:a-variant ps:expr ...) rhs1:expr rhs:expr ...] ...
                                    (~optional [else:id last1:expr last:expr ... (~bind [(oplast 1) (list #'[else last1 last ...])])]
                                               #:defaults ([(oplast 1) null])))
                              #:with (pats ...) #'([(v.struct-name ps ...) rhs1 rhs ...] ... oplast ...))))
                   (...
                    (syntax-parse stx2
                      [(_ e:expr cls:match-clauses)
                       #`(match/derived e #,stx2 cls.pats ...)]))))))]))
