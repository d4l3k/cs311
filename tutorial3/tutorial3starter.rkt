;; CPSC 311
;; Alec Thériault & Khurram Jafery
;; Tuesday tutorials: T1C and T1D

#lang plai

;; Problem 1

#|
BNF of expressions with Let and functions (as presented in class) extended with +-nary:

  <E> ::= <num>
        | {+ <E> <E>}
        | {- <E> <E>}
        | <symbol>
        | {Let <symbol> <E> <E>}
        | {Lam <symbol> <E>}
        | {App <E> <E>}
        | {+-nary <E> <E> ...}

The `...`  are read as one or more occurrences of the preceding nonterminal.
|#

;; Abstract syntax of expressions (as presented in class):
(define-type E
  [Num (n number?)]
  [Add (lhs E?) (rhs E?)]
  [Sub (lhs E?) (rhs E?)]
  [Id  (x symbol?)]
  [Let (x symbol?) (bound-expr E?) (body E?)]
  [Lam (name symbol?) (body E?)]
  [App (function E?) (argument E?)]
  ;[Nary-Add ...]
  )

;; parse : s-expression -> E?
;; parser for expressions (as presented in class)
(define (parse sexp)
  (cond
    [(number? sexp) (Num sexp)]
    [(symbol? sexp) (Id  sexp)]
    [(list? sexp)   (case (first sexp)
                      [(+) (if (= (length sexp) 3)
                               (Add (parse (second sexp)) (parse (third sexp)))
                               (error "parse: + needs exactly 2 arguments"))]
                      [(-) (if (= (length sexp) 3)
                               (Sub (parse (second sexp)) (parse (third sexp)))
                               (error "parse: - needs exactly 2 arguments"))]
                      [(Let) (if (= (length sexp) 4)
                                 (if (not (symbol? (second sexp)))
                                     (error "parse: Let needs a symbol")
                                     (Let (second sexp)
                                          (parse (third sexp))
                                          (parse (fourth sexp))))
                                 (error "parse: Let needs exactly 3 arguments"))]
                      [(Lam) (if (= (length sexp) 3)
                                 (if (not (symbol? (second sexp)))
                                     (error "parse: Lam needs a symbol")
                                     (Lam (second sexp) (parse (third sexp))))
                                 (error "parse: Lam needs exactly 2 arguments"))]
                      [(App) (if (= (length sexp) 3)
                                 (App (parse (second sexp)) (parse (third sexp)))
                                 (error "parse: App needs exactly 2 arguments"))]
                      ;[(+-nary) (...)]
                      [else (error "parse: I only understand +, -, Let, Lam, and App")])]
    [else (error "parse: syntax error")]))

;; interp : E? -> E? 
;; interpreter for expressions (as presented in class)
(define (interp e)
  (type-case E e
    [Num (n) (Num n)]
    
    [Add (e1 e2) (type-case E (interp e1)
                   [Num (n1) (type-case E (interp e2)
                               [Num (n2) (Num (+ n1 n2))]
                               [else (error "interp: Add on non-number")])]
                   [else (error "interp: Add on non-number")])]
    
    [Sub (e1 e2) (type-case E (interp e1)
                   [Num (n1) (type-case E (interp e2)
                               [Num (n2) (Num (- n1 n2))]
                               [else (error "interp: Sub on non-number")])]
                   [else (error "interp: Sub on non-number")])]
    
    [Id (x) (error "interp: free-variable-error " x)]
    
    [Let (x e1 e2) (let* ([v1 (interp e1)]
                          [v2 (interp (subst v1 x e2))])
                     v2)]
    
    [Lam (x body) (Lam x body)]
    
    #|
    ;; expression strategy
    [App (e1 e2) (let ([v1 (interp e1)])
                   (type-case E v1
                     [Lam (x body) (let ([v (interp (subst e2 x body))])
                                     v)]
                     [else (error "interp: applied non-function")]))]
    |#
    
    ;; value strategy
    [App (e1 e2) (let ([v1 (interp e1)]
                       [v2 (interp e2)])
                   (type-case E v1
                     [Lam (x body) (let ([v (interp (subst v2 x body))])
                                     v)]
                     [else (error "interp: applied non-function")]))]
    #|

         e1 ⇓ (Num n1)    e2 ⇓ (Num n2)
      ---------------------------------------- Eval-+nary-base
        (Nary-Add (e1 e2)) ⇓ (Num (n1 + n2))


         e1 ⇓ (Num n1)     (Nary-Add (e2 ... ek)) ⇓ (Num n2)
      ---------------------------------------------------------- Eval-+nary-rec
              (Nary-Add (e1 e2 ... ek)) ⇓ (Num (n1 + n2))

    |#
    
    ;[Nary-Add ...]
    ))

;; subst : E? symbol? E? -> E?
;; substiution function for expressions (as presented in class)
;; it reads substitute v for x in e
(define (subst v x e)
  (type-case E e
    [Num (n) (Num n)]
    [Add (e1 e2) (Add (subst v x e1) (subst v x e2))]
    [Sub (e1 e2) (Sub (subst v x e1) (subst v x e2))]
    [Id (y) (if (symbol=? x y)
                v
                (Id y))]
    [Let (y e1 e2) (if (symbol=? x y)
                       (Let y (subst v x e1) e2)
                       (Let y (subst v x e1) (subst v x e2)))]
    [Lam (y body) (if (symbol=? x y)
                      (Lam y body)
                      (Lam y (subst v x body)))]
    [App (e1 e2) (App (subst v x e1) (subst v x e2))]
    ;[Nary-Add ...]
    ))

;; Problem 2

#|
Given an expression e, we want to write a function called `unparse` that turns e back into an
s-expression. Having an unparse function, will allow us to map back and forth between the concrete
syntax of our language and the abstract syntax of our language!

For the moment, `parse` and `unparse` will be inverse operations i.e. if `(parse sexp)` returns e,
then `(unparse e)` returns sexp, in otherwords (equal? (unparse (parse sexp)) sexp) is true. But as
our language grows and evolves, due to subtleties this may no longer be the case. Check Problem 4!

Also note that Racket turns all different kinds of brackets such as square brackets [] and braces {}
into parantheses (). For example, when we run '{+ 1 2} we get back '(+ 1 2).
|#

;; unparse : E -> sexp
;; unparser for abstract expressions                 
(define (unparse e)
  (type-case E e
    [Num (n)       n]
    [Add (e1 e2)   (list '+ (unparse e1) (unparse e2))] 
    ;; The rest of unparse uses "quasiquote" ("`...") and "unquote" (",...").
    ;; This is either a cute trick or a "crown jewel" of Racket,
    ;; depending on your taste.
    ;;
    ;; This is how we would write the Add branch using quasiquote/unquote:
    ;; [Add (e1 e2)               `(+ ,(unparse e1) ,(unparse e2))]
    ;;
    [Sub (e1 e2)   `(- ,(unparse e1) ,(unparse e2))]
    [Id  (x)        x]
    ;[Let (x e body) ]
    ;[Lam (name body)]
    ;[App (f arg) ]
    ;[Nary-Add (args) (cons '+-nary (map unparse args))]
    [else (error "not implemented yet")]
    ))

;; Problem 3

#|
Let's extend the `+` and `-` operations to support at least two arguments!
The BNF would now look something like:

  <E> ::= <num>
        | {+ <E> <E> ...}
        | {- <E> <E> ...}
        | <symbol>
        | {Let <symbol> <E> <E>}
        | {Lam <symbol> <E>}
        | {App <E> <E>}
        | {+-nary <E> <E> ...}

The `...`  are read as one or more occurrences of the preceding nonterminal.

Note that that Racket opeation `+` supports zero or more arguments but the case where either zero
or one argument is passed to `+` it requires special handling, hence we do not consider it for the
AE language. Similarly, the Racket operation `-` supports one (not zero!) or more arguments but we
do not consider it for our language.

To add `+` and `-` operations that support at least two arguments, we have the option of either
updating the abstract syntax and evaluation rules, or add them as `syntactic sugar` in terms of our
current abstract syntax. For our purposes, the easiest approach is to treat them as syntactic sugar
and adapt our parser to handle them.
|#

;; Examples of new arithmetic expressions allowed in concrete syntax
(define AE1 '{+ 1 2 3})
(define AE2 '{- 1 2 3})
(define AE3 '{- {+ 1 2 3} 2})
(define AE4 '{- {+ 1 2 3} 2 3})

;; Examples of arithmetic expressions in abstract syntax
(define PAE1 (Add (Add (Num 1) (Num 2)) (Num 3)))
(define PAE2 (Sub (Sub (Num 1) (Num 2)) (Num 3)))
(define PAE3 (Sub (Add (Add (Num 1) (Num 2)) (Num 3)) (Num 2)))
(define PAE4 (Sub (Sub (Add (Add (Num 1) (Num 2)) (Num 3)) (Num 2)) (Num 3)))

;; New functionality tests for parse
(test (parse AE1) PAE1)
(test (parse AE2) PAE2)
(test (parse AE3) PAE3)
(test (parse AE4) PAE4)

;; New functionality tests for interp-
(test (interp PAE1) (Num  6))
(test (interp PAE2) (Num -4))
(test (interp PAE3) (Num  4))
(test (interp PAE4) (Num  1))

;; Problem 4 (Optional)

#|
In Problem 3, we extended the `+` and `-` operations to support at least two arguments. By treating
them as syntactic sugar, we lost a one-to-one mapping between our concrete syntax and abstract syntax.
For example, `(unparse PAE1) does not return AE1 bur rather '(+ (+ 1 2) 3). Extend the unparser to
handle such n-ary `+` and `-` cases.  
|#