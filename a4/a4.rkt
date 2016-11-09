#lang plai

; a4.rkt
; CPSC 311 2016W1 assignment 4

; This file implements a _small-step_ semantics that, unlike big-step semantics,
; is relatively easy to extend with (simulated) parallelism and nondeterminism.

; BNF of the version of Fun used in this file:
;
;  <E> ::= <num>
;        | <symbol>
;        | {+ <E> <E>}
;        | {- <E> <E>}
;        | {= <E> <E>}
;        | {< <E> <E>}
;        | {Let <symbol> <E> <E>}
;        | {Lam <symbol> <E>}
;        | {App <E> <E>}
;        | {Rec <symbol> <E>}
;        | {Let* <Binding>... <E>}     -----> syntactic sugar for Let
;                           ^
;                           zero or more
;        | Btrue
;        | Bfalse
;        | {Ite <E> <E> <E>}    ; "if-then-else"
;        | {Pair <E> <E>}
;        | {Pair-case <E> {<symbol> <symbol> => <E>}}
;
;        | {Leaf}                    ; leaf node of tree
;        | {Branch <E> <E> <E>}      ; branch node: key, left child, right child
;        | {Tree-case <E> {Leaf => <E>} {Branch <symbol> <symbol> <symbol> => <E>}}
;
;        | {Par <E> <E>}        ; new in a4
;        | {Choose <E> <E>}     ; new in a4
;
;        | Unit                 ; new in a4
;        | {Inl <E>}            ; new in a4
;        | {Inr <E>}            ; new in a4
;        | {Sum-case <E> {Inl <symbol> => <E>} {Inr <symbol> => <E>}}   ; new in a4
;        | {Inl-case <E> {Inl <symbol> => <E>}}                         ; new in a4
;        | {Inr-case <E> {Inr <symbol> => <E>}}                         ; new in a4
;
; Note that there are no types in expressions (Lam, Rec, Leaf).
; This demonstrates that Fun types are not being used in the dynamic semantics.
; Later in 311, we'll see how to make type-checking work even when we
;  don't write (most of) those types.

; Abstract syntax of binary operators:
(define-type Op
  [Plusop]
  [Minusop]
  [Equalsop]
  [Lessthanop])

; Abstract syntax of expressions:
(define-type E
  [Num (n number?)]
  [Binop (op Op?) (lhs E?) (rhs E?)]
  [Let (name symbol?) (named-expr E?) (body E?)]
  [Id (name symbol?)]

  [Bfalse]
  [Btrue]
  [Ite (scrutinee E?) (then-branch E?) (else-branch E?)]

  [Lam (name symbol?)                (body E?)]
  [App (function E?) (argument E?)]
  [Rec (name symbol?)                   (body E?)]

  ; pairs
  [Pair (left E?) (right E?)]
  [Pair-case (scrutinee E?) (name1 symbol?) (name2 symbol?) (body E?)]

  ; trees
  [Leaf]
  [Branch (key E?) (left E?) (right E?)]
  [Tree-case  (scrutinee E?)
              (leaf-branch E?)
              (key symbol?) (left symbol?) (right symbol?) (branch-branch E?)]

  ; unit
  [Unit]

  ; sums
  [Inl (contents E?)]
  [Inr (contents E?)]
  [Sum-case  (scrutinee E?)
             (left-contents symbol?)  (left-branch E?)
             (right-contents symbol?) (right-branch E?)]
  [Inl-case (scrutinee E?)
            (left-contents symbol?)  (left-branch E?)]
  [Inr-case (scrutinee E?)
            (right-contents symbol?)  (right-branch E?)]

  ; nondeterminism
  [Par    (lhs E?) (rhs E?)]   ; new in a4
  [Choose (lhs E?) (rhs E?)]   ; new in a4

  ; Do *not* add variants to this definition! (unless you're doing a bonus problem)
  )

; parse : sexp -> E
;
; Parser for Fun expressions
(define (parse sexp)
  (cond
    [(number? sexp) (Num sexp)]

    [(symbol? sexp)
     (case sexp
       [(Bfalse) (Bfalse)]
       [(Btrue)  (Btrue)]
       [(Unit)   (Unit)]
       [else     (Id sexp)])]

    [(list? sexp)
     (let* ([head      (first sexp)]
            [args      (rest sexp)]
            [arg-count (length args)])
       (case head
         ; {+ sexp1 sexp2}
         ;  ^ ^^^^^^^^^^^ args
         ; head
         [(+ - = <) (if (= arg-count 2)
                        (Binop (parse-op head) (parse (first args)) (parse (second args)))
                        (error "parse: operators need exactly 2 arguments"))]

         [(Par) (if (= arg-count 2)
                    (Par (parse (first args)) (parse (second args)))
                    (error "parse: par needs exactly 2 arguments"))]

         [(Choose) (if (= arg-count 2)
                       (Choose (parse (first args)) (parse (second args)))
                       (error "parse: choose needs exactly 2 arguments"))]

         [(Let*) (case arg-count
                   [(0)  (error "parse: Let* with no body")]
                   [(1)  (parse (first args))]
                   [else ; arg-count >= 2
                    (let ([binding1-sexp (first args)])
                      (if (list? binding1-sexp)
                          (let ([x1-sexp (first binding1-sexp)]
                                [e1-sexp (second binding1-sexp)])
                            (if (symbol? x1-sexp)
                                (Let x1-sexp
                                     (parse e1-sexp)
                                     (parse (cons 'Let* (rest args))))
                                (error "parse: Let* needs a symbol")))
                          (error "parse: each Let* binding must be bracketed")))]
                   )]

         [(Ite) (if (= arg-count 3)
                    (Ite (parse (first args))
                         (parse (second args))
                         (parse (third args)))
                    (error "parse needs exactly 3 arguments"))]

         [(Lam) (cond
                  [(= arg-count 3)  (begin
                                      (printf "I think you're writing a type (~a) in Lam.  I'm ignoring it.~n" (second args))
                                      ; This is basically like syntactic sugar: I'm turning invalid input
                                      ;  (Lam with a type) into valid input (Lam without a type),
                                      ;  then feeding that back into `parse'.
                                      (parse (list 'Lam (first args) (third args))))]
                  [(= arg-count 2)  (if (symbol? (first args))
                                        (Lam (first args) (parse (second args)))
                                        (error "parse: Lam must be followed by an identifier"))]
                  [else (error "parse: malformed `Lam'")])]

         [(App) (if (= arg-count 2)
                    (App (parse (first args)) (parse (second args)))
                    (error "parse: App needs 1 function and 1 argument"))]

         [(Rec) (cond
                  [(= arg-count 3)  (begin
                                      (printf "I think you're writing a type (~a) in Rec.  I'm ignoring it.~n" (second args))
                                      (parse (list 'Rec (first args) (third args))))]
                  [(= arg-count 2)  (if (symbol? (first args))
                                        (Rec (first args) (parse (second args)))
                                        (error "parse: Rec must be followed by an identifier"))]
                  [else (error "parse: malformed `Rec'")])]

         [(Let) (if (= arg-count 3)
                    (let ([name (first args)]
                          [named-sexp (second args)]
                          [body-sexp  (third args)])
                      (if (symbol? name)
                          (Let name (parse named-sexp) (parse body-sexp))
                          (error "parse: malformed `Let'")))
                    (error "parse: malformed `Let'"))]

         [(Pair) (if (= arg-count 2)
                     (Pair (parse (first args))
                           (parse (second args)))
                     (error "parse: malformed `Pair'"))]

         [(Pair-case) (parse-pair-case arg-count args)]

         [(Inl
           Inr)      (cond
                       [(= arg-count 2)   (begin
                                            (printf "I think you're writing a type (~a) in Inl/Inr.  I'm ignoring it.~n" (first args))
                                            (parse (list head (first args))))]
                       [(= arg-count 1)   (let ([variant (case head
                                                           [(Inl) Inl]
                                                           [(Inr) Inr])])
                                            (variant (parse (first args))))]
                       [else (error "parse: malformed `Leaf'")])]

         [(Sum-case) (parse-sum-case arg-count args)]

         [(Inl-case
           Inr-case) (parse-single-sum-case head
                                            (case head [(Inl-case) 'Inl]
                                                       [(Inr-case) 'Inr])
                                            arg-count
                                            args)]

         [(Leaf)     (cond
                       [(= arg-count 1)   (begin
                                            (printf "I think you're writing a type (~a) in Leaf.  I'm ignoring it.~n" (first args))
                                            (parse (list 'Leaf)))]
                       [(= arg-count 0)   (Leaf)]
                       [else (error "parse: malformed `Leaf'")])]

         [(Branch)   (if (= arg-count 3)
                         (Branch (parse (first args)) (parse (second args)) (parse (third args)))
                         (error "parse: malformed `Branch'"))]

         [(Tree-case) (parse-tree-case arg-count args)]

         [else (error "parse: syntax error")]))]

    [else (error "parse: syntax error")]))


; parse-op : sexp -> Op
;
(define (parse-op sexp)
  (case sexp
    [(+) (Plusop)]
    [(-) (Minusop)]
    [(=) (Equalsop)]
    [(<) (Lessthanop)]
    [else (error "parse-op: unknown operator")]
    ))

; parse-pair-case : positive-integer (listof sexp) -> E
;
(define (parse-pair-case arg-count args)
  (if (= arg-count 2)

      (let ([scrutinee (parse (first args))]
            [inner-sexp (second args)])

        (if (and (list? inner-sexp)
                 (= (length inner-sexp) 4)
                 (symbol? (first inner-sexp))
                 (symbol? (second inner-sexp))
                 (symbol=? (third inner-sexp) '=>))

            (let ([name1 (first inner-sexp)]
                  [name2 (second inner-sexp)]
                  [body (parse (fourth inner-sexp))])

              (Pair-case scrutinee name1 name2 body))

            (error "parse: malformed `Pair-case'")))

      (error "parse: malformed `Pair-case'")))

; parse-tree-case : positive-integer (listof sexp) -> E
;
(define (parse-tree-case arg-count args)
  (if (= arg-count 3)

      (let ([scrutinee (parse (first args))]
            [leaf-branch-sexp (second args)]
            [branch-branch-sexp (third args)]
            )

        (if (and (list? leaf-branch-sexp)
                 (= (length leaf-branch-sexp) 3)
                 (symbol=? (first leaf-branch-sexp) 'Leaf)
                 (symbol=? (second leaf-branch-sexp) '=>))

            (let ([leaf-branch (parse (third leaf-branch-sexp))])

              (if (and (list? branch-branch-sexp)
                       (= (length branch-branch-sexp) 6)
                       (symbol=? (first branch-branch-sexp) 'Branch)
                       (symbol? (second branch-branch-sexp))
                       (symbol? (third branch-branch-sexp))
                       (symbol? (fourth branch-branch-sexp))
                       (symbol=? (fifth branch-branch-sexp) '=>))

                  (let ([xKey (second branch-branch-sexp)]
                        [xL (third branch-branch-sexp)]
                        [xR (fourth branch-branch-sexp)]
                        [branch-branch (parse (sixth branch-branch-sexp))])

                    (Tree-case scrutinee leaf-branch xKey xL xR branch-branch))
                  (error "parse: malformed `Tree-case'")))
            (error "parse: malformed `Tree-case'")))
      (error "parse: malformed `Tree-case'")))

; valid-sum-branch : symbol sexp -> boolean
;
; (valid-sum-branch 'Inx '{Inx <symbol> => <E>}) = #true

(define (valid-sum-branch injection-name sexp)
  (and (list? sexp)
       (= (length sexp) 4)
       (symbol=? (first sexp) injection-name)
       (symbol? (second sexp))
       (symbol=? (third sexp) '=>)))

; parse-sum-case : positive-integer (listof sexp) -> E
;
(define (parse-sum-case arg-count args)
  (if (= arg-count 3)

      (let ([scrutinee (parse (first args))]
            [inl-branch-sexp (second args)]
            [inr-branch-sexp (third args)])

        (if (and (valid-sum-branch 'Inl inl-branch-sexp)
                 (valid-sum-branch 'Inr inr-branch-sexp))
            (let ([xL (second inl-branch-sexp)]
                  [eL (parse (fourth inl-branch-sexp))]
                  [xR (second inr-branch-sexp)]
                  [eR (parse (fourth inr-branch-sexp))]
                  )
              (Sum-case scrutinee xL eL xR eR))
            (error "parse: malformed `Sum-case'")))
      (error "parse: malformed `Sum-case'")))

; parse-single-sum-case : symbol symbol positive-integer (listof sexp) -> E
;
; Precondition: first argument is either 'Inl-case or 'Inr-case,
;               second argument is either 'Inl or 'Inr
(define (parse-single-sum-case head head-word arg-count args)
  (if (= arg-count 2)

      (let ([scrutinee (parse (first args))]
            [branch-sexp (second args)])

        (if (valid-sum-branch head-word branch-sexp)
            (let ([x (second branch-sexp)]
                  [eBranch (parse (fourth branch-sexp))]
                  )
              ((case head [(Inl-case) Inl-case]
                          [(Inr-case) Inr-case]) scrutinee x eBranch))
            (error "parse: malformed" head)))
      (error "parse: malformed" head)))


; subst : E symbol E -> E
;
; (subst e2 x e1) returns e1 with x replaced by e2.
(define (subst e2 x e1)
  (type-case E e1
    [Num (n) (Num n)]

    [Bfalse () (Bfalse)]

    [Btrue () (Btrue)]

    [Let (y e eB)
         (if (symbol=? x y)
             (Let x (subst e2 x e) eB)
             (Let y (subst e2 x e) (subst e2 x eB)))]

    [Lam (y eB)
         (if (symbol=? x y)
             ; same symbol; if x appears inside eB, it refers to *this*
             ;  binding, not to the x we're replacing, so return same eB
             (Lam x eB)

             ; different symbol; leave y alone and replace inside eB
             (Lam y (subst e2 x eB))
             )]

    [Binop (op eL eR)  (Binop op (subst e2 x eL)   (subst e2 x eR))]
    [App (eFun eArg)   (App      (subst e2 x eFun) (subst e2 x eArg))]
    [Par (eL eR)       (Par      (subst e2 x eL)   (subst e2 x eR))]
    [Choose (eL eR)    (Choose   (subst e2 x eL)   (subst e2 x eR))]

    [Rec (y eB)     ; Rec binds y, so treat it the same way as Lam
         (if (symbol=? x y)
             (Rec x eB)
             (Rec y (subst e2 x eB)))]

    [Ite (e left right)   (Ite (subst e2 x e)
                               (subst e2 x left)
                               (subst e2 x right))]
    [Id (y)
        (if (symbol=? x y)
            e2
            (Id y))]

    [Pair (left right)   (Pair (subst e2 x left) (subst e2 x right))]
    [Pair-case (scrutinee name1 name2 body)

               (Pair-case (subst e2 x scrutinee) name1 name2
                          (if (or (symbol=? x name1) (symbol=? x name2))
                              body
                              (subst e2 x body)))]

    [Leaf ()            (Leaf)]
    [Branch (ek eL eR)  (Branch (subst e2 x ek) (subst e2 x eL) (subst e2 x eR))]

    [Tree-case (e eEmpty xkey xleft xright eBranch)
               (Tree-case (subst e2 x e)
                          (subst e2 x eEmpty)
                          xkey
                          xleft
                          xright
                          (if (or (symbol=? x xkey)
                                  (symbol=? x xleft)
                                  (symbol=? x xright))
                              eBranch
                              (subst e2 x eBranch)))]

    [Unit ()            (Unit)]

    [Inl (eL)           (Inl (subst e2 x eL))]
    [Inr (eR)           (Inr (subst e2 x eR))]

    [Sum-case (e xL eLeft xR eRight)
              (Sum-case (subst e2 x e)
                        xL
                        (if (symbol=? x xL)
                            eLeft
                            (subst e2 x eLeft))
                        xR
                        (if (symbol=? x xR)
                            eRight
                            (subst e2 x eRight))
                        )]

    [Inl-case (e xL eLeft)
              (Inl-case (subst e2 x e)
                        xL
                        (if (symbol=? x xL)
                            eLeft
                            (subst e2 x eLeft)))]
    [Inr-case (e xR eRight)
              (Inr-case (subst e2 x e)
                        xR
                        (if (symbol=? x xR)
                            eRight
                            (subst e2 x eRight)))]
    ))


; value? : E -> boolean
;
; Returns true if e is a value.
;
(define (value? e)
  (type-case E e
    [Num (n)                  #true]

    [Id  (x)     ; Won't happen during stepping, so it doesn't really matter what we put here.
         ; Still, I want Id to be a value:
         ;  we're using the value strategy, so whenever we substitute e2 for x in some
         ;  expression, the expression e2 that replaces x is always a value.
         ;  Since x is always replaced by a value, it makes sense to say that x is a value.
         #true]

    [Bfalse ()                #true]
    [Btrue ()                 #true]
    [Lam (x eB)               #true]
    [Pair (e1 e2)             (and (value? e1)
                                   (value? e2))]
    [Leaf ()                  #true]
    [Branch (eKey eL eR)      (and (value? eKey)
                                   (value? eL)
                                   (value? eR))]

    [Unit ()                  #true]
    [Inl (eL)                 (value? eL)]
    [Inr (eR)                 (value? eR)]

    [else                     #false]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Stuff with binary operators: valid-binop, apply-binop.
; This code is identical to a3:
; arithmetic happens inside a single step in the small-step semantics,
; and inside a single rule application in the big-step semantics.
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; racket-boolean-to-Fun-boolean : bool? -> E?
;
; Postcondition: result is Bfalse or Btrue
(define (racket-boolean-to-Fun-boolean b)
  (if b
      (Btrue)
      (Bfalse)))

; valid-binop : Op E E -> boolean
;
; valid-binop op v1 v2 returns true iff v1 and v2 are consistent with op:
;    If op is plusop or minusop, then v1 and v2 must be nums.
;    If op is equalsop or lessthanop, then v1 and v2 must be nums.
;
; Precondition: v1 and v2 are values.

(define (valid-binop op v1 v2)
  (type-case Op op
    [Plusop ()      (and (Num? v1) (Num? v2))]
    [Minusop ()     (and (Num? v1) (Num? v2))]
    [Equalsop ()    (and (Num? v1) (Num? v2))]
    [Lessthanop ()  (and (Num? v1) (Num? v2))]

    ; This code is redundant, but it makes it easy to match an operator with
    ; its valid arguments, and is easier to extend if we add operators whose
    ; arguments aren't numbers.
    ))

; apply-binop : Op E E -> E
;
; apply-binop op v1 v2 applies op to v1 and v2, returning an expression.
; Used in interp, below.
;
; Precondition:
;    1.  v1 and v2 are values (i.e., num, lam, Bfalse, or Btrue).
;    2.  (valid-binop op v1 v2)

; Postcondition:
;    If op is plusop or minusop, result is a num.
;    If op is equalsop or lessthanop, result is Bfalse or Btrue.

(define (apply-binop op v1 v2)
  (type-case Op op
    [Plusop ()      (Num (+ (Num-n v1) (Num-n v2)))]
    [Minusop ()     (Num (- (Num-n v1) (Num-n v2)))]
    [Equalsop ()    (racket-boolean-to-Fun-boolean (= (Num-n v1) (Num-n v2)))]
    [Lessthanop ()  (racket-boolean-to-Fun-boolean (< (Num-n v1) (Num-n v2)))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Functions built on top of stepping: try-step, steps-aux, steps.
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; try-step : E -> E
;
; (try-step e): If e is already a value, return it.
;               Otherwise, try to take 1 step.
(define (try-step e)
  (if (value? e)
      e
      (step e)))

; steps-aux : E -> E
;
; Calls step repeatedly, if needed, until it gets a value.
;
(define (steps-aux e)
  (if (value? e)
      (begin
        (printf "    value.\n")
        e)
      (let* ([e2 (step e)])
        (if e2
            (begin
              (printf "--> ~a\n" (unparse e2))
              (steps-aux e2))
            (begin
              (printf "    stuck!\n")
              #false)))))

; steps : E -> (or false E)
;
; Calls step repeatedly, if needed, until it gets a value
(define (steps e)
  (and e
       (begin
         (printf "    ~a\n" (unparse e))
         (steps-aux e))
       ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Core stepping functions:
;
; reduce implements the reduction rules: Step-..., except for Step-context.
; step implements *all* the rules, including Step-context.
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; reduce : E -> (or false E)
;
; Attempts to apply one of the Step-... rules, *except* for
; Step-context.  If no rule can be applied, returns false.
;
(define (reduce e)
  (type-case E e

    [Par (e1 e2)
         ; a4 Problem 4
         ; Step-par-left
         (if (value? e1)
           e1
           ; Step-par-right
           (if (value? e2)
             e2
             #f))]

    [Choose (e1 e2)
            ; a4 Problem 4
            (if (= (random 2) 0)
              e1
              e2)]

    [Ite (e eThen eElse)

         (type-case E e
           [Btrue ()      eThen]   ; Step-ite-true
           [Bfalse ()     eElse]   ; Step-ite-false
           [else          #false]
           )]

    [Binop (op e1 e2)   ; Step-binop

           (if (and (value? e1) (value? e2))

               (if (valid-binop op e1 e2)
                   (let ([v  (apply-binop op e1 e2)])
                     v)
                   (error "binop applied to invalid arguments"))
               #false)
           ]

    [App (e1 e2)   ; Step-app-value

         (if (and (Lam? e1) (value? e2))
             (subst e2 (Lam-name e1) (Lam-body e1))
             #false)
         ]

    [Let (x e1 e2)   ; Step-let
         (if (value? e1)
             (subst e1 x e2)
             #false)
         ]

    [Rec (u e)        ; Step-rec
         (subst (Rec u e) u e)]

    [Pair-case (ePair x1 x2 eBody)
               (and (value? ePair)
                    (type-case E ePair
                      [Pair (v1 v2)   (subst v2 x2 (subst v1 x1 eBody))]
                      [else #false]))]

    ; [Branch (eKey eL eR)]
    [Tree-case (eTree eLeaf xKey xL xR eBranch)

               (and (value? eTree)
                    (type-case E eTree
                      [Leaf   ()
                              ; Step-tree-case-leaf
                              eLeaf]

                      [Branch (vKey vL vR)   ; (value? eTree) = #true, so vKey/vL/vR are values
                              ; Step-tree-case-branch
                              (subst vR xR
                                     (subst vL xL
                                            (subst vKey xKey
                                                   eBranch)))]
                      [else  #false]))
               ]

    ; a4 Problem 3:
    ; Step-sum
    [Sum-case (eSum xL eL xR eR)
              (and (value? eSum)
                   (type-case E eSum
                              ; Step-sum-case-inl
                              [Inl (v)
                                   (subst v xL eL)]
                              ; Step-sum-case-inr
                              [Inr (v)
                                   (subst v xR eR)]
                              [else #false]))]
    ; Step-inl-case
    [Inl-case (eSum xL eL)
              (and (value? eSum)
                   (type-case E eSum
                              [Inl (v)
                                   (subst v xL eL)]
                              [else #false]))]
    ; Step-inr-case
    [Inr-case (eSum xL eL)
              (and (value? eSum)
                   (type-case E eSum
                              [Inr (v)
                                   (subst v xL eL)]
                              [else #false]))]
    ; Implement the rules Step-sum-case-inl,
    ;                     Step-sum-case-inr,
    ;                     Step-inl-case,
    ;                     Step-inr-case.

    [Id (x)
        (error "free-variable")]

    [else
     #false]
    ))

; step : E -> (or false E)
;
; Given e, returns an e' such that  e --> e'  using the Step-... rules.
; If no such e' exists, returns false.
;
(define (step e)
  (or
   ; First, try to call reduce (above) to apply one of the
   ; "reduction rules".
   ;
   ;    (You will implement: Step-par-left, Step-par-right,
   ;                         Step-choose-left, Step-choose-right.)
   (reduce e)

   ; If we get this far in the (or ...), it means that (reduce e) = #false.
   ; That means we couldn't apply any reduction rules to the whole expression.
   ;
   ; Now, try to apply the context rule Step-context,
   ; using the definition of evaluation contexts C
   ; to find a subexpression that steps.
   (type-case E e
     [Binop (op e1 e2)
            (let ([s1 (step e1)])            ; C ::= (Binop op C e2)
              (if s1
                  (Binop op s1 e2)
                  (if (value? e1)
                      (let ([s2 (step e2)])  ; C ::= (Binop op v C)
                        (if s2
                            (Binop op e1 s2)
                            #false))
                      #false)))]

     [App (e1 e2)
          (let ([s1 (step e1)])
            (if s1
                (App s1 e2)              ; C ::= (App C e2)
                (if (value? e1)
                    (let ([s2 (step e2)])
                      (if s2
                          (App e1 s2)    ; C ::= (App v C)
                          #false))
                    #false)))]

     [Let (x e1 eB)
          (let ([s1 (step e1)])
            (if s1
                (Let x s1 eB)    ; C ::= (Let x C eB)
                #false))]

     [Ite (e eThen eElse)
          (let ([s (step e)])              ; C ::= (Ite C eThen eElse)
            (and s
                 (Ite s eThen eElse)))]

     [Pair (eL eR)
           (let ([sL (step eL)])
             (if sL
                 (Pair sL eR)              ; C ::= (Pair C eR)
                 (and (value? eL)
                      (let ([sR (step eR)])
                        (and sR
                             (Pair eL sR)    ; C ::= (Pair v C)
                             )))))]

     [Pair-case (ePair xL xR eBody)
                (let ([sPair (step ePair)])
                  (if sPair
                      (Pair-case sPair xL xR eBody)  ; C ::= (Pair-case C x x e)
                      #false))]

     [Branch (eKey eL eR)
             (let ([sKey (step eKey)])
               (if sKey
                   (Branch sKey eL eR)     ; C ::= (Branch C e e)
                   (and (value? eKey)
                        (let ([sL (step eL)])
                          (if sL
                              (Branch eKey sL eR)  ; C ::= (Branch v C e)
                              (and (value? eL)
                                   (let ([sR (step eR)])
                                     (if sR
                                         (Branch eKey eL sR)  ; C ::= (Branch v v C)
                                         #false))))))))
             ]

     [Tree-case (eTree eLeaf xKey xL xR eBranch)
                (let ([sTree (step eTree)])
                  (if sTree                      ; C ::= (Tree-case C e x x x e)
                      (Tree-case sTree eLeaf xKey xL xR eBranch)
                      #false))]

     [Inl (eL)
          (let ([sL (step eL)])
            (and sL                              ; C ::= (Inl C)
                 (Inl sL)))]
     [Inr (eR)
          (let ([sR (step eR)])
            (and sR                              ; C ::= (Inr C)
                 (Inr sR)))]

     ; Sum-case, Inl-case, Inr-case all work in essentially the same way:
     ; the "scrutinee" (eSum) can step, but no other subexpressions can step.
     [Sum-case (eSum xL eL xR eR)
               (let ([sSum (step eSum)])
                 (if sSum                        ; C ::= (Sum-case C x e x e)
                     (Sum-case sSum xL eL xR eR)
                     #false))]

     [Inl-case (eSum xL eL)
               (let ([sSum (step eSum)])
                 (if sSum                        ; C ::= (Inl-case C x e)
                     (Inl-case sSum xL eL)
                     #false))]
     [Inr-case (eSum xR eR)
               (let ([sSum (step eSum)])
                 (if sSum                         ; C ::= (Inr-case C x e)
                     (Inr-case sSum xR eR)
                     #false))]

     [Par (e1 e2)
          ; The call to reduce, above, returned #false;
          ; therefore (once you've implemented the missing code in reduce),
          ; neither e1 nor e2 is a value.
          ; a4 Problem 4
          (if (= (random 2) 0)
            (Par (step e1) e2)
            (Par e1 (step e2)))]

     ; NOTE: no branch for Choose, since it doesn't appear
     ;  in the grammar of evaluation contexts C

     [else  #false]
     )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Unparsing
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (unparse-op op)
  (type-case Op op
    [Plusop ()      `+]
    [Minusop ()     `-]
    [Equalsop ()    `=]
    [Lessthanop ()  `<]))

; unparse : (or false E) -> sexp
;
(define (unparse e)
  (if (false? e)
      #false     ; allows us to use `unparse' on the result of `steps' when stepping gets stuck
      (type-case E e
        [Num (n)                   n]
        [Binop (op e1 e2)          `(,(unparse-op op) ,(unparse e1) ,(unparse e2))]
        [Id (x)                    x]
        [Let (x e1 eB)             `(Let ,x ,(unparse e1) ,(unparse eB))]
        [Lam (x   body)            `(Lam ,x                   ,(unparse body))]
        [App (e1 e2)               `(App ,(unparse e1) ,(unparse e2))]
        [Par (e1 e2)               `(Par ,(unparse e1) ,(unparse e2))]
        [Choose (e1 e2)            `(Choose ,(unparse e1) ,(unparse e2))]
        [Rec (u   body)            `(Rec ,u                  ,(unparse body))]
        [Bfalse ()                 `Bfalse]
        [Btrue ()                  `Btrue]
        [Ite (e e1 e2)             `(Ite ,(unparse e) ,(unparse e1) ,(unparse e2))]

        [Pair (e1 e2)              `(Pair ,(unparse e1) ,(unparse e2))]
        [Pair-case (e x1 x2 body)  `(Pair-case ,(unparse e) (,x1 ,x2 => ,(unparse body)))]

        [Leaf ( )                  `(Leaf                )]
        [Branch (eKey eL eR)       `(Branch ,(unparse eKey) ,(unparse eL) ,(unparse eR))]
        [Tree-case (e eLeaf xk xl xr eBranch)
                   `(Tree-case ,(unparse e)
                               (Leaf               => ,(unparse eLeaf))
                               (Branch ,xk ,xl ,xr => ,(unparse eBranch)))]

        [Unit ()                   `Unit]
        [Inl (eL)                  `(Inl ,(unparse eL))]
        [Inr (eR)                  `(Inr ,(unparse eR))]
        [Sum-case (e xL eL xR eR)
                  `(Sum-case ,(unparse e)
                             (Inl ,xL            => ,(unparse eL))
                             (Inr ,xR            => ,(unparse eR)))]
        [Inl-case (e xL eL)
                  `(Inl-case ,(unparse e)
                             (Inl ,xL            => ,(unparse eL)))]
        [Inr-case (e xR eR)
                  `(Inr-case ,(unparse e)
                             (Inr ,xR            => ,(unparse eR)))]
        )))

;
; try-some : E -> positive-integer -> listof E
;
; Our semantics is now very nondeterministic, so we need
; a way to evaluate the same expression repeatedly and
; collect the results into a list.
(define (try-some e n)
  (if (= n 0)
      empty
      (cons (unparse (steps e))
            (try-some e (- n 1)))))

#|
  Problem 5

  Replace the concrete syntax {+ 1 1}, etc. with your solution.
  Or remove the calls to parse, and build abstract syntax directly.
|#
(define part5a-e1 (parse '{Rec u u}))

(define part5a-e2 (parse '{+ 2 2}))

#| Part 5a:
   If you think no such expressions e1, e2 exist,
   explain why here:


   (Part 5a)
|#

(define part5b-e3 (parse '{+ 3 3}))

(define part5b-e4 (parse '{+ 4 4}))


#| Part 5b:
   If you think no such expressions e3, e4 exist,
   explain why here:

For (Choose e3 e4) to always converge, both e3 and e4 must converge when
executed seperately. When (Par e3 e4) runs, it will randomly step e3 and e4
until one of them converges. Since we know e3 and e4 converge, (Par e3 e4) must
also converge. Thus, there are no such expressions such that (Choose e3 e4)
converges and (Par e3 e4) does not.


   (Part 5b)
|#

; Save before you try these...

#|
; test 5a:
  (try-some (Par part5a-e1 part5a-e2) 10)
  (try-some (Choose part5a-e1 part5a-e2) 10)

; test 5b:
  (try-some (Choose e3 e4) 20)
  (try-some (Par e3 e4) 5)
|#

#|
(unparse (steps (parse
                 '{Let repeat {Lam f {Lam x {App f {App f x}}}}
                       {App repeat {Lam z {+ z z}}}}
                 )))

; The next block of examples won't work until you
(unparse (steps (parse
                 '{Choose {Choose 1 2} {Choose 3 4}})))

(unparse (steps (parse
                 '{Par {App {Lam x 1} 0}
                       {App {Lam x 2} 0}})))


(try-some (parse '{Choose {Choose 1 2} {Choose 3 4}}) 10)

(try-some (parse '{Par {App {Lam x 1} 0}
                       {App {Lam x 2} 0}}) 10)

(try-some (parse '{Par {App {App {Lam x {Lam y 1}} 0} 0}
                         {App {App {Lam x {Lam y 2}} 0} 0}}) 10)

(try-some (parse
           '{Let ; A way to take extra steps:
                  spin {Rec spin {Lam k {Ite {= k 0}
                                             0
                                             {App spin {- k 1}}}}}
                  ; Starts two "threads", one that spins for time 3,
                  ; one that spins for time 4.  Occasionally, the
                  ; second thread "wins" and we return 2.
                  {Par {Let s {App spin 3}
                            {App {Lam x 1} 0}}
                       {Let s {App spin 4}
                             {App {Lam x 2} 0}}}}
           )
          10)
|#

;
; Examples with trees and sums
;
#|
(steps (parse '{Tree-case {Branch 99 {Leaf} {Leaf}} {Leaf => 1} {Branch key l r => key}}))

; Uncomment this part to test your Problem 3 code

(test (steps (parse '{Sum-case {App {Lam z {Inl z}} 50}
                    {Inl l => {+ l 10}}
                    {Inr r => {- r 10}}}))
      (Num 60))
(test (steps (parse '{Sum-case {Inr {+ 2 2}}
                    {Inl l => {+ l 10}}
                    {Inr r => {- r 10}}}))
      (Num -6))

(test (steps (parse '{Inr-case {Inr {+ 2 {- 5 1}}} {Inr yy => yy}}))
      (Num 6))
|#


#| Commented-out example.  Printing all the steps takes a while...
(steps (parse '{Let* {AND {Lam p {Lam q {Ite p q Bfalse}}}}
                     {OR  {Lam p {Lam q {Ite p Btrue q}}}}
                     {NOT {Lam p {Ite p Bfalse Btrue}}}
                     {XOR {Lam p {Lam q   ; p XOR q  iff  (p OR q) AND NOT(p AND q)
                                      {App {App AND
                                                   {App {App OR p} q}   ; p OR q
                                                   }
                                           {App NOT {App {App AND p} q}}}}}}  ; NOT (p AND q)
                     {trueXORtrue   {App {App XOR Btrue} Btrue}}
                     {trueXORfalse  {App {App XOR Btrue} Bfalse}}
                     {falseXORtrue  {App {App XOR Bfalse} Btrue}}
                     {falseXORfalse {App {App XOR Bfalse} Bfalse}}

                     {Pair {Pair trueXORtrue trueXORfalse}
                           {Pair falseXORtrue falseXORfalse}}}
              ))
|#

; Another commented-out example, "the same" as the example above (do you see why?),
; but it won't work until you implement the reduction rules for sums.
#|
(steps (parse '{Let* {t {Inl Unit}}
                     {f {Inr Unit}}
                     {AND {Lam p {Lam q {Sum-case p {Inl l => q} {Inr r => f}}}}}
                     {OR  {Lam p {Lam q {Sum-case p {Inl l => t} {Inr r => q}}}}}
                     {NOT {Lam p {Sum-case p {Inl l => f} {Inr r => t}}}}
                     {XOR {Lam p {Lam q   ; p XOR q  iff  (p OR q) AND NOT(p AND q)
                                      {App {App AND
                                                   {App {App OR p} q}   ; p OR q
                                                   }
                                           {App NOT {App {App AND p} q}}}}}}  ; NOT (p AND q)
                     {trueXORtrue   {App {App XOR t} t}}
                     {trueXORfalse  {App {App XOR t} f}}
                     {falseXORtrue  {App {App XOR f} t}}
                     {falseXORfalse {App {App XOR f} f}}

                     {Pair {Pair trueXORtrue trueXORfalse}
                           {Pair falseXORtrue falseXORfalse}}}
              ))
|#
