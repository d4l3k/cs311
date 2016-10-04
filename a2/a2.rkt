#lang plai

; CPSC 311 2016W1 assignment 2

; BNF of the Fun++ language:
;
; <LetBinding> ::= {<symbol> <E>}            ; used in Let*, below
;
;  <E> ::= <num>
;        | {+ <E> <E>}
;        | {- <E> <E>}
;        | {= <E> <E>}
;        | {< <E> <E>}
;        | {Let <symbol> <E> <E>}
;        | <symbol>
;        | {Lam <symbol> <E>}
;        | {App <E> <E>}
;
;        | {Rec <symbol> <E>}
;
;        | {Let* <LetBinding>... <E>}
;                            ^
;                            zero or more
;
;        | Btrue
;        | Bfalse
;        | {Ite <E> <E> <E>}         ; "if-then-else"
;
;        | {Pair <E> <E>}
;        | {Pair-case <E> {<symbol> <symbol> => <E>}}
;
;        | {Fst <E>}
;        | {Snd <E>}
;
; Note: this concrete syntax for Pair-case is "anti-Racket",
; with an extra "=>", which makes parse-pair-case kind of annoying.

; Abstract syntax of Fun:

; 1. Abstract syntax of bindings inside Let* expressions:
(define-type LetBinding
  [Binding (name symbol?) (named-expr E?)])

; 2. Abstract syntax of operators (+, -, =, <):
(define-type Op
  ; operators from (Num n1) (Num n2) to (Num n):
  [Plusop]
  [Minusop]
  ; operators from (Num n1) (Num n2) to (Bfalse) or (Btrue):
  [Equalsop]
  [Lessthanop])

; 3. Abstract syntax of expressions:
(define-type E
  ; numbers
  [Num (n number?)]
  [Binop (op Op?) (lhs E?) (rhs E?)]

  ; LetBinding
  [Let (name symbol?) (named-expr E?) (body E?)]
  [Id (name symbol?)]
  [Let* (LetBindings (listof LetBinding?)) (body E?)]

  ; functions
  [Lam (name symbol?) (body E?)]
  [App (function E?) (argument E?)]

  ; recursion
  [Rec (name symbol?) (body E?)]

  ; booleans
  [Bfalse]
  [Btrue]
  [Ite (b E?) (then-branch E?) (else-branch E?)]

  ; pairs
  [Pair (left E?) (right E?)]
  [Pair-case (scrutinee E?) (name1 symbol?) (name2 symbol?) (body E?)]

  ; Do *not* add variants to this definition!
  )



; Parser for Fun expressions
;
; parse : sexp -> E
(define (parse sexp)
  (cond

    [(number? sexp) (Num sexp)]

    [(symbol? sexp)
     (case sexp
       [(Bfalse) (Bfalse)]
       [(Btrue)  (Btrue)]
       [else
        (Id sexp)])]

    [(list? sexp)
     (let*
         ([head      (first sexp)]
          [args      (rest sexp)]
          [arg-count (length args)])

       (case head
         [(Binop) (error "parse: Binop isn't concrete syntax, it's abstract syntax")]

         [(+) (if (= arg-count 2)
                  (Binop (Plusop) (parse (first args)) (parse (second args)))
                  (error "parse: + needs exactly 2 arguments"))]

         [(-) (if (= arg-count 2)
                  (Binop (Minusop) (parse (first args)) (parse (second args)))
                  (error "parse: - needs exactly 2 arguments"))]

         [(=) (if (= arg-count 2)
                  (Binop (Equalsop) (parse (first args)) (parse (second args)))
                  (error "parse: = needs exactly 2 arguments"))]

         [(<) (if (= arg-count 2)
                  (Binop (Lessthanop) (parse (first args)) (parse (second args)))
                  (error "parse: < needs exactly 2 arguments"))]

         [(Let*) (if (>= arg-count 1)
                     (let ([bindings-sexp-list (drop-right args 1)]
                           [body-sexp (first (take-right args 1))])
                       (Let* (parse-bindings bindings-sexp-list)
                             (parse body-sexp)))
                     (error "parse: malformed `Let*'"))]

         [(Ite) (if (= arg-count 3)
                    (Ite (parse (first args))
                         (parse (second args))
                         (parse (third args)))
                    (error "parse needs exactly 3 arguments"))]

         [(Lam) (if (= arg-count 2)
                    (if (symbol? (first args))
                        (Lam (first args) (parse (second args)))
                        (error "parse: lam must be followed by an identifier"))
                    (error "parse: malformed `lam'"))]

         [(App) (if (= arg-count 2)
                    (App (parse (first args)) (parse (second args)))
                    (error "parse: app needs 1 function and 1 argument"))]

         [(Rec) (if (= arg-count 2)
                    (if (symbol? (first args))
                        (Rec (first args) (parse (second args)))
                        (error "parse: rec must be followed by an identifier"))
                    (error "parse: malformed `rec'"))]

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
                     (error "parse: malformed `pair'"))]

         [(Pair-case) (parse-pair-case arg-count args)]

         [(Fst) (Pair-case (parse (first args)) 'x 'y (parse 'x))]

         [(Snd) (Pair-case (parse (first args)) 'x 'y (parse 'y))]

         [else (error "parse: syntax error")]))]

    [else (error "parse: syntax error")]))

; parse-pair-case : sexp -> E
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

            (error "parse: malformed `pair-case'")))

      (error "parse: malformed `pair-case'")))

; parse-binding : sexp -> LetBinding
;
; Parse a single concrete-syntax binding, which should be a 2-element list
; whose first element is a symbol, into a LetBinding.
(define (parse-binding sexp)
  (if (and (list? sexp) (= (length sexp) 2))
      (let ([name       (first sexp)]
            [named-sexp (second sexp)])
        (if (symbol? name)
            (Binding name (parse named-sexp))
            (error "parse: malformed `Let*'" name)))
      (error "parse-binding: malformed `Let*' binding" sexp)))

; parse-binding : listof sexp -> listof LetBinding
;
; Parse a list of concrete-syntax bindings into a list of LetBindings.
(define (parse-bindings sexp)
  (if (list? sexp)
      (map parse-binding sexp)
      (error "parse-bindings: malformed `Let*' bindings" sexp)))


; subst : E? symbol? E? -> E?
;
; (subst v x e) returns e with x replaced by v.
;
(define (subst v x e)
  (type-case E e
    [Num (n) (Num n)]
    [Binop (op eL eR) (Binop op (subst v x eL) (subst v x eR))]

    [Btrue () e]
    [Bfalse () e]
    [Ite (e1 eThen eElse)
         (Ite (subst v x e1) (subst v x eThen) (subst v x eElse))]

    [Let (y e eB)
          (if (symbol=? x y)
              (Let x (subst v x e) eB)
              (Let y (subst v x e) (subst v x eB)))]
    [Id (y)
        (if (symbol=? x y)
            v
            (Id y))]

    [Lam (y eB)
         (if (symbol=? x y)
             ; same symbol; if x appears inside eB, it refers to *this*
             ;  binding, not to the x we're replacing, so return same eB
             (Lam x eB)

             ; different symbol; leave y alone and replace inside eB
             (Lam y (subst v x eB))
             )]

    [App (eFun eArg) (App (subst v x eFun) (subst v x eArg))]

    [Rec (y eB)     ; rec binds y, so treat it the same way as lam
         (if (symbol=? x y)
             (Rec x eB)
             (Rec y (subst v x eB)))]


    [Let* (bindings eB)
           (if (empty? bindings)
               (Let* empty (subst v x eB))
               (let ([binding1  (first bindings)]
                     [bindings2 (rest bindings)])
                 (type-case LetBinding binding1
                   [Binding (y e)
                            (let ([binding1-subst (Binding y (subst v x e))])
                              (if (symbol=? x y)
                                  (Let* (cons binding1-subst bindings2) eB)
                                  (type-case E (subst v x (Let* bindings2 eB))
                                    [Let* (bindings2-subst eB-subst)
                                          (Let* (cons binding1-subst bindings2-subst)
                                                eB-subst)]
                                    [else (error "impossible")]
                                    )))]
                   )))]

    [Pair (left right)   (Pair (subst v x left) (subst v x right))]
    [Pair-case (scrutinee name1 name2 body)

               (Pair-case (subst v x scrutinee) name1 name2
                          (if (or (symbol=? x name1) (symbol=? x name2))
                              body
                              (subst v x body)))]


    ;[else (error "subst: unimplemented")]
    ))

; racket-boolean-to-Fun-boolean : bool? -> E?
;
; Postcondition: result is Bfalse or Btrue

(define (racket-boolean-to-Fun-boolean b)
  (if b
      (Btrue)
      (Bfalse)))



; valid-binop : Op? E? E? -> boolean?
;
; valid-binop op v1 v2 returns true iff v1 and v2 are consistent with op:
;    If op is Plusop or Minusop, then v1 and v2 must be Nums.
;    If op is Equalsop or Lessthanop, then v1 and v2 must be Nums.
;
; Precondition: v1 and v2 are values (i.e., Num, Lam, Bfalse, or Btrue).

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


; apply-binop : Op? E? E? -> E?
;
; apply-binop op v1 v2 applies op to v1 and v2, returning an expression.
; Used in interp, below.
;
; Precondition:
;    1.  v1 and v2 are values (i.e., num, lam, Bfalse, or Btrue).
;    2.  (valid-binop op v1 v2)

; Postcondition:
;    If op is Plusop or Minusop, result is a num.
;    If op is Equalsop or Lessthanop, result is Bfalse or Btrue.

(define (apply-binop op v1 v2)
  (type-case Op op
    [Plusop ()      (Num (+ (Num-n v1) (Num-n v2)))]
    [Minusop ()     (Num (- (Num-n v1) (Num-n v2)))]
    [Equalsop ()    (racket-boolean-to-Fun-boolean (= (Num-n v1) (Num-n v2)))]
    [Lessthanop ()  (racket-boolean-to-Fun-boolean (< (Num-n v1) (Num-n v2)))]))



; Interpreter for Fun expressions:
;
; interp : E? -> E?
;
; Given an E e, return the E v such that
;
;                e ⇓ v
;
; according to the rules specified in Assignment 2.

(define (interp e)
  (type-case E e

    ; Values evaluate to themselves:
    [Num (n)     (Num n)]
    [Lam (x eB)  (Lam x eB)]
    [Bfalse ()   (Bfalse)]
    [Btrue ()    (Btrue)]

    ; Non-values:
    [App (e1 e2)
         (let ([v1 (interp e1)])
           (type-case E v1
             [Lam (x eB)
                  (let* ([v2 (interp e2)]
                         [v (interp (subst v2 x eB))])
                    v)]
             [else (error "tried to apply non-lam")]
             ))]

    [Rec (u eB)
      (let ([v (interp (subst (Rec u eB) u eB))])
        v)]

    [Binop (op e1 e2)
           (let* ([v1 (interp e1)]
                  [v2 (interp e2)])
             (if (valid-binop op v1 v2)
                 (let ([v  (apply-binop op v1 v2)])
                   v)
                 (error "binop applied to invalid arguments")))]

    [Ite (e eThen eElse)
         (let* ([v (interp e)])
           (if (Btrue? v)
             (interp eThen)
             (interp eElse)))]

    [Let (x e1 e2)
          (let* ([v1 (interp e1)]
                 [v2 (interp (subst v1 x e2))])
            v2)]

    [Let* (bindings eB)
          (if (empty? bindings)
            (interp eB)
            (type-case LetBinding (first bindings)
              [Binding (y expr)
                       (interp (subst expr y (Let* (rest bindings) eB)))]))]

    [Id (x)
        (error "free-variable")]

    [Pair (e1 e2)
          (Pair (interp e1) (interp e2))]

    [Pair-case (ePair x1 x2 eB)
               (type-case E ePair
                          [Pair (e1 e2)
                                (interp (subst e1 x1 (subst e2 x2 eB)))]
                          [else (error "tried to run pair-case with non pair")])]

    ;[else (error "interp: unimplemented")]
    ))


(define (unparse-op op)
  (type-case Op op
    [Plusop ()      `+]
    [Minusop ()     `-]
    [Equalsop ()    `=]
    [Lessthanop ()  `<]))

(define (unparse-binding b)
  (type-case LetBinding b
    [Binding (x e)  `(,x ,(unparse e))]))

(define (unparse-bindings bs)
  (map unparse-binding bs))

(define (unparse e)
  (type-case E e
    [Num (n)                   n]
    [Binop (op e1 e2)          `(,(unparse-op op) ,(unparse e1) ,(unparse e2))]
    [Id (x)                    x]
    [Let (x e1 eB)             `(Let ,x ,(unparse e1) ,(unparse eB))]
    [Let* (bindings body)      (append (list 'Let*) (unparse-bindings bindings) (list (unparse body)))]
    [Lam (x body)              `(Lam ,x ,(unparse body))]
    [App (e1 e2)               `(App ,(unparse e1) ,(unparse e2))]
    [Rec (u body)              `(Rec ,u ,(unparse body))]
    [Bfalse ()                 `Bfalse]
    [Btrue ()                  `Btrue]
    [Ite (e e1 e2)             `(Ite ,(unparse e) ,(unparse e1) ,(unparse e2))]
    [Pair (e1 e2)              `(Pair ,(unparse e1) ,(unparse e2))]
    [Pair-case (e x1 x2 body)  `(Pair-case ,(unparse e) (,x1 ,x2 => ,(unparse body)))]
    ))


(define (do-parse input)
  (let* ([abstract-exp  (parse input)]
         [concrete-exp  (unparse abstract-exp)])
    (printf "          input: ~v\n" input)
    (printf "abstract syntax: ~v\n" abstract-exp)
    (printf "unparsed syntax: ~v\n" concrete-exp)
    ))

(define (do-parse-interp input)
  (let* ([abstract-exp  (parse input)]
         [concrete-exp  (unparse abstract-exp)])
    (printf "          input: ~v\n" input)
    (printf "abstract syntax: ~v\n" abstract-exp)
    (printf "unparsed syntax: ~v\n\n" concrete-exp)
    (let ([v (interp abstract-exp)])
      (printf "\nresult of evaluation: ~v\n" v)
      (printf "     unparsed result: ~v\n\n" (unparse v)))))


; test-parse input expected-abstract-exp
;
; Checks that
;  1. the result of (parse input) is the same as expected-abstract-exp
;  2. the result of (unparse (parse input)) is the same as input.
;
; May fail if input uses syntactic sugar; see test-parse-sugar below.
;
(define (test-parse input expected-abstract-exp)
  (let* ([abstract-exp  (parse input)]
         [concrete-exp  (unparse abstract-exp)])
    (test abstract-exp expected-abstract-exp)
    (test concrete-exp input)
    ))

; test-parse-sugar:
;
; Like test-parse, but doesn't check that the result of unparsing
; matches the original input.
;
(define (test-parse-sugar input expected-abstract-exp)
  (let* ([abstract-exp  (parse input)]
         [concrete-exp  (unparse abstract-exp)])
    (test abstract-exp expected-abstract-exp)
    ))

(test-parse '{+ 11 22} (Binop (Plusop) (Num 11) (Num 22)))

(test-parse '{Let*
                    {Lam botanical botanical}}
            (Let* empty (Lam 'botanical (Id 'botanical))))

(test-parse '{Let* {abba {Lam sweden sweden}}
                     {austra {Lam canada {App abba canada}}}
                    austra}
            (Let* (list (Binding 'abba (Lam 'sweden (Id 'sweden)))
                         (Binding 'austra (Lam 'canada (App (Id 'abba) (Id 'canada)))))
                   (Id 'austra)))

(test-parse '{= 5 5}            (Binop (Equalsop) (Num 5) (Num 5)))
(test-parse '{= 5 6}            (Binop (Equalsop) (Num 5) (Num 6)))

(test-parse '{Ite Bfalse 0 1}             (Ite (Bfalse) (Num 0) (Num 1)))
(test-parse '{Ite Btrue 1 2}              (Ite (Btrue) (Num 1) (Num 2)))
(test-parse '{Ite {Ite 1 2 3} 4 5}        (Ite (Ite (Num 1) (Num 2) (Num 3)) (Num 4) (Num 5)))

(test-parse '{Pair Btrue Bfalse}          (Pair (Btrue) (Bfalse)))
(test-parse '{Pair-case {Pair 7       8}       {a b => {- Btrue b}}}
            (Pair-case (Pair (Num 7) (Num 8)) 'a 'b   (Binop (Minusop) (Btrue) (Id 'b))))



(define (test-interp input expected-value)
  (let* ([abstract-exp  (parse input)])
    (printf "          input: ~v\n" input)
    (printf "abstract syntax: ~v\n" abstract-exp)
    (let ([v (interp abstract-exp)])
      (printf "\n         unparsed value: ~v\n" (unparse v))
      (printf "unparsed expected value: ~v\n\n" (unparse expected-value))
      (test v expected-value))))

(test-interp '{+ 11 22} (Num 33))

(test-interp '{Let*
                     {Lam botanical botanical}}
             (Lam 'botanical (Id 'botanical)))

(test-interp '{Let* {abba {Lam sweden sweden}}
                    {austra {Lam canada {App abba canada}}}
                    austra}
             (Lam 'canada (App (Lam 'sweden (Id 'sweden)) (Id 'canada))))

(test-interp '{= 5 5}               (Btrue))
(test-interp '{= 5 6}               (Bfalse))
(test-interp '{< 4 4}               (Bfalse))
(test-interp '{< 4 3}               (Bfalse))
(test-interp '{< 4 7}               (Btrue))

(test-interp '{Ite Bfalse 0 1}      (Num 1))
(test-interp '{Ite Btrue 1 2}       (Num 1))

(test-interp '{Pair {Ite {< 1 2} Bfalse Btrue} 3}    (Pair (Bfalse) (Num 3)))
(test-interp '{Pair-case {Pair 7 {+ 7 1}} {a b => {- 3 b}}}
             (Num -5))

(test-interp '{Let*
                {multiply {Rec m {Lam x {Lam y {Ite {= y 0}
                                                    0
                                                    {Ite {= y 1}
                                                         x
                                                         {+ x {App {App m x} {- y 1}}}}}}}}}
               {App {App multiply 5} 3}}
             (Num 15))

(test-interp '{Let*
                {multiply {Rec m {Lam x {Lam y {Ite {= y 0}
                                                    0
                                                    {Ite {= y 1}
                                                         x
                                                         {+ x {App {App m x} {- y 1}}}}}}}}}
                {fact {Rec u {Lam n {Ite {< n 2}
                                         1
                                         {Let c {App u {- n 1}}
                                               {App {App multiply n} c}}}}}}
                {App fact 5}}
             (Num 120))

(test-interp '{Fst {Pair 1 2}} (Num 1))
(test-interp '{Snd {Pair 1 2}} (Num 2))
