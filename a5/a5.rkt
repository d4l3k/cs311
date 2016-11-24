#lang plai

; UBC CPSC 311, 2016W1
; a5.rkt   (descended from env-state-direct.rkt)
;
; Environment-based evaluation with closures, recursion, and state.
; In this file, state is implemented using Racket's mutable state (boxes).

; BNF for the language interpreted here:
;
;  <E> ::= <num>
;        | <symbol>
;        | {+ <E> <E>}
;        | {- <E> <E>}
;        | {= <E> <E>}
;        | {< <E> <E>}
;        | {Let <symbol> <E> <E>}
;        | {Lam <symbol> <Type> <E>}
;        | {App <E> <E>}
;        | {Rec <symbol> <Type> <E>}
;        | {Let* <Binding>... <E>}     -----> syntactic sugar for Let
;                           ^
;                           zero or more
;        | Btrue
;        | Bfalse
;        | {Ite <E> <E> <E>}    ; "if-then-else"
;        | {Ref <Type> <E>}
;        | {Deref <E>}
;        | {Setref <E> <E>}
;
;        | {Pair <E> <E>}
;        | {Pair-case <E> {<id> <id> => <E>}}
;
;        | {Downcast <Type> <E>}         ; new
;
;        | {Record <Field>...}           ; new
;                         ^
;                         zero or more
;        | {Dot <E> <Field>}             ; new
;
;        | {Begin <E>...}
;                    ^ one or more
;        | {While <E> <E>}

;  <Type> ::= rat
;           | int
;           | pos
;           | bool
;           | {* <Type> <Type>}
;           | {-> <Type> <Type>...}
;                              ^ one or more
;           | {record <FieldsType>...}
;                                 ^ zero or more
;
; <FieldsType> ::= {<symbol>... <Type>}
;                           ^ one or more

(define-type Type
  [Tpos]    ; positive integers
  [Tint]    ; integers
  [Trat]    ; rationals
  [Tbool]
  [T*       (t1 Type?)     (t2 Type?)]
  [T->      (domain Type?) (range Type?)]
  [Tref     (contents Type?)]
  [Trecord  (fields (listof FieldType?))]
  )

(define-type FieldType
  [field-type (name symbol?) (A Type?)])

(define-type Typing-context
  [tc/empty]
  [tc/cons-tp    (x symbol?) (A Type?) (rest Typing-context?)]
  )

; Abstract syntax of binary operators:
(define-type Op
  [Plusop]
  [Minusop]
  [Equalsop]
  [Lessthanop])

; Abstract syntax of E:
(define-type E
  [Num (n number?)]
  [Binop (op Op?) (lhs E?) (rhs E?)]
  [Let (name symbol?) (named-expr E?) (body E?)]
  [Id (name symbol?)]

  [Bfalse]
  [Btrue]
  [Ite (scrutinee E?) (then-branch E?) (else-branch E?)]

  [Lam (name symbol?) (domain Type?) (body E?)]
  [App (function E?) (argument E?)]
  [Rec (name symbol?) (body-type Type?) (body E?)]

  [Clo (env Env?) (e E?)]

  ; pairs
  [Pair (left E?) (right E?)]
  [Pair-case (scrutinee E?) (name1 symbol?) (name2 symbol?) (body E?)]

  ; refs
  [Ref       (contents-type Type?) (initial-contents E?)]
  [Deref     (loc-expr E?)]
  [Setref    (loc-expr E?) (new-contents E?)]
  [Location  (locsym (box/c E?))]
  ; downcasts
  [Downcast  (target Type?) (e E?)]
  ; records
  [Record    (fields (listof Field?))]
  [Dot       (e E?) (field symbol?)]

  ; sequencing and looping
  [Begin     (expressions (listof E?))]
  [While     (guard E?) (body E?)]
  )

(define-type Field
  [fld       (name symbol?) (contents E?)])

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

         [(Lam) (if (= arg-count 3)
                    (if (symbol? (first args))
                        (Lam (first args) (parse-type (second args)) (parse (third args)))
                        (error "parse: Lam must be followed by an identifier"))
                    (error "parse: malformed `Lam'"))]

         [(App) (if (= arg-count 2)
                    (App (parse (first args)) (parse (second args)))
                    (error "parse: App needs 1 function and 1 argument"))]

         [(Rec) (if (= arg-count 3)
                    (if (symbol? (first args))
                        (Rec (first args) (parse-type (second args)) (parse (third args)))
                        (error "parse: Rec must be followed by an identifier"))
                    (error "parse: malformed `Rec'"))]

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

         [(Ref) (if (= arg-count 2)
                    (Ref (parse-type (first args)) (parse (second args)))
                    (error "parse: malformed `Ref'"))]
         [(Deref) (if (= arg-count 1)
                      (Deref (parse (first args)))
                      (error "parse: malformed `Deref'"))]
         [(Setref) (if (= arg-count 2)
                       (Setref (parse (first args))
                               (parse (second args)))
                       (error "parse: malformed `Setref'"))]

         [(Downcast) (if (= arg-count 2)
                         (Downcast (parse-type (first args))
                                   (parse (second args)))
                         (error "parse: malformed `Downcast'"))]

         [(Record) (Record (append (map parse-field args)))]

         [(Dot)   (if (and (= arg-count 2)
                           (symbol? (second args)))
                      (Dot (parse (first args)) (second args))
                      (error "parse: malformed `Dot'"))]

         [(Begin) (if (>= arg-count 1)
                      (Begin (map parse args))
                      (error "parse: malformed `Begin'"))]

         [(While) (cond
                    [(< arg-count 2)   (error "parse: malformed `While'")]
                    [(= arg-count 2)   (While (parse (first args))
                                              (parse (second args)))]
                    [else              (While (parse (first args))
                                              (parse (cons 'Begin (rest args))))])]

         [else (error "parse: syntax error")]))]

    [else (error "parse: syntax error")]))

; parse-field : sexp -> FieldType
(define (parse-field arg)
  (if (not (and (list? arg)
                (= (length arg) 2)
                (symbol? (first arg))))
      (error "parse-field: syntax error")
      (fld (first arg) (parse (second arg)))))

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

; build-> : listof Type -> Type
;
; Given (list A1 ... A(n-1) An), returns
;
;    (T-> A1 (T-> A2 ... (T-> A(n-1) An)))
;
; Precondition: n >= 2
;
(define (build-> types)
  (if (= (length types) 2)
      (T-> (first types) (second types))
      (T-> (first types) (build-> (rest types)))))

; parse-field-type : sexp -> listof FieldType
;
(define (parse-field-type arg)
  (if (or (not (list? arg)) (< (length arg) 2))
      (error "parse-field-type: syntax error")
      (let* ([ids  (drop-right arg 1)]
             [A    (parse-type (last arg))]
             [ids  (map (lambda (x) (if (symbol? x)
                                        x
                                        (error "parse-field-type: syntax error")))
                        ids)]
             [flds (map (lambda (x) (field-type x A))
                        ids)])
        flds)
      ))

; parse-type : sexp -> Type
;
(define (parse-type sexp)
  (cond
    [(symbol? sexp)
     (case sexp
       [(num)    (Trat)]
       [(rat)    (Trat)]
       [(int)    (Tint)]
       [(pos)    (Tpos)]
       [(bool)   (Tbool)]
       [else     (error "unknown type name")]
       )]
    [(list? sexp)
     (if (empty? sexp)
         (error "parse-type: empty")
         (let*
             ([head      (first sexp)]
              [args      (rest sexp)]
              [arg-count (length args)])

           (case head
             [(*)       (T* (parse-type (first args)) (parse-type (second args)))]
             [(->)      (build-> (map parse-type args))]
             [(ref)     (Tref (parse-type (first args)))]
             [(record)  (Trecord (append* (map parse-field-type args)))]
             [else   (error "unknown type constructor " head)])))]
    [else (error "unknown animal in type")]))

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


; Environments   env ::= Ø
;                      | x=e, env
;                      | Ɛ
;                      | (env-rec Ɛ env)
;
(define-type Env
  [env/empty]
  [env/cons (id symbol?) (bound-expr E?) (tail Env?)]
  [env/id  (name symbol?)]
  [env/rec (name symbol?) (bound-env Env?)])

; env-subst-env : Env symbol Env -> Env
;
; (env-subst-env env1 x env2) returns env2 with x replaced with env1.
(define (env-subst-env env1 x env2)
  (type-case Env env2
    [env/empty () (env/empty)]
    [env/cons (id bound-expr tail)
              (env/cons id
                        (env-subst-expr env1 x bound-expr)
                        (env-subst-env env1 x tail))]
    [env/id (name)
            (if (symbol=? name x)
                env1
                (env/id name))]
    [env/rec (name bound-env)
             (if (symbol=? name x)
                 (env/rec name bound-env)
                 (env/rec name (env-subst-env env1 x bound-env)))]))

; env-subst-expr : Env symbol E -> E
;
; (env-subst-expr env x e) returns e with x replaced with env.
(define (env-subst-expr env x e)
  (type-case E e

    [Num (n) (Num n)]
    [Binop (op e1 e2) (Binop op
                             (env-subst-expr env x e1)
                             (env-subst-expr env x e2))]

    [Btrue () (Btrue)]
    [Bfalse () (Bfalse)]
    [Ite (e eThen eElse) (Ite (env-subst-expr env x e)
                              (env-subst-expr env x eThen)
                              (env-subst-expr env x eElse))]

    [Id (y) (Id y)]
    [Let (y e1 e2)  (Let y
                         (env-subst-expr env x e1)
                         (env-subst-expr env x e2))]

    [Lam (y A eB)   (Lam y A (env-subst-expr env x eB))]
    [App (e1 e2)    (App (env-subst-expr env x e1)
                         (env-subst-expr env x e2))]
    [Rec (u B eB)   (Rec u B (env-subst-expr env x eB))]

    [Clo (envE e)   (Clo (env-subst-env env x envE)
                         (env-subst-expr env x e))]

    [Pair (e1 e2)   (Pair (env-subst-expr env x e1)
                          (env-subst-expr env x e2))]

    [Pair-case (e x1 x2 eBody)
               (Pair (env-subst-expr env x e)
                     x1 x2
                     (env-subst-expr env eBody))]

    [Ref (A e)      (Ref A (env-subst-expr env x e))]
    [Deref (e)      (Deref (env-subst-expr env x e))]

    [Setref (e1 e2) (Setref (env-subst-expr env x e1)
                            (env-subst-expr env x e2))]

    [Downcast (A e) (Downcast A (env-subst-expr env x e))]

    [Record (flds)  (Record flds)]
    [Dot (e fld)    (Dot (env-subst-expr env x e) fld)]

    [Begin (es)     (Begin (map (lambda (e) (env-subst-expr env x e)) es))]
    [While (e1 e2)  (While (env-subst-expr env x e1)
                           (env-subst-expr env x e2))]

    [Location (l)   (Location l)]
    ))


; look-up-id : Env symbol -> (or false E)
;
; Returns expression bound to symbol in environment,
;  or #false if symbol not found
;
(define (look-up-id env x)
  (type-case Env env
    [env/empty ()             #f]
    [env/cons (y e env0)   (if (symbol=? x y)
                               e
                               (look-up-id env0 x))]
    [env/id (name) #f]
    [env/rec (name bound-env) (look-up-id (env-subst-env env name bound-env) x)]))


(define (look-up-loc l)
  (unbox l))

(define (update-loc l v)
  (set-box! l v))


(define depth 0)

(define (spaces n)
  (if (= n 0)
      ""
      (string-append " " (spaces (- n 1)))))


(define interp-limit 0)
(set! interp-limit 10000)

(define interp-calls 0)

; Interpreter for Fun expressions:
;
; env-interp : Env E -> E
;
; Given an E e, and where the state of Racket boxes corresponds to S1,
; return the E v such that
;
;              env; S1 ⊢ e ⇓ v; S2
;
; where the state of Racket boxes corresponds to S2.

(define (env-interp env e)
  (if (>= interp-calls interp-limit)
      (error "interp-limit exceeded")
      (type-case E e
        [Num (n)   (Num n)]
        [Btrue ()  (Btrue)]
        [Bfalse () (Bfalse)]
        [Location (l) (Location l)]
        [else
         (begin
           (set! interp-calls (+ interp-calls 1))
           (set! depth (+ depth 1))
           (printf "~aenvironment   ~a~n" (spaces depth) (unparse-env env))
           (printf "~aexpression    ~a~n" (spaces depth) (unparse e))
           ; (printf "interp: starting evaluation of ~a~n" (unparse e))
           (let ([result

                  (type-case E e

                    [Binop (op e1 e2)
                           (let* ([v1 (env-interp env e1)]
                                  [v2 (env-interp env e2)])
                             (if (valid-binop op v1 v2)
                                 (let ([v  (apply-binop op v1 v2)])
                                   v)
                                 (error "binop applied to invalid arguments")))]

                    [Ite (e eThen eElse)
                         (let ([v (env-interp env e)])
                           (type-case E v
                             [Btrue ()   (env-interp env eThen)]
                             [Bfalse ()  (env-interp env eElse)]
                             [else (error "Ite on a non-boolean")]))]

                    [Id (x)
                        (let ([maybe-e (look-up-id env x)])
                          (if maybe-e
                              (env-interp env maybe-e)
                              (error "unknown-id-error")))
                        ]

                    [Let (x e1 e2)
                         (let* ([v1    (env-interp env e1)]
                                [env-x (env/cons x v1 env)]
                                [v2    (env-interp env-x e2)])
                           v2)
                         ]

                    [Lam (x A eB) (Clo env (Lam x A eB))]

                    [Clo (env-old e)
                         (let ([v (env-interp env-old e)])
                           v)]

                    [App (e1 e2)
                         (let ([v1 (env-interp env e1)]
                               [v2 (env-interp env e2)])
                           (type-case E v1
                             [Clo (env-old f)
                                  (type-case E f
                                    [Lam (x A eB) (let* ([env-new (env/cons x v2 env-old)]
                                                         [v (env-interp env-new eB)])
                                                    v)]
                                    [else (error "tried to apply non-lam")])]
                             [else (error "expected a closure")]))]

                    [Rec (u B eB)
                         (let* ([EnvE (gensym "EnvE")]
                                [env-new (env/rec EnvE (env/cons u (Clo (env/id EnvE) eB) env))]
                                [v (env-interp env-new eB)])
                           v)]

                    [Pair (e1 e2)
                          (let ([v1 (env-interp env e1)]
                                [v2 (env-interp env e2)])
                            (Pair v1 v2))]

                    [Pair-case (e x1 x2 eBody)
                               (type-case E (env-interp env e)
                                 [Pair (v1 v2)
                                       (env-interp (env/cons x2 v2
                                                             (env/cons x1 v1
                                                                       env))
                                                   eBody)]
                                 [else (error "Pair-case on non-Pair")])]

                    [Downcast (A e)
                              (let* ([v  (env-interp env e)]
                                     [B  (typeof (tc/empty) v)])
                                (if (and B
                                         (subtype? B A))
                                    v
                                    (error "downcast failed")))]

                    [Ref (A e)
                         (let* ([v  (env-interp env e)]
                                [b  (box v)])
                           (Location b))]

                    [Deref (e)
                           (let ([v (env-interp env e)])
                             (type-case E v
                               [Location (b)
                                         (look-up-loc b)]
                               [else (error "Deref")]))]

                    [Setref (e1 e2)
                            (let ([v1 (env-interp env e1)])
                              (type-case E v1
                                [Location (b)
                                          (let ([v2 (env-interp env e2)])
                                            (update-loc b v2)
                                            v2)]
                                [else (error "Setref")]))]

                    [Begin (es)
                           (cond
                             [(empty? es) #f]
                             [else
                               (let ([v (env-interp env (first es))])
                                 (if (= (length es) 1)
                                   v
                                   (env-interp env (Begin (rest es)))))])]

                    [While (eG eBody)
                           (let ([v (env-interp env eG)])
                             (type-case E v
                              [Btrue ()
                                     (let ([v1 (env-interp env eBody)]
                                           [v2 (env-interp env e)])
                                       v2)]
                              [Bfalse () (Bfalse)]
                              [else #f]))]

                    [else (error "should have been handled above")]
                    )])
             (begin
               ; (printf "~acontext is  ~a~n" (spaces depth) env)
               (printf "~aevaluated to  ~a~n" (spaces depth) (unparse result))
               (set! depth (- depth 1))
               result)))]))
  )

; interp : E -> E
;
; Calls env-interp with an empty environment.
;
(define (interp e)
  (begin
    (set! interp-calls 0)
    (set! depth 0)
    (env-interp (env/empty) e)))


; look-up-type : Typing-context symbol -> Type
;
(define (look-up-type context x)
  (type-case Typing-context context
    [tc/empty ()                    (error "look-up-type: not in scope: " x)]
    [tc/cons-tp (y A context)       (if (symbol=? x y)
                                        A
                                        (look-up-type context x))]
    ))

; atomic-subtype? : Type Type -> boolean
;
; Handles subtyping for atomic types (pos, int, rat).
;
(define (atomic-subtype? A B)
  (or
   (equal? A B)               ; redundant, but avoids questions about "why is (atomic-subtype? (Tint) (Tint)) false?"
   (and (Tpos? A) (Tint? B))
   (and (Tpos? A) (Trat? B))
   (and (Tint? A) (Trat? B))
   ))

; subtype? : Type Type -> boolean
;
(define (subtype? A B)
  (and A         ; weed out stray #false results
       B
       (or
        (equal? A B)     ; Sub-refl
        ; try atomic subtyping
        (atomic-subtype? A B)
        ; try record subtyping (Problem 3)
        (type-case Type B
          [Trecord (Bflds)
                   (cond
                     [(= (length Bflds) 1)
                      (type-case Type A
                       [Trecord (Aflds)
                                (cond
                                  [(empty? Aflds) #f]
                                  [else
                                    (let ([Aname (field-type-name (first Aflds))]
                                          [Bname (field-type-name (first Bflds))])
                                        (and
                                          (if (equal? Aname Bname)
                                            (subtype? (get-field-type Aname Aflds) (get-field-type Bname Bflds))
                                            #t)
                                          (if (> (length Aflds) 1)
                                            (subtype? (Trecord (rest Aflds)) B)
                                            #t)))])]
                       [else #t])]
                     [(> (length Bflds) 1)
                      (and (subtype? A (Trecord (list (first Bflds))))
                           (subtype? A (Trecord (rest Bflds))))]
                     [else #t])]
          [else
           ; if that doesn't work, try the other rules
           (type-case Type A
             ; [Tbool () handled by else branch]
             [T* (A1 A2)   (type-case Type B [T* (B1 B2)   (and (subtype? A1 B1)
                                                                (subtype? A2 B2))]
                             [else #f])]

             [T-> (A1 A2)  (type-case Type B [T-> (B1 B2)  (and (subtype? B1 A1)  ; contravariant
                                                                (subtype? A2 B2))]
                             [else #f])]

             [Tref (A0)    (type-case Type B
                             [Tref (B0)      (and (subtype? A0 B0)
                                                  (subtype? B0 A0))]
                             [else #f])]
             [else #f])]
          ))))

; get-field-names : (listof FieldType) -> (listof symbol)
;
(define (get-field-names fieldtypes)
  (map (lambda (fieldtype) (type-case FieldType fieldtype
                             [field-type (f A)  f]))
       fieldtypes))

; intersection : (listof symbol) (listof symbol) -> (listof symbol)
;
(define (intersection list1 list2)
  (if (empty? list1)
      empty
      (let ([h  (first list1)]
            [t  (rest list1)])
        (if (member h list2)
            (cons h (intersection t list2))
            (intersection t list2)))))

; build-upper-bound : (listof FieldType) (listof FieldType) (listof symbol)
;                  -> (or false (listof FieldType))
(define (build-upper-bound Afields Bfields common-names)
  (if (empty? common-names)
      empty
      (let* ([h         (first common-names)]
             [t         (rest common-names)]

             [Atype     (get-field-type h Afields)]
             [Btype     (get-field-type h Bfields)]
             ; field type (h : Atype) in Afields
             ; field type (h : Btype) in Bfields
             [AB-upper  (upper-bound Atype Btype)])
        (if (false? AB-upper)
            ; A and B have no upper bound, so leave this field out of the result
            (build-upper-bound Afields Bfields t)
            ; add this upper bound
            (cons (field-type h AB-upper) (build-upper-bound Afields Bfields t)))
        )))

; try-record-upper-bound : Type Type -> (or false Type)
;
; If either type is not Record, returns false.
; Otherwise, returns the Record whose fields are the intersection
; of the sets of fields of each record, and whose individual field types
; are the upper-bound of each record type.
;
(define (try-record-upper-bound A B)
  (type-case Type A
    [Trecord (Afields)
             (type-case Type B
               [Trecord (Bfields)
                        ; A = Record Afields,   B = Record Bfields
                        ;
                        ; 1. Get all the field names in common.
                        (let* ([Anames        (get-field-names Afields)]
                               [Bnames        (get-field-names Bfields)]
                               [common-names  (intersection Anames Bnames)])
                          ; 2. Build the upper bound.
                          (Trecord (build-upper-bound Afields Bfields common-names)))
                        ]
               [else #f])]
    [else #f])
  )

; upper-bound : Type Type -> (or false Type)
;
(define (upper-bound A B)
  (and A     ; weed out stray #false results
       B
       (if (subtype? A B)
           B              ; A <: B, so upper bound of A and B is B
           (if (subtype? B A)
               A          ; B <: A, so upper bound of A and B is A

               ; neither A <: B nor B <: A;
               ; however, with records there may be an upper bound
               (try-record-upper-bound A B)))))

; lower-bound : Type Type -> (or false Type)
;
(define (lower-bound A B)
  (if (false? A)
      B
      (if (false? B)
          A
          (if (subtype? A B)
              A              ; A <: B, so lower bound of A and B is A
              (if (subtype? B A)
                  B          ; B <: A, so lower bound of A and B is B
                  #false)))))


; type=? : Type Type -> boolean
;
(define (type=? A B)
  (and A         ; weed out stray #false results
       B
       (type-case Type A
         ; [Tnum ()  handled by else branch]
         ; [Tbool () handled by else branch]
         [T* (A1 A2)   (type-case Type B [T* (B1 B2)   (and (type=? A1 B1)
                                                            (type=? A2 B2))]
                         [else #f])]

         [T-> (A1 A2)  (type-case Type B [T-> (B1 B2)  (and (type=? B1 A1)
                                                            (type=? A2 B2))]
                         [else #f])]

         [Tref (A0)    (type-case Type B
                         [Tref (B0)     (type=? A0 B0)]
                         [else #f])]
         [else
          (equal? A B)])))


; op-signature : Op -> Type
;
(define (op-signature op)
  (let* ([rat*rat        (T* (Trat) (Trat))]
         [int*int        (T* (Tint) (Tint))]
         [pos*pos        (T* (Tpos) (Tpos))]

         [rat*rat->rat   (T-> rat*rat (Trat))]
         [int*int->int   (T-> int*int (Tint))]
         [pos*pos->pos   (T-> pos*pos (Tpos))]

         [rat*rat->bool  (T-> rat*rat (Tbool))])
    (type-case Op op
      [Plusop ()     (list pos*pos->pos int*int->int rat*rat->rat)]
      [Minusop ()    (list int*int->int rat*rat->rat)]
      [Lessthanop () (list rat*rat->bool)]
      [Equalsop ()   (list rat*rat->bool)]
      )))



(define (typeof-app tc eFun eArg)
  (let* ([AFun (typeof tc eFun)]
         [AArg (typeof tc eArg)])
    (and AFun
         (type-case Type AFun
           [T-> (A1 A2)  (if (subtype? AArg A1)   ; subtype call
                             A2
                             #false)]
           [else          #false]))))

;
; typeof : Typing-context E -> (or false Type)
;
(define (typeof tc e)
  (type-case E e

    [Num (n)               (if (not (rational? n))   ; sadly, even Racket's definition of rational is interesting
                               #false
                               (if (not (exact-integer? n))
                                   (Trat)
                                   (if (not (>= n 0))
                                       (Tint)
                                       (Tpos)))
                               )]

    [Binop (op e1 e2)      (let* ([A1 (typeof tc e1)]
                                  [A2 (typeof tc e2)])
                             (define (try-op-type AOp)
                               (type-case Type AOp
                                 [T-> (domain range)
                                      (if (subtype? (T* A1 A2) domain)
                                          range
                                          #false)]
                                 [else (error "strange op signature: " op " : " (op-signature op))]))
                             (and A1
                                  A2
                                  (let* ([ranges_or_falses  (map try-op-type (op-signature op))]
                                         [ranges            (filter (lambda (x) (not (false? x))) ranges_or_falses)])
                                    (foldl lower-bound (first ranges) (rest ranges)))
                                  ))]

    [Bfalse ()             (Tbool)]
    [Btrue ()              (Tbool)]

    [Ite (e eThen eElse)   (and (subtype? (typeof tc e) (Tbool))    ; subtype call
                                (let ([AThen (typeof tc eThen)]
                                      [AElse (typeof tc eElse)])
                                  ; (and (type=? AThen AElse)
                                  ;     AThen)
                                  (upper-bound AThen AElse)
                                  ))]

    [Id (x)                (let ([A (look-up-type tc x)])
                             (or A
                                 (begin
                                   (printf "unbound identifier ~v~n" x)
                                   #false)))]

    [Let (x e eBody)      (let ([A (typeof tc e)])
                            (and A
                                 (let* ([tc-extended  (tc/cons-tp x A tc)]
                                        [B            (typeof tc-extended eBody)])
                                   B)))]

    [Lam (x A eBody)       (let* ([tc-extended  (tc/cons-tp x A tc)]
                                  [B (typeof tc-extended eBody)])
                             (and B
                                  (T-> A B)))]

    [Rec (u B eBody)       (let* ([tc-extended  (tc/cons-tp u B tc)]
                                  [B2 (typeof tc-extended eBody)])
                             (and (type=? B B2)
                                  B))]

    [App (eFun eArg)       (typeof-app tc eFun eArg)]

    [Pair (e1 e2)
          (let* ([A1 (typeof tc e1)]
                 [A2 (typeof tc e2)])
            (and A1
                 A2
                 (T* A1 A2)
                 ))
          ]

    [Pair-case (e x1 x2 eBody)
               (let* ([A (typeof tc e)])
                 (and A
                      (type-case Type A
                        [T* (A1 A2)
                            (typeof (tc/cons-tp x2 A2
                                                (tc/cons-tp x1 A1
                                                            tc)) eBody)]
                        [else #false])
                      ))
               ]

    [Ref (A e)
         (let ([B (typeof tc e)])
           (and B
                (subtype? B A)
                (Tref A)))
         ]
    [Deref (eRef)
           (let ([ARef (typeof tc eRef)])
             (and ARef
                  (type-case Type ARef
                    [Tref (A)   A]
                    [else        #false])))
           ]
    [Setref (eRef e)
            (let ([ARef (typeof tc eRef)])
              (and ARef
                   (type-case Type ARef
                     [Tref (A)  (let ([Ae (typeof tc e)])
                                  (and (subtype? Ae A)
                                       Ae))]
                     [else       #false])))
            ]

    [Downcast (A e)
              (let ([B  (typeof tc e)])
                (and B
                     (subtype? A B)
                     A))]

    [Record (fields)
            (if (empty? fields)
                (Trecord empty)
                (type-case Field (first fields)
                  [fld (f1 contents)
                       (let ([A1 (typeof tc contents)]
                             [Arest (typeof tc (Record (rest fields)))])
                         (and A1
                              Arest
                              (type-case Type Arest
                                [Trecord (Arest)
                                         (Trecord (cons (field-type f1 A1) Arest))]
                                [else (error "impossible")]))
                         )])
                )]

    [Dot (e name)      (let ([Arecord  (typeof tc e)])
                         (and Arecord
                              (type-case Type Arecord
                                [Trecord (field-types)
                                         (get-field-type name field-types)]
                                [else #false])
                              ))]

    [Begin (es)        (case (length es)
                         [(0)   (error "typeof: Begin with no expressions")]
                         [(1)   (typeof tc (first es))]
                         [else  (and (typeof tc (first es))
                                     (typeof tc (Begin (rest es))))])]

    [While (eG eB)     (and (subtype? (typeof tc eG) (Tbool))
                            (typeof tc eB)
                            (Tbool))]

    [Clo (env e)       (error "typeof: Clo: not handled")]
    [Location (loc)    (error "typeof: Location: not handled")]
    ))

;
; get-field-type : symbol (listof FieldType) -> (or false Type)
;
(define (get-field-type key field-types)
  (if (empty? field-types)
      #false
      (type-case FieldType (first field-types)
        [field-type (name A)  (if (symbol=? key name)
                                  A
                                  (get-field-type key (rest field-types)))]
        )))

(define (typeof-program e)
  (typeof (tc/empty) e))


(define (unparse-env env)
  (type-case Env env
    [env/empty ()         `Ø]
    [env/cons (x e env)   `(,x = ,(unparse e) \, ,(unparse-env env))]
    [env/id (x)           x]
    [env/rec (x env)      `(Env-Rec ,x ,(unparse-env env))]
    ))

(define (unparse-op op)
  (type-case Op op
    [Plusop ()      `+]
    [Minusop ()     `-]
    [Equalsop ()    `=]
    [Lessthanop ()  `<]))

(define (unparse-fieldtype ft)
  (type-case FieldType ft
    [field-type (name A)  `(,name ,(unparse-type A))]))

; unparse-type : (or false Type) -> (or false sexp)
;
; Given abstract syntax type A, return its concrete syntax (s-expression).
; Or, if given #false, return #false.
(define (unparse-type A)
  (if A
      (type-case Type A
        [Trat ()             `rat]
        [Tint ()             `int]
        [Tpos ()             `pos]
        [Tbool ()            `bool]
        [T->  (domain range) `(-> ,(unparse-type domain) ,(unparse-type range))]
        [T*   (A1 A2)        `(*  ,(unparse-type A1) ,(unparse-type A2))]
        [Tref (A0)           `(Tref ,(unparse-type A0))]
        [Trecord (fieldtypes) (cons 'record (map unparse-fieldtype fieldtypes))]
        )
      #false))

(define (unparse-field field)
  (type-case Field field
    [fld (name e)    `(,name ,(unparse e))]))

(define (unparse e)
  (type-case E e
    [Num (n)             n]
    [Binop (op e1 e2)    `(,(unparse-op op) ,(unparse e1) ,(unparse e2))]
    [Id (x)              x]
    [Let (x e1 eB)       `(Let ,x ,(unparse e1) ,(unparse eB))]
    [Lam (x A body)      `(Lam ,x ,(unparse-type A) ,(unparse body))]
    [App (e1 e2)         `(App ,(unparse e1) ,(unparse e2))]
    [Rec (u B body)      `(Rec ,u ,(unparse-type B) ,(unparse body))]
    [Bfalse ()           `Bfalse]
    [Btrue ()            `Btrue]
    [Ite (e e1 e2)       `(Ite ,(unparse e) ,(unparse e1) ,(unparse e2))]
    [Clo (env e)         `(Clo ,(unparse-env env) ,(unparse e))]
    [Pair (e1 e2)              `(Pair ,(unparse e1) ,(unparse e2))]
    [Pair-case (e x1 x2 body)  `(Pair-case ,(unparse e) (,x1 ,x2 => ,(unparse body)))]
    [Ref (A e1)          `(Ref ,(unparse-type A) ,(unparse e1))]
    [Deref (e1)          `(Deref ,(unparse e1))]
    [Setref (e1 e2)      `(Setref ,(unparse e1) ,(unparse e2))]
    [Location (l)        `(Location ,l)]
    [Downcast (A e)      `(Downcast ,(unparse-type A) ,(unparse e))]
    [Record (fields)     `(Record ,(append* (map unparse-field fields)))]
    [Dot (e name)        `(Dot ,(unparse e) ,name)]
    [Begin (es)          `(Begin ,(map unparse es))]
    [While (eG eB)       `(While ,(unparse eG) ,(unparse eB))]
    ))


(interp (parse '{Ref int 1}))

(interp (parse '{Let r {Ref int 1} {Deref r}}))

(interp (parse '{Let r {Ref int 1}
                     {Let r1 {Deref r}
                          {Let a {Setref r 2}
                               {Let r2 {Deref r}
                                    {+ r1 r2}}}}}))

; subtype-parse : sexp sexp -> boolean
;
(define (subtype-parse A-sexp B-sexp)
  (subtype? (parse-type A-sexp) (parse-type B-sexp)))


"test upper-bound"
; incompatible z fields; z field dropped:
(typeof-program (parse '{Ite Btrue
                             {Record {x 1} {y -3} {z Bfalse}}
                             {Record {x 5} {y 9.5} {z 0}}}))

; compatible z fields; z field kept:
(typeof-program (parse '{Ite Btrue
                             {Record {x 1} {y -3} {z -1.5}}
                             {Record {x 5} {y 9.5} {z 0}}}))

; no fields in common; record type with no fields:
(typeof-program (parse '{Ite Btrue
                             {Record {x 1} {y -3} {z -1.5}}
                             {Record {aa 5} {bb 9.5}}}))


"start record subtyping tests"
(subtype-parse 'int '{record})
(subtype-parse '{record {x pos} {y int} {z rat}}
               '{record {x pos} {y int} {z rat}})

(subtype-parse '{record {x pos} {y int} {z rat}}
               '{record {x pos} {z rat} {y int}})  ; should succeed (permutation)

(subtype-parse '{record {x pos} {y int} {z rat}}
               '{record {x rat} {y rat} {z rat}})  ; should succeed (depth)

(subtype-parse '{record {x pos} {y int} {z rat}}
               '{record {x rat} {y pos} {z rat}})  ; should fail

"width:"
(subtype-parse '{record {x pos} {y pos} {z rat}}
               '{record {x rat}         {z rat}})  ; should succeed (width)

"width + depth:"
(subtype-parse '{record {x pos} {y pos} {z rat}}
               '{record {x int}         {z rat}})  ; should succeed (width + depth)

"should fail:"
(subtype-parse '{record {x int}         {z rat}}
               '{record {x pos} {y pos} {z rat}})  ; should fail (width reversed)


(define (print-typeof sexp)
  (printf "the type of~n~a~nis:  ~a~n~n"
          sexp
          (unparse-type (typeof-program (parse sexp)))))

(print-typeof '{Lam x pos {+ x x}})

(interp (parse '{Setref {Ref rat 0} -66}))

(print-typeof '{Ref pos 0})               ;

(print-typeof '{Setref {Ref pos 0} 3})    ;   :-)

(print-typeof '{Setref {Ref int 0} -3})   ;   :-)

(print-typeof '{Downcast pos 2})      ; : pos
(print-typeof '{Downcast rat 2})      ; useless, but well-typed
(print-typeof '{Downcast rat -2.5})   ; : rat
(print-typeof '{Downcast pos -3})     ; : pos, but evaluation will fail since -3 is not pos

(print-typeof '{Let to-pos {Lam x int {Ite {< -1 x}
                                           0
                                           {Downcast pos x}}}
                    {Pair {App to-pos 5}
                          {App to-pos -3}}})

(interp (parse '{Let to-pos {Lam x int {Ite {< x 0}
                                            0
                                            {Downcast pos x}}}
                     {Pair {App to-pos 5}
                           {App to-pos -3}}}))

(test (subtype? (Trecord (list (field-type 'a (Tint))))
                (Trecord (list (field-type 'a (Trat)))))
      #t)

(test (subtype? (Trecord (list (field-type 'a (Trat))))
                (Trecord (list (field-type 'a (Tint)))))
      #f)

(test (subtype? (Trecord (list (field-type 'a (Tint))))
                (Trecord (list (field-type 'b (Tpos))
                               (field-type 'a (Trat)))))
      #t)

(test (subtype? (Trecord (list (field-type 'b (Tint))))
                (Trecord (list (field-type 'b (Trat))
                               (field-type 'a (Tpos)))))
      #t)

(test (subtype? (Trecord (list (field-type 'a (Tbool))))
                (Trecord (list (field-type 'b (Tpos))
                               (field-type 'a (Trat)))))
      #f)

(test (subtype? (Trecord (list (field-type 'b (Tbool))))
                (Trecord (list (field-type 'b (Trat))
                               (field-type 'a (Tpos)))))
      #f)

(test (subtype? (Trecord (list (field-type 'b (Tpos))
                               (field-type 'a (Tpos))))
                (Trecord (list (field-type 'b (Trat))
                               (field-type 'a (Trat)))))
      #t)

(test (subtype? (Trecord (list (field-type 'b (Tpos))
                               (field-type 'a (Tpos))))
                (Trecord (list (field-type 'b (Trat))
                               (field-type 'a (Tbool)))))
      #f)

(test (subtype? (Trecord (list (field-type 'b (Tpos))
                               (field-type 'a (Tpos))))
                (Trecord empty))
      #t)

(test (subtype? (Trecord empty)
                (Trecord (list (field-type 'b (Tpos))
                               (field-type 'a (Tpos)))))
      #f)

(test (interp (parse '{Begin 1}))
      (Num 1))

(test (interp (parse '{Let x {Ref int 2} {Begin {Setref x 1} {Deref x}}}))
      (Num 1))

; test While  (The derivations in Problem 2b are related.)
;
; (interp (parse '{Let x {Ref int 2} {While {< 1 {Deref x}} {Setref x 0}}}))
(test (interp (parse '{Let x {Ref int 10} {Begin {While {< 0 {Deref x}} {Setref x {- {Deref x} 1}}} {Deref x}}}))
      (Num 0))
