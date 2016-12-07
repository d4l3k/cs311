#lang plai

; CPSC 311 2016W1
; Assignment 6: bidirectional typing
; VERSION 2, 2016-11-27; fixes bugs in type-subst

;  <E> ::= <number>
;        | {+ <E> <E>}
;        | {- <E> <E>}
;        | {= <E> <E>}
;        | {< <E> <E>}
;        | {Let <symbol> <E> <E>}
;        | {Let <symbol> : <Type> <E> <E>}  ----> syntactic sugar for
;                                                 {Let <symbol> {Anno <E> <Type>} <E>}
;        | <symbol>
;        | {Lam <symbol> <E>}
;        | {App <E> <E>}
;
;        | {Rec <symbol> <E>}
;        | {Rec <symbol> <Type> <E>}   -----> syntactic sugar for {Anno {Rec <symbol> <E>} <Type>}
;
;        | {Let* { <symbol> <E> }... <E>}     -----> syntactic sugar for Let
;                                ^
;                                zero or more
;        | Btrue
;        | Bfalse
;        | {Ite <E> <E> <E>}         ; "if-then-else"
;
;        | {Pair <E> <E>}
;        | {Pair-case <E> {<symbol> <symbol> => <E>}}
;
;        | {Anno <E> <Type>}
;
;        | {All <symbol> <E>}
;        | {All <symbol> <symbol>... <E>}  ; syntactic sugar for
;                                          ;    {All <symbol> {All <symbol> <E>}}
;        | {At <E> <Type>}
;
;        | Unit
;        | {Inl <E>}
;        | {Inr <E>}
;        | {Sum-case <E> {Inl <symbol> => <E>} {Inr <symbol> => <E>}}
;
;  <Type> ::= pos
;           | int
;           | rat
;           | bool
;           | {* <Type> <Type>}
;           | {-> <Type>...}
;                       ^ one or more
;           | {all <symbol> <Type>}
;                         ^ one or more:  {all a b <Type>} syntactic sugar for {all a {all b <Type>}}
;           | <symbol>
;
;           | unit
;           | {+ <Type> <Type>}
;
;           | {mu <symbol> <Type>}
;
;           | {sect <Type> <Type>}  ; for bonus problem

(define-type Type
  [Tpos]
  [Tint]
  [Trat]
  [Tbool]
  [T*       (t1 Type?)     (t2 Type?)]
  [T->      (domain Type?) (range Type?)]
  [Tall     (a symbol?)    (t  Type?)]
  [Tvar     (a symbol?)]
  [Tunit]
  [T+       (left Type?)   (right Type?)]
  [Tmu      (a symbol?)    (t  (and/c Type? (not/c Tvar?)))]

  ; For bonus problem
  [Tsect    (left Type?)   (right Type?)]
  )

(define-type Typing-context
  [tc/empty]
  [tc/cons-tp    (x symbol?) (A Type?) (rest Typing-context?)]
  [tc/cons-tyvar (a symbol?)           (rest Typing-context?)]
  )

(define-type Op
  [Plusop]
  [Minusop]
  [Equalsop]
  [Lessthanop])

; Abstract syntax of E (Fun expressions):
(define-type E
  [Anno (e E?) (t Type?)]

  ; numbers
  [Num (n number?)]
  [Binop (op Op?) (lhs E?) (rhs E?)]

  ; binding
  [Let (name symbol?) (named-expr E?) (body E?)]
  [Id (name symbol?)]
  ;  [Let* (bindings (listof Binding?)) (body E?)]

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

  ; polymorphism
  [All (tyvar symbol?) (body E?)]
  [At (poly-expr E?) (instance Type?)]

  ; unit
  [Unit]

  ; sums
  [Inl (contents E?)]
  [Inr (contents E?)]
  [Sum-case  (scrutinee E?)
             (left-contents symbol?)  (left-branch E?)
             (right-contents symbol?) (right-branch E?)]
  )

; parse-op : symbol? -> E?
;
(define (parse-op s)
  (case s
    [(+) (Plusop)]
    [(-) (Minusop)]
    [(<) (Lessthanop)]
    [(=) (Equalsop)]
    [else (error "impossible")]))

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

         [(Let*) (case arg-count
                   [(0)  (error "parse: Let* with no body")]
                   [(1)  (parse (first args))]
                   [else ; arg-count >= 2
                    (let ([binding1-sexp (first args)])
                      (if (list? binding1-sexp)
                          (parse (append (list 'Let)
                                         binding1-sexp
                                         (list (cons 'Let* (rest args)))))
                          (error "parse: each Let* binding must be bracketed")))]
                   )]

         [(Ite) (if (= arg-count 3)
                    (Ite (parse (first args))
                         (parse (second args))
                         (parse (third args)))
                    (error "parse needs exactly 3 arguments"))]

         [(Lam) (if (= arg-count 2)
                    (if (symbol? (first args))
                        (Lam (first args) (parse (second args)))
                        (error "parse: Lam must be followed by an identifier"))
                    (error "parse: malformed `Lam'"))]

         [(App) (if (= arg-count 2)
                    (App (parse (first args)) (parse (second args)))
                    (error "parse: App needs 1 function and 1 argument"))]

         [(Rec) (case arg-count
                  [(2)  (if (symbol? (first args))
                            (Rec (first args) (parse (second args)))
                            (error "parse: Rec must be followed by an identifier"))]
                  [(3)  (Anno (Rec (first args)
                                   (parse (third args)))
                              (parse-type (second args)))]
                  [else (error "parse: malformed `Rec'")])]

         [(Let) (case arg-count
                  [(3)
                   (let ([name (first args)]
                         [named-sexp (second args)]
                         [body-sexp  (third args)])
                     (if (symbol? name)
                         (Let name (parse named-sexp) (parse body-sexp))
                         (error "parse: malformed `Let'")))]
                  [(5)
                   (let ([name        (first args)]
                         [colon-sexp  (second args)]
                         [A-sexp      (third args)]
                         [named-sexp  (fourth args)]
                         [body-sexp   (fifth args)])
                     (if (and (symbol? name) (symbol=? ': colon-sexp))
                         (Let name
                              (Anno (parse named-sexp) (parse-type A-sexp))
                              (parse body-sexp))
                         (error "parse: malformed `Let'")))]
                  [else (error "parse: malformed `Let'")])]

         [(Pair) (if (= arg-count 2)
                     (Pair (parse (first args))
                           (parse (second args)))
                     (error "parse: malformed `pair'"))]

         [(Pair-case) (parse-pair-case arg-count args)]

         [(Anno) (if (= arg-count 2)
                     (let ([body (parse (first args))]
                           [type (parse-type (second args))])
                       (Anno body type))
                     (error "parse: malformed `Anno'"))]

         [(All) (if (or (< arg-count 2) (not (symbol? (first args))))
                    (error "parse: malformed `All'")
                    (if (= arg-count 2)
                        (All (first args) (parse (second args)))
                        (All (first args) (parse (cons 'All (rest args))))
                        ))]

         [(At) (if (= arg-count 2)
                   (let ([body (parse (first args))]
                         [type (parse-type (second args))])
                     (At body type))
                   (error "parse: malformed `At'"))]

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

         [else (error "parse: syntax error")]))]

    [else (error "parse: syntax error")]))

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

; parse-pair-case : positive-integer (listof sexp) -> E
;
(define (parse-pair-case arg-count args)
  (if (= arg-count 2)

      (let ([scrutinee (parse (first args))]
            [inner-sexp (second args)])

        (if (and (list? inner-sexp)
                 (= (length inner-sexp) 4)
                 (symbol=? (third inner-sexp) '=>))

            (let ([name1 (first inner-sexp)]
                  [name2 (second inner-sexp)]
                  [body (parse (fourth inner-sexp))])

              (Pair-case scrutinee name1 name2 body))

            (error "parse: malformed `Pair-case'")))

      (error "parse: malformed `Pair-case'")))

(define (build-> types)
  (if (= (length types) 2)
      (T-> (first types) (second types))
      (T-> (first types) (build-> (rest types)))))

(define (parse-type sexp)
  (cond
    [(symbol? sexp)
     (case sexp
       [(rat)    (Trat)]
       [(int)    (Tint)]
       [(pos)    (Tpos)]
       [(num)    (Trat)]   ; for compatibility
       [(bool)   (Tbool)]
       [(unit)   (Tunit)]
       [else     (Tvar sexp)])]
    [(list? sexp)
     (if (empty? sexp)
         (error "parse-type: empty")
         (let*
             ([head      (first sexp)]
              [args      (rest sexp)]
              [arg-count (length args)])

           (case head
             [(*)    (T* (parse-type (first args))
                         (parse-type (second args)))]
             [(+)    (T+ (parse-type (first args))
                         (parse-type (second args)))]
             [(->)   (build-> (map parse-type args))]
             [(all)  (if (= 2 arg-count)
                         (Tall (first args) (parse-type (second args)))
                         (Tall (first args) (parse-type (cons 'all (rest args)))))
                     ]
             [(mu)   (if (and (= 2 arg-count) (symbol? (first args)))
                         (Tmu (first args) (parse-type (second args)))
                         (error "invalid arguments for Tmu"))]

             ; For bonus problem
             [(sect) (Tsect (parse-type (first args))
                            (parse-type (second args)))]

             [else   (error "unknown type constructor " head)])))]
    [else (error "unknown animal in type")]))


(define (look-up-type context x)
  (type-case Typing-context context
    [tc/empty ()  (error "look-up-type: " x  " not in scope")]
    [tc/cons-tp (y A context)       (if (symbol=? x y)
                                        A
                                        (look-up-type context x))]
    [tc/cons-tyvar (a context)      (look-up-type context x)]
    ))

; fresh-tyvar : Typing-context symbol -> symbol
(define (fresh-tyvar context base)
  (gensym base))

; free? : symbol Type -> boolean
;
(define (free? a B)
  (type-case Type B
    [Trat ()         #f]
    [Tint ()         #f]
    [Tpos ()         #f]
    [Tbool ()        #f]
    [Tunit ()        #f]
    [T* (B1 B2)      (or (free? a B1) (free? a B2))]
    [T+ (B1 B2)      (or (free? a B1) (free? a B2))]
    [T-> (B1 B2)     (or (free? a B1) (free? a B2))]
    [Tall (b B0)     (if (symbol=? a b)
                         #f
                         (free? a B0))]
    [Tvar (b)        (symbol=? a b)]
    [Tmu  (b B0)     (if (symbol=? a b)
                         #f
                         (free? a B0))]

    ; For bonus problem
    [Tsect (B1 B2)   (or (free? a B1) (free? a B2))]
    ))

; type-subst : Typing-context Type symbol Type -> Type
;
; (type-subst tc A a B) = Bsubst
; if
; [A/a]B = Bsubst
;
(define (type-subst context A a B)
  (let ([self (lambda (B) (type-subst context A a B))])
    (type-case Type B
      [Trat ()       (Trat)]
      [Tint ()       (Tint)]
      [Tpos ()       (Tpos)]
      [Tbool ()      (Tbool)]
      [Tunit ()      (Tunit)]
      [T*  (B1 B2)   (T*  (self B1) (self B2))]
      [T+  (B1 B2)   (T+  (self B1) (self B2))]
      [T-> (B1 B2)   (T-> (self B1) (self B2))]
      [Tall (b B0)
            (if (symbol=? a b)
                (Tall b B0)
                (if (free? b A)
                    (let* ([fresh-b    (fresh-tyvar context b)]
                           [B0-renamed (type-subst context (Tvar fresh-b) b B0)])
                      (Tall fresh-b
                            (type-subst (tc/cons-tyvar fresh-b context)
                                        A
                                        a
                                        B0-renamed)))
                    (Tall b (self B0))))]
      [Tvar (b)      (if (symbol=? a b)
                         A
                         (Tvar b))]
      [Tmu (b B0)
           (if (symbol=? a b)
               (Tmu b B0)
               (if (free? b A)
                   (let* ([fresh-b    (fresh-tyvar context b)]
                          [B0-renamed (type-subst context (Tvar fresh-b) b B0)])
                     (Tmu fresh-b (type-subst (tc/cons-tyvar fresh-b context)
                                              A
                                              a
                                              B0-renamed)))
                   (Tmu b (self B0))))]

      ; For bonus problem
      [Tsect (B1 B2) (Tsect (self B1) (self B2))]
      )))


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

; subtype? : Typing-context Type Type -> boolean
;
(define (subtype? context A B)
  (and A         ; weed out stray #false results
       B
       (or
        (equal? A B)     ; Sub-refl
        ; try atomic subtyping
        (atomic-subtype? A B)
        ; if that doesn't work, try the other rules
        (type-case Type B
          [Tmu (b B0) (type-case Type A
                        [Tmu (a A0) (subtype? context (type-subst context (Tvar b) a B0) B0)]
                        [else (subtype? context A (type-subst context B b B0))])]
          [else
           (type-case Type A
             ; [Tbool () handled by else branch]
             [T* (A1 A2)   (type-case Type B
                             [T* (B1 B2) (and (subtype? context A1 B1)
                                              (subtype? context A2 B2))]
                             [else #f])]

             [T+ (A1 A2)   (type-case Type B
                             [T+ (B1 B2) (and (subtype? context A1 B1)
                                              (subtype? context A2 B2))]
                             [else #f])]

             [T-> (A1 A2)  (type-case Type B
                             [T-> (B1 B2) (and (subtype? context B1 A1)  ; contravariant
                                               (subtype? context A2 B2))]
                             [else #f])]

             [Tmu (a A0)   (subtype? context (type-subst context A a A0) B)]

             [else #f])]))))

; op-signature : Op -> listof Type
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

; type-binop : Typing-context E E (listof Type) -> (or false Type)
;
; (type-binop tc e1 e2 op-types)
; returns B if:
;     op-types contains A1 * A2 -> B
; and e1 checks against A1
; and e2 checks against A2.
(define (type-binop tc e1 e2 op-types)
  (if (empty? op-types)
      #false
      (let ([AOp (first op-types)])
        (type-case Type AOp
          [T-> (domain range)
               (if (check tc (Pair e1 e2) domain)
                   range
                   (type-binop tc e1 e2 (rest op-types)))]
          [else (error "strange op signature: " AOp)]))))

; inner-synth : Typing-context E -> (or false Type)
;
; (inner-synth context e) returns A if there exists A such that
;
;   Γ ⊢ e ⇒ A
;
; by any rule *except* Synth-mu.  Also see `synth`, below.
;
(define (inner-synth context e)
  (printf "inner-synth ~a => ... ~n" (unparse e))
  (type-case E e
    [Anno (e0 A0)     ; Synth-anno
          (and  (check context e0 A0)
                A0)]

    [Num (n)
         (if (not (rational? n))   ; sadly, even Racket's definition of rational is interesting
             #false
             (if (not (exact-integer? n))
                 (Trat)                     ; Synth-rat
                 (if (not (>= n 0))
                     (Tint)                 ; Synth-int
                     (Tpos)))               ; Synth-pos
             )]

    [Pair (e1 e2)                           ; Synth-pair
          (let ([A1 (synth context e1)]
                [A2 (synth context e2)])
            (and A1
                 A2
                 (T* A1 A2)))]

    [Binop (op e1 e2)    ; Synth-binop, roughly
           (type-binop context e1 e2 (op-signature op))
           ]

    [Id (x)  ; Synth-var
        (look-up-type context x)]

    [Let (x e1 eB)     ; Synth-let
         (let ([A1 (synth context e1)])
           (and A1
                (synth (tc/cons-tp x A1 context) eB)))]

    [App (eFun eArg)   ; Synth-app
         (let ([Afun (synth context eFun)])
           (type-case Type Afun
             [T-> (A B)   (and (check context eArg A)
                               B)]
             [else #false]))]

    [Bfalse ()        (Tbool)]   ; Synth-btrue
    [Btrue ()         (Tbool)]   ; Synth-bfalse

    ;[Inl (e) (T+ (synth context e) (Tunit))]
    ;[Inr (e) (T+ (Tunit) (synth context e))]

    [At (e Ainstance)   ; Synth-at
        (let ([A (synth context e)])
          (and A
               (type-case Type A
                 [Tall (b B0)
                       (type-subst context Ainstance b B0)]
                 [else #false])))]

    [Unit ()          (Tunit)]   ; Synth-unit

    [else             (error "can't synthesize type for " e)]))

; synth : Typing-context E -> (or false Type)
;
; (synth tc e) returns A if there exists A such that
;
;   Γ ⊢ e ⇒ A
;
; by *any* rule, including Synth-mu.
; Currently it doesn't try to use Synth-mu; that's part of Problem 2b.
;
(define (synth context e)
  (let ([A (inner-synth context e)])
    (and A
         (type-case Type A
                    [Tmu (b B)
                         (type-subst context A b B)]
                    [else A]))))

; check : Typing-context E Type -> boolean
;
; (check context e A) returns #true if e checks against A, #false otherwise
;
;   Γ ⊢ e ⇐ A
;
(define (check context e A)
  (printf "check ~a <= ~a~n" (unparse e) (unparse-type A))
  (type-case Type A
    [Tmu (b B)
         (check context e (type-subst context A b B))]
    [else
     (type-case E e
       [Lam (x eBody)             ; Check-lam
            (type-case Type A
              [T-> (A1 A2)
                   (check (tc/cons-tp x A1 context) eBody A2)]
              [else #false])]

       [Rec (u e0)                ; Check-rec
            (check (tc/cons-tp u A context) e0 A)]

       [Let (x e1 eB)             ; Check-let
            (let ([A1 (synth context e1)])
              (and A1
                   (check (tc/cons-tp x A1 context)
                          eB
                          A)))]

       [Pair (e1 e2)              ; Check-pair
             (type-case Type A
               [T*  (A1 A2)
                    (and (check context e1 A1)
                         (check context e2 A2))]
               [else #false])]

       [Inl (eL)                  ; Check-inl
            (type-case Type A
              [T+ (A1 A2)
                  (check context eL A1)]
              [else #false])]

       [Inr (eR)                  ; Check-inr
            (type-case Type A
              [T+ (A1 A2)
                  (check context eR A2)]
              [else #false])]

       [Ite (scrutinee then-branch else-branch)     ; Check-ite
            (and (check context scrutinee (Tbool))
                 (check context then-branch A)
                 (check context else-branch A))]

       [Pair-case (scrutinee x1 x2 body)            ; Check-pair-case
                  (let ([APair (synth context scrutinee)])
                    (and APair
                         (type-case Type APair
                           [T* (A1 A2)
                               (let ([context-x1-x2  (tc/cons-tp x2 A2 (tc/cons-tp x1 A1 context))])
                                 (check context-x1-x2 body A))]
                           [else #false])))]


       [All (a e)                 ; Check-all
            (type-case Type A
              [Tall (b B)
                    (let ([A   (type-subst context (Tvar a) b B)]
                          [context-a (tc/cons-tyvar a context)])
                      (check context-a e A))]
              [else #false])]

       [Sum-case (e x1 e1 x2 e2)
                 (let ([ASum (synth context e)])
                   (and ASum
                        (type-case Type ASum
                                   [T+ (A1 A2)
                                       (and (check (tc/cons-tp x1 A1 context) e1 A)
                                            (check (tc/cons-tp x2 A2 context) e2 A))]
                                   [else #f])))]


       [else   ; can't use any of the Check- rules that need a specific kind of expression,
        ;  so try Check-sub, which potentially works on any kind of expression
        (let ([Asynth (synth context e)])
          (if (subtype? context Asynth A)
              #true
              #false ; (error "expression " e " synthesized type " Asynth " but checking against " A)
              ))])]))

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

    [Anno (e t)  (Anno (subst e2 x e) t)]
    [At (e t)    (At (subst e2 x e) t)]

    [All (a e)   (All a (subst e2 x e))]

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

    [Unit ()                  #true]
    [Inl (eL)                 (value? eL)]
    [Inr (eR)                 (value? eR)]

    [Anno (e A)               (value? e)]

    [else                     #false]))

; racket-boolean-to-Fun-boolean : bool? -> E?
;
; Postcondition: result is Bfalse or Btrue
;
(define (racket-boolean-to-Fun-boolean b)
  (if b
      (Btrue)
      (Bfalse)))



; valid-binop : Op? E? E? -> boolean?
;
; valid-binop op v1 v2 returns true iff v1 and v2 are consistent Let op:
;    If op is Plusop or Minusop, then v1 and v2 must be nums.
;    If op is Equalsop or Lessthanop, then v1 and v2 must be nums.
;
; Precondition: v1 and v2 are values (i.e., num, lam, Bfalse, or Btrue).

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
; apply-binop op v1 v2 Applies op to v1 and v2, returning an expression.
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
; interp : E -> E
;
; Given an E e, return the E v such that
;
;                e ⇓ v
(define (interp e)
  (type-case E e

    [Num (n)     (Num n)]
    [Lam (x eB)  (Lam x eB)]
    [Bfalse ()   (Bfalse)]
    [Btrue ()    (Btrue)]
    [Unit ()     (Unit)]

    [App (e1 e2)
         (let ([v1 (interp e1)])
           (type-case E v1
             [Lam (x eB)
                  (let* ([v2 (interp e2)]
                         [v (interp (subst v2 x eB))])
                    v)]
             [else (error "tried to Apply non-Lam")]
             ))]

    [Rec (u eB)
         (let ([v (interp (subst (Rec u eB) u eB))])
           v)]

    [Binop (op e1 e2)
           (let* ([v1 (interp e1)]
                  [v2 (interp e2)])
             (if (valid-binop op v1 v2)                 ; UNNECESSARY
                 (let ([v  (apply-binop op v1 v2)])
                   v)
                 (error "Binop Applied to invalid arguments")))]

    [Ite (eCond eThen eElse)
         (let ([vCond (interp eCond)])
           (type-case E vCond
             [Btrue ()   (interp eThen)]
             [Bfalse ()  (interp eElse)]
             [else (error "Ite on a non-boolean")]))]

    [Pair (e1 e2)
          (let ([v1  (interp e1)]
                [v2  (interp e2)])
            (Pair v1 v2))]

    [Pair-case (ePair x1 x2 eB)
               (let ([vPair  (interp ePair)])
                 (type-case E vPair
                   [Pair (v1 v2)  (interp (subst v2 x2 (subst v1 x1 eB)))]
                   [else (error "Pair-case on a non-Pair")]))]

    [Inl (e0)
         (let ([v0  (interp e0)])
           (Inl v0))]

    [Inr (e0)
         (let ([v0  (interp e0)])
           (Inr v0))]

    [Sum-case (eSum xL eL xR eR)
              (let ([vSum  (interp eSum)])
                (type-case E vSum
                  [Inl (vL)  (interp (subst vL xL eL))]
                  [Inr (vR)  (interp (subst vR xR eR))]
                  [else (error "Sum-case on a non-sum")]))]

    [Let (x e1 e2)
         (let* ([v1 (interp e1)]
                [v2 (interp (subst v1 x e2))])
           v2)]

    ;
    [Id (x)
        (error "free-variable")]

    [Anno (e A)  (interp e)]
    [At (e A)    (interp e)]
    [All (a e)   (interp e)]

    ))


(define (unparse-op op)
  (type-case Op op
    [Plusop ()      `+]
    [Minusop ()     `-]
    [Equalsop ()    `=]
    [Lessthanop ()  `<]))

(define (unparse-type t)
  (type-case Type t
    [Trat ()         `rat]
    [Tint ()         `int]
    [Tpos ()         `pos]
    [Tbool ()        `bool]
    [Tunit ()        `unit]
    [T*  (t1 t2)     `(*  ,(unparse-type t1) ,(unparse-type t2))]
    [T+  (t1 t2)     `(+  ,(unparse-type t1) ,(unparse-type t2))]
    [T-> (t1 t2)     `(-> ,(unparse-type t1) ,(unparse-type t2))]
    [Tall (a A0)     `(all ,a ,(unparse-type A0))]
    [Tvar (a)        `,a]
    [Tmu  (a A0)     `(mu ,a ,(unparse-type A0))]

    ; For bonus problem
    [Tsect (t1 t2)   `(sect ,(unparse-type t1) ,(unparse-type t2))]
    ))

; unparse : (or false E) -> sexp
;
(define (unparse e)
  (if (false? e)
      #false
      (type-case E e
        [Num (n)                   n]
        [Binop (op e1 e2)          `(,(unparse-op op) ,(unparse e1) ,(unparse e2))]
        [Id (x)                    x]
        [Anno (e A)                `(Anno ,(unparse e) ,(unparse-type A))]
        [All (a e)                 `(All ,a ,(unparse e))]
        [At (e A)                  `(At ,(unparse e) ,(unparse-type A))]
        [Let (x e1 eB)             `(Let (,x ,(unparse e1)) ,(unparse eB))]
        [Lam (x body)              `(Lam ,x ,(unparse body))]
        [App (e1 e2)               `(App ,(unparse e1) ,(unparse e2))]
        [Rec (u body)              `(Rec ,u ,(unparse body))]
        [Bfalse ()                 `Bfalse]
        [Btrue ()                  `Btrue]
        [Ite (e e1 e2)             `(Ite ,(unparse e) ,(unparse e1) ,(unparse e2))]
        [Pair (e1 e2)              `(Pair ,(unparse e1) ,(unparse e2))]
        [Pair-case (e x1 x2 body)  `(Pair-case ,(unparse e) (,x1 ,x2 => ,(unparse body)))]
        [Unit ()                   `Unit]
        [Inl (eL)                  `(Inl ,(unparse eL))]
        [Inr (eR)                  `(Inr ,(unparse eR))]
        [Sum-case (e xL eL xR eR)
                  `(Sum-case ,(unparse e)
                             (Inl ,xL => ,(unparse eL))
                             (Inr ,xR => ,(unparse eR)))]
        )))


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

#|
(test-parse '{+ 11 22} (Binop (Plusop) (Num 11) (Num 22)))

(test-parse '{Let* {}
                    {Lam botanical botanical}}
            (Let* empty (Lam 'botanical (Id 'botanical))))

(test-parse '{Let* {{abba {Lam sweden sweden}}
                     {austra {Lam canada {App abba canada}}}}
                    austra}
            (Let* (list (binding 'abba (Lam 'sweden (Id 'sweden)))
                         (binding 'austra (Lam 'canada (App (Id 'abba) (Id 'canada)))))
                   (Id 'austra)))

(test-parse '{= 5 5}            (Binop (Equalsop) (Num 5) (Num 5)))
(test-parse '{= 5 6}            (Binop (Equalsop) (Num 5) (Num 6)))
|#

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

(synth (tc/empty)
       (parse '{Anno {Let*
                      {multiply : {-> num num num} {Rec m
                                                        {Lam x {Lam y {Ite {= y 0}
                                                                           0
                                                                           {Ite {= y 1}
                                                                                x
                                                                                {+ x {App {App m x} {- y 1}}}}}}}}}
                      {fact : {-> num num} {Rec u
                                                {Lam n
                                                     {Ite {< n 2}
                                                          1
                                                          {Let c {App u {- n 1}}
                                                               {App {App multiply n} c}}}}}}
                      {App fact 5}} num}))


(synth (tc/empty)
       (parse '{Anno
                {All a {All b
                            {Lam f {Lam p
                                        {Pair-case p
                                                   {x1 x2 => {Pair {App f x1}
                                                                   {App f x2}}}}}}}}
                {all a b {-> {-> a b} {* a a} {* b b}}}}))

(synth (tc/empty)
       (parse '{Anno
                {All a {All b
                            {Lam f {Lam p
                                        {Pair-case p
                                                   {x1 x2 => {Pair {App f x1}
                                                                   x2}}}}}}}
                {all a b {-> {-> a b} {* a a} {* b b}}}}))

(define (List a)
  `{mu L {+ unit {* ,a L}}})

(define Map
  `{Anno
    {All a b
         {Rec map
              {Lam f
                   {Lam xs
                        {Sum-case xs
                                  {Inl x1 => {Inl Unit}}
                                  {Inr x2 => {Inr {Pair-case x2 {xh xt => {Pair {App f xh} {App {App map f} xt}}}}}}}}}}}
    {all a b
         {-> {-> a b} ,(List 'a) ,(List 'b)}}})

(define Nil
  `{Anno
    {All a {Inl Unit}}
    {all a ,(List 'a)}})

(define Cons
  `{Anno
    {All a
         {Lam x
              {Lam xs
                   {Inr {Pair x xs}}}}}
    {all a {-> a ,(List 'a) ,(List 'a)}}})

(define SIP
  `{Let* {ConsInt {At ,Cons int}}
         {NilInt  {At ,Nil int}}
         {List-101 {App {App ConsInt 0}
                        {App {App ConsInt -1}
                             {App {App ConsInt 1}
                                  NilInt}}}}
         {App {App {At {At ,Map int} bool}
                   {Lam x {< 0 x}}}
              List-101}})

(subtype? (tc/empty)
          (Tmu 'b (T+ (Tunit) (T* (Tpos) (Tvar 'b))))
          (Tmu 'b (T+ (Tunit) (T* (Tint) (Tvar 'b)))))

(subtype? (tc/empty)
          (Tmu 'a (T+ (Tunit) (Tvar 'a)))
          (Tmu 'b (T+ (Tunit) (Tvar 'b))))

(subtype? (tc/empty)
          (Tmu 'a (T+ (Tunit) (Tvar 'a)))
          (T+ (Tunit) (Tmu 'b (T+ (Tunit) (Tvar 'b)))))

(subtype? (tc/empty)
          (Tmu 'a (T+ (Tunit) (Tvar 'a)))
          (T+ (Tunit) (Tmu 'b (T+ (Tunit) (Tvar 'b)))))


; Once you have done Problem 2, this
;
;   (synth (tc/empty) (parse SIP))
;
; should return
;
;   (T+ (Tunit) (T* (Tbool) (Tmu 'L (T+ (Tunit) (T* (Tbool) (Tvar 'L))))))

(test (interp (parse `{Sum-case {Inl 5} {Inl x1 => 1} {Inr x2 => 2}}))
      (Num 1))

(test (check (tc/empty) (parse `{Sum-case {Anno {Inl 5} {+ int int}} {Inl x1 => 1} {Inr x2 => 2}}) (Tint))
      #t)

(test (interp (parse `{Sum-case {Inr 5} {Inl x1 => 1} {Inr x2 => 2}}))
      (Num 2))

(test
  (synth (tc/empty) (parse SIP))
  (T+ (Tunit) (T* (Tbool) (Tmu 'L (T+ (Tunit) (T* (Tbool) (Tvar 'L)))))))


