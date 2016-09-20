;; CPSC 311
;; Alec Thériault & Khurram Jafery
;; Tuesday tutorials: T1C and T1D

#lang plai

;; Problem 1

#|
Consider the following BNF of binary numbers:

<Binary-num> ::= ()
               | (<Binary-num> 0)
               | (<Binary-num> 1)
|#

;; Examples of binary numbers in concrete syntax
(define BN-E   '())
(define BN-0   '(() 0))          ;; equivalent to (cons BN-E  '(0))
(define BN-1   '(() 1))          ;; equivalent to (cons BN-E  '(1))
(define BN-00  '((() 0) 0))      ;; equivalent to (cons BN-0  '(0))
(define BN-01  '((() 0) 1))      ;; equivalent to (cons BN-0  '(1))
(define BN-10  '((() 1) 0))      ;; equivalent to (cons BN-1  '(0))
(define BN-11  '((() 1) 1))      ;; equivalent to (cons BN-1  '(1))
(define BN-100 '(((() 1) 0) 0))  ;; equivalent to (cons BN-10 '(0))
(define BN-101 '(((() 1) 0) 1))  ;; equivalent to (cons BN-10 '(1))

;; Abstract syntax of binary numbers
(define-type Binary-num
  [Empty-num]
  [Snoc-0 (n Binary-num?)]
  [Snoc-1 (n Binary-num?)])

;; Examples of binary numbers in abstract syntax
(define PBN-E   (Empty-num))
(define PBN-0   (Snoc-0 PBN-E))
(define PBN-1   (Snoc-1 PBN-E))
(define PBN-00  (Snoc-0 PBN-0))
(define PBN-01  (Snoc-1 PBN-0))
(define PBN-10  (Snoc-0 PBN-1))
(define PBN-11  (Snoc-1 PBN-1))
(define PBN-100 (Snoc-0 PBN-10))
(define PBN-101 (Snoc-1 PBN-10))

;; Problem 1a

;; parse-binary-num : s-expression -> Binary-num?
;; parses the provided s-expressin as a Binary-num
(define (parse-binary-num sexp)
  (cond
    [(empty? sexp) (Empty-num)]
    [(= (first (rest sexp)) 1) (Snoc-1 (parse-binary-num (first sexp)))]
    [(= (first (rest sexp)) 0) (Snoc-0 (parse-binary-num (first sexp)))]
    [else (Empty-num)]))

;; Tests for parse-binary-num
(test (parse-binary-num BN-E)   PBN-E)
(test (parse-binary-num BN-0)   PBN-0)
(test (parse-binary-num BN-1)   PBN-1)
(test (parse-binary-num BN-00)  PBN-00)
(test (parse-binary-num BN-01)  PBN-01)
(test (parse-binary-num BN-10)  PBN-10)
(test (parse-binary-num BN-11)  PBN-11)
(test (parse-binary-num BN-100) PBN-100)
(test (parse-binary-num BN-101) PBN-101)

;; Problem 1b

;; eval : Binary-num? -> number?
;; evaluates the provided binary number to a decimal number
(define (eval-binary-num bnum)
  (type-case Binary-num bnum
    [Empty-num () 0]
    [Snoc-0 (n) (arithmetic-shift (eval-binary-num n) 1)]
    [Snoc-1 (n) (+ (arithmetic-shift (eval-binary-num n) 1) 1)]))

;; Tests for eval-binary-num
(test (eval-binary-num PBN-0)   0)
(test (eval-binary-num PBN-1)   1)
(test (eval-binary-num PBN-00)  0)
(test (eval-binary-num PBN-01)  1)
(test (eval-binary-num PBN-10)  2)
(test (eval-binary-num PBN-11)  3)
(test (eval-binary-num PBN-100) 4)
(test (eval-binary-num PBN-101) 5)

;; Problem 2

#|
Consider the following BNF of binary expressions:

<Binary-exp> ::= <Binary-num>
               | {~ <Binary-exp>}
               | {+ <Binary-exp> <Binary-exp>}
|#

;; Examples of binary expressions in concrete syntax
(define BE1 '{+ (() 0) (() 1)})                 ;; equiv to (cons '+ (list BN-0 BN-1))
(define BE2 '{~ ((() 0) 1)})                    ;; equiv to (cons '~ (list BN-01))
(define BE3 '{~ ((() 0) 0)})                    ;; equiv to (cons '~ (list BN-00))
(define BE4 '{+ (() 1) {~ ((() 0) 0)}})         ;; equiv to (cons '+ (list BN-1 BE3))
(define BE5 '{+ {~ ((() 0) 1)} {~ ((() 0) 0)}}) ;; equiv to (cons '+ (list BE2 BE3))

;; Abstract syntax of binary expressions
(define-type Binary-exp
  [BNum (bn  Binary-num?)]
  [BNot (be  Binary-exp?)]
  [BAdd (be1 Binary-exp?) (be2 Binary-exp?)])

;; Examples of binary expressions in abstract syntax
(define PBE1 (BAdd (BNum PBN-0) (BNum PBN-1)))
(define PBE2 (BNot (BNum PBN-01)))
(define PBE3 (BNot (BNum PBN-00)))
(define PBE4 (BAdd (BNum PBN-1) PBE3))
(define PBE5 (BAdd PBE2 PBE3))

;; Problem 2a

;; parse-binary-exp : s-expression -> Binary-exp?
;; parses the provided s-expressin as a Binary-exp
(define (parse-binary-exp sexp)
  (cond
    [(not (symbol? (first sexp))) (BNum (parse-binary-num sexp))]
    [(symbol=? (first sexp) '+) (BAdd
                                  (parse-binary-exp (second sexp))
                                  (parse-binary-exp (third sexp)))]
    [(symbol=? (first sexp) '~) (BNot (parse-binary-exp (second sexp)))]))

;; Tests for parse-binary-exp
(test (parse-binary-exp BE1) PBE1)
(test (parse-binary-exp BE2) PBE2)
(test (parse-binary-exp BE3) PBE3)
(test (parse-binary-exp BE4) PBE4)
(test (parse-binary-exp BE5) PBE5)

;; Problem 2b

#|
Evaluation semantics for Binary-exp.

----------- Eval-bnum
  bn ⇓ bn


     be ⇓ bn
----------------- Eval-bnot
  {~ be} ⇓ ~ bn


  be1 ⇓ bn1     be2 ⇓ bn2
--------------------------- Eval-badd
  {+ be1 be2} ⇓ bn1 + bn2

Note that `~` and `+` on the right hand side of ⇓ refers to
the not operation and add operation on binary numbers respectively.
|#

;; interp: Binary-exp? ->  Binary-num?
;; interpreter for Binary-exp based on evaluation semantics
(define (interp-binary-exp be) PBN-E)

;; negate-binary-num : Binary-num? -> Binary-num?
;; produces the negation of the provided binary number
(define (negate-binary-num bn) PBN-E)

;; Tests for negate-binary-num
(test (negate-binary-num PBN-0)  PBN-1)
(test (negate-binary-num PBN-1)  PBN-0)
(test (negate-binary-num PBN-00) PBN-11)
(test (negate-binary-num PBN-01) PBN-10)
(test (negate-binary-num PBN-10) PBN-01)
(test (negate-binary-num PBN-11) PBN-00)

;; add-binary-nums : Binary-num? Binary-num? -> Binary-num?
;; produces the result of adding the provided binary numbers
(define (add-binary-nums bn1 bn2) PBN-E)

;; Tests for add-binary-nums
(test (add-binary-nums PBN-0  PBN-0)  PBN-0)
(test (add-binary-nums PBN-1  PBN-0)  PBN-1)
(test (add-binary-nums PBN-0  PBN-1)  PBN-1)
(test (add-binary-nums PBN-1  PBN-1)  PBN-10)
(test (add-binary-nums PBN-1  PBN-11) PBN-100)
(test (add-binary-nums PBN-10 PBN-10) PBN-100)

;; Tests for interp-binary-exp
(test (interp-binary-exp PBE1) PBN-1)
(test (interp-binary-exp PBE2) PBN-10)
(test (interp-binary-exp PBE3) PBN-11)
(test (interp-binary-exp PBE4) PBN-100)
(test (interp-binary-exp PBE5) PBN-101)

;; Problem 3

#|
BNF of arithmetic expressions (as presented in class):

<AE> ::= <num>
       | {+ <AE> <AE>}
       | {- <AE> <AE>}

Let's extend the `+` and `-` operations to support at least two arguments!
The EBNF would now look something like:

<AE> ::= <num>
       | {+ <AE> <AE> ...}
       | {- <AE> <AE> ...}

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

;; Abstract syntax of arithmetic expressions (as presented in class)
(define-type AE
  [Num (n number?)]
  [Add (lhs AE?) (rhs AE?)]
  [Sub (lhs AE?) (rhs AE?)])

;; TODO: Change PAE1 to correspond to AE1 in abstract syntax.
;; Similary change PAE2, PAE3, PAE4, and PAE5 as well.
(define PAE1 (Num 0))
(define PAE2 (Num 0))
(define PAE3 (Num 0))
(define PAE4 (Num 0))

;; parse-ae : s-expression -> AE?
;; parser for arithmetic expressions (as presented in class)
(define (parse-ae sexp)
  (cond
    [(number? sexp) (Num sexp)]
    [(list? sexp)
     (case (first sexp)
       [(+) (if (= (length sexp) 3)
                (Add (parse-ae (second sexp)) (parse-ae (third sexp)))
                (error "parse-ae: + needs exactly 2 arguments"))]
       [(-) (if (= (length sexp) 3)
                (Sub (parse-ae (second sexp)) (parse-ae (third sexp)))
                (error "parse-ae: - needs exactly 2 arguments"))]
       [else (error "parse-ae: I only understand + and -")])]
    [else (error "parse-ae: syntax error")]))

;; Tests for parse-ae
(test (parse-ae AE1) PAE1)
(test (parse-ae AE2) PAE2)
(test (parse-ae AE3) PAE3)
(test (parse-ae AE4) PAE4)

;; interp-ae : AE? -> number?
;; interpreter for arithmetic expressions (as presented in class)
(define (interp-ae ae)
  (type-case AE ae
    [Num (n) n]
    [Add (ae1 ae2) (+ (interp-ae ae1) (interp-ae ae2))]
    [Sub (ae1 ae2) (- (interp-ae ae1) (interp-ae ae2))]))

;; Tests for interp-ae
(test (interp-ae PAE1)  6)
(test (interp-ae PAE2) -4)
(test (interp-ae PAE3)  4)
(test (interp-ae PAE4)  1)

;; Problem 4 (Extra/Bonus)
;; Disclaimer: The following problem is quite challenging in our opinion, and uses parsing ideas
;; and techniques outside the scope of CPSC 311. Therefore, we do not consider this problem as a
;; part of this tutorial but rather as a fun exercise if you choose to attempt it. We may or may not
;; upload complete solutions for this problem.

#|
Consider the following EBNF of regular expressions:

<Regex> ::= <char>
          | {<Regex> * ...}
          | {<Regex> ... ∪ <Regex> ...}
          | {<Regex> <Regex> ...}

The `...`  are read as one or more occurrences of the preceding nonterminal (* is not a nonterminal).

Description of each alternative:
- <char> corresponds to any Racket character, for example #\a and #\1.
- {<Regex> *} corresponds to the Kleene star operation, for example consider r to be a regular
  expression then {r*} matches zero or more copies of r. The star operation binds tightly i.e.
  {r1 r2 *} is equivalent to {r1 {r2 *}}.
- {<Regex> ∪ <Regex>} corresponds to alternation, for example consider r1 and r2 to be regular
  expressions then {r1 ∪ r2} matches either r1 or r2. To avoid ambiguity, let's consider
  alternation associates to the right i.e. {r1 ∪ r2 ∪ r3} is equivalent to {r1 ∪ {r2 ∪ r3}}.
- {<Regex> <Regex>} corresponds to concatenation, for example consider r1 and r2 to be regular
  expressions then {r1 r2} matches r1 first then r2 second. To avoid ambiguity, let's consider
  concatenation associates to the right i.e. {r1 r2 r3 r4} is equivalent to {r1 {r2 {r3 r4}}}.

We also the usual order of operations i.e. the Kleene star followed by concatenation followed by
alternation. Note that we do not expect the parser to handle {r * *}, the correct concrete syntax
in this case would be {{r *} *}.

Although the concrete syntax is ambiguous and open to interpretation, this ambiguity must go away when
we move to the abstract syntax and so the parser becomes responsible for dealing with it.
|#

;; Examples of (ambiguous) regular expressions in concrete syntax
(define RE1 '{#\1 #\0 *})                 ;; equivalent to '{{#\1 {#\0 *}}
(define RE2 '{#\1 #\0 * #\1})             ;; equivalent to '{{#\1 {#\0 *} #\1}
(define RE3 '{#\1 #\0 * ∪ #\0 * #\1})     ;; equivalent to '{{#\1 {#\0 *}} ∪ {{#\0 *} #\1}}
(define RE4 '{#\1 ∪ #\0 * ∪ #\0 * ∪ #\1}) ;; equivalent to '{{#\1 ∪ {#\0 *}} ∪ {{#\0 *} ∪ #\1}}
(define RE5 '{#\1 #\0 #\1 #\0})           ;; equivalent to '{#\1 {#\0 {#\1 #\0}}}

;; Abstract syntax of regular expressions
(define-type RegEx
  [Character   (c    char?)]
  [Concatenate (re1 RegEx?) (re2 RegEx?)]
  [Alternate   (re1 RegEx?) (re2 RegEx?)]
  [Star        (re  RegEx?)])

;; Examples of (disambiguous) regular expressions in abstract syntax
(define PRE1 (Concatenate (Character #\1) (Star (Character #\0))))
(define PRE2 (Concatenate (Character #\1) (Concatenate (Star (Character #\0)) (Character #\1))))
(define PRE3 (Alternate (Concatenate (Character #\1) (Star (Character #\0)))
                        (Concatenate (Star (Character #\0)) (Character #\1))))
(define PRE4 (Alternate (Character #\1)
                        (Alternate (Star (Character #\0))
                                   (Alternate (Star (Character #\0)) (Character #\1)))))
(define PRE5 (Concatenate (Character #\1)
                          (Concatenate (Character #\0)
                                       (Concatenate (Character #\1) (Character #\0)))))

;; parse-regex : s-expression -> RegEx?
;; parses the provided s-expression as a regular expression
(define (parse-regex sexp) (Character #\0))

;; Tests for parse-regex
;; TODO: Uncomment if you are attempting the problem
#|
(test (parse-regex RE1) PRE1)
(test (parse-regex RE2) PRE2)
(test (parse-regex RE3) PRE3)
(test (parse-regex RE4) PRE4)
(test (parse-regex RE5) PRE5)
|#

;; Optional: implement the regex-match function.
;; regex-match : (listof char?) RegEx? -> boolean?
;; returns true if the provided string (list of characters) matches the given regular expression
(define (regex-match loc rex) false)
