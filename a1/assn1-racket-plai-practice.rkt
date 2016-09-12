#lang plai
(require racket/local)

;;;; TODO: PROBLEM #1 ;;;;
;;
;; Complete the function.  This should be a simple one!

;; compute-greater-power : positive positive -> positive
;; Computes the greater of x^y and y^x (i.e., x raised to
;; the power of y and y raised to the power of x).
;;
;; Hint: look up the identifier "expt" in the helpdesk.

(define (compute-greater-power x y)
  (max (expt x y) (expt y x)))

; Trivial case
(test (compute-greater-power 1 1) 1)

; Cases where order matters.
(test (compute-greater-power 1 2) 2)
(test (compute-greater-power 2 1) 2)

; Cases where order and operation both matter.
(test (compute-greater-power 2 3) 9)
(test (compute-greater-power 3 2) 9)

; An extra case just to feel confident.
; (Note that in this case the smaller of x and y raised to the larger "wins".)
(test (compute-greater-power 4 5) 1024)





;;;; TODO: PROBLEM #2 ;;;;
;;
;; Complete the function.  You'll want to remind yourself of
;; some list functions for this one!

;; interleave : (listof any?) (listof any?) -> (listof any?)
;; Interleave the elements of list1 and list2.
;;
;; That is, return a list with the first element of list1,
;; then the first of list2, then the second of list1, then the second of list2,
;; and so on.
;;
;; If one list ends before the other, include all leftover elements of the other list.

(define (interleave list1 list2)
  (cond
    [(empty? list1) list2]
    [(empty? list2) list1]
    [else (cons (first list1) (cons (first list2) (interleave (rest list1) (rest list2))))]))

(test (interleave empty empty) empty)
(test (interleave '(1 2 3) empty) '(1 2 3))
(test (interleave empty '(1 2 3)) '(1 2 3))
(test (interleave '(1) '(2)) '(1 2))
(test (interleave '(2) '(1)) '(2 1))
(test (interleave '(1 3) '(2)) '(1 2 3))
(test (interleave '(1 3 5 7) '(2 4 6 8 9)) '(1 2 3 4 5 6 7 8 9))
(test (interleave '(1 3 5 7 8 9) '(2 4 6)) '(1 2 3 4 5 6 7 8 9))

; Not just numbers!
(test (interleave '(z y x w) '("a" 1 "and a" 2 "and a" 3))
      '(z "a" y 1 x "and a" w 2 "and a" 3))


;;;; TODO: PROBLEM #3 ;;;;
;;
;; Complete the function.  More list practice!

;; contains-sequence : (listof symbol?) (listof symbol?) -> boolean?
;; Determine whether data contains the elements from sequence in order (but not necessarily right next to each other).
(define (contains-sequence data sequence)
  (cond
    [(empty? sequence) true]
    [(empty? data) false]
    [(eq? (first data) (first sequence)) (contains-sequence (rest data) (rest sequence))]
    [else (contains-sequence (rest data) sequence)]))

;; True tests, trivial though complex
;; plus repeated symbols.
(test (contains-sequence empty empty) true)
(test (contains-sequence '(a) empty) true)
(test (contains-sequence '(a b) '(a)) true)
(test (contains-sequence '(a b) '(b)) true)
(test (contains-sequence '(a b c) '(a c)) true)
(test (contains-sequence '(a b c) '(a b)) true)
(test (contains-sequence '(a b c) '(a b c)) true)
(test (contains-sequence '(a b a) '(a a)) true)

;; False test, trivial though complex.
(test (contains-sequence empty '(a)) false)
(test (contains-sequence '(a) '(b)) false)
(test (contains-sequence '(a b) '(b a)) false)
(test (contains-sequence '(a b) '(a a)) false)


;;;; TODO: PROBLEM #4 ;;;;
;;
;; Write thorough tests for the truth-or-lie? function declared below.
;; Do NOT use check-expect; use plai's test construct instead.

(define-type BoolExpr
  [Simple-expr (value boolean?)]
  [Conj-expr (lhs BoolExpr?) (rhs BoolExpr?)]   ; conjunction (AND)
  [Disj-expr (lhs BoolExpr?) (rhs BoolExpr?)])  ; disjunction (OR)

;; truth-or-lie? : BoolExpr -> boolean?
;; Determines whether the boolean expression represented is true or false.
;;
;; Note: type-case is REALLY handy for data defined with define-type.
;; However, you can also access fields with functions like conj-expr-lhs
;; which, given a conj-expr, returns its lhs field.

(define (truth-or-lie? exp)
  (type-case BoolExpr exp
    [Simple-expr (v) v]
    [Conj-expr (lhs rhs) (and (truth-or-lie? lhs)
                              (truth-or-lie? rhs))]
    [Disj-expr (lhs rhs) (or (truth-or-lie? lhs)
                             (truth-or-lie? rhs))]))

;; Write your tests here:
(test (truth-or-lie? (Simple-expr #t)) #t)
(test (truth-or-lie? (Simple-expr #f)) #f)
(test (truth-or-lie? (Conj-expr (Simple-expr #t) (Simple-expr #t))) #t)
(test (truth-or-lie? (Conj-expr (Simple-expr #t) (Simple-expr #f))) #f)
(test (truth-or-lie? (Conj-expr (Simple-expr #f) (Simple-expr #t))) #f)
(test (truth-or-lie? (Conj-expr (Simple-expr #f) (Simple-expr #f))) #f)
(test (truth-or-lie? (Disj-expr (Simple-expr #t) (Simple-expr #t))) #t)
(test (truth-or-lie? (Disj-expr (Simple-expr #t) (Simple-expr #f))) #t)
(test (truth-or-lie? (Disj-expr (Simple-expr #f) (Simple-expr #t))) #t)
(test (truth-or-lie? (Disj-expr (Simple-expr #f) (Simple-expr #f))) #f)



;;;; TODO: PROBLEM #5 ;;;;
;;
;; Time for define-type.  This is a big one.
;; find-species works well with a HtDP-like "template" approach.
;; is-extinct? should be easy using find-species.
;; common-ancestor is fairly tricky, but let the test cases guide you!
;;
;; Complete find-species, is-extinct?, and common-ancestor.

;; The "tree of life" is the biological tree of species charting
;; the evolution of one species from another.
(define-type Tree-of-life
  [Empty-tree]
  [Species (name string?)
           (extinct? boolean?)
           (child1 Tree-of-life?)
           (child2 Tree-of-life?)])

(define human-species-ToL (Species "human" false (Empty-tree) (Empty-tree)))
(define troll-species-ToL (Species "troll" true (Empty-tree) (Empty-tree)))
(define three-species-ToL (Species "missing-link" true human-species-ToL troll-species-ToL))

;; find-species : string Tree-of-life -> (or false Tree-of-life)
;; Produces the Tree-of-life node representing the named species if it exists.
;; Otherwise, produces false.
;;
;; Precondition: the species with the given name appears AT MOST once.
(define (find-species name tree)
  ;; Use a type-case!
  (type-case Tree-of-life tree
    [Empty-tree () #f]
    [Species (sname extinct? child1 child2)
             (if (eq? name sname)
               tree
               (or (find-species name child1)
                   (find-species name child2)))]))

(test (find-species "elsa" (Empty-tree)) false)
(test (find-species "elsa" human-species-ToL) false)
(test (find-species "elsa" three-species-ToL) false)
(test (find-species "human" human-species-ToL) human-species-ToL)
(test (find-species "human" three-species-ToL) human-species-ToL)
(test (find-species "troll" three-species-ToL) troll-species-ToL)



;; is-extinct? : string Tree-of-life -> boolean
;; Determines whether the given species is recorded as extinct in the given tree.
;;
;; Precondition: the species with the given name appears exactly once in the tree.
;; Hint: use find-species!
(define (is-extinct? name tree)
  (type-case Tree-of-life (find-species name tree)
             [Species (sname extinct? child1 child2) extinct?]
             [else #t]))

(test (is-extinct? "troll" three-species-ToL) true)
(test (is-extinct? "human" three-species-ToL) false)

;; common-ancestor : string string Tree-of-life -> (or false Tree-of-life)
;; Returns the node of the closest common ancestor OR false if one or both species does not exist in the tree.
;; DOES NOT NEED TO BE EFFICIENT.
;;
;; Precondition: each named species appears AT MOST once (i.e., zero or one time).

(define (common-ancestor name1 name2 tree)
  (type-case Tree-of-life tree
             [Species (sname extinct? child1 child2)
                      (let ([left (common-ancestor name1 name2 child1)]
                            [right (common-ancestor name1 name2 child2)])
                        (cond
                          [left left]
                          [right right]
                          [(and (find-species name1 tree)
                                (find-species name2 tree)) tree]
                          [else #f]))]
             [else #f]))

; Neither appears
(test (common-ancestor "elsa" "anna" (Empty-tree)) false)
(test (common-ancestor "elsa" "anna" human-species-ToL) false)
(test (common-ancestor "elsa" "anna" three-species-ToL) false)

; Only one appears (both orders)
(test (common-ancestor "elsa" "human" human-species-ToL) false)
(test (common-ancestor "human" "elsa" human-species-ToL) false)
(test (common-ancestor "elsa" "human" three-species-ToL) false)
(test (common-ancestor "human" "elsa" three-species-ToL) false)

; One is THIS node, other in subtree.
(test (common-ancestor "missing-link" "human" three-species-ToL) three-species-ToL)
(test (common-ancestor "human" "missing-link" three-species-ToL) three-species-ToL)
(test (common-ancestor "missing-link" "troll" three-species-ToL) three-species-ToL)
(test (common-ancestor "troll" "missing-link" three-species-ToL) three-species-ToL)

; Both appear in different subtrees.
(test (common-ancestor "troll" "human" three-species-ToL) three-species-ToL)
(test (common-ancestor "human" "troll" three-species-ToL) three-species-ToL)


; Both appear in the same subtree.
(define subtree-appearances-right (Species "goo" false
                                           (Species "foo" true (Empty-tree) (Empty-tree))
                                           three-species-ToL))
(define subtree-appearances-left (Species "goo" false
                                          three-species-ToL
                                          (Species "foo" true (Empty-tree) (Empty-tree))))

(test (common-ancestor "troll" "human" subtree-appearances-right) three-species-ToL)
(test (common-ancestor "human" "troll" subtree-appearances-right) three-species-ToL)
(test (common-ancestor "troll" "human" subtree-appearances-left) three-species-ToL)
(test (common-ancestor "human" "troll" subtree-appearances-left) three-species-ToL)
(test (common-ancestor "missing-link" "human" subtree-appearances-right) three-species-ToL)
(test (common-ancestor "human" "missing-link" subtree-appearances-right) three-species-ToL)
(test (common-ancestor "missing-link" "human" subtree-appearances-left) three-species-ToL)
(test (common-ancestor "human" "missing-link" subtree-appearances-left) three-species-ToL)

; Both are ONE node.
(test (common-ancestor "troll" "troll" troll-species-ToL) troll-species-ToL)
(test (common-ancestor "troll" "troll" subtree-appearances-left) troll-species-ToL)



;;;; TODO: PROBLEM #6 ;;;;
;;
;; Consider the language of nested pair expressions described by this BNF grammar:
;;
;; <nestedPair> ::= <number>
;;                | <string>
;;                | (<nestedPair>, <nestedPair>)
;;
;; Assume that a <number> is a Racket number, and a <string> is a Racket string.
;;
;; Some examples of strings that are syntactically valid <nestedPair>s:
;;
;;   3
;;   "hello"
;;   (3,4)
;;   ((3,4), 3)
;;   ("Hello", (3,("Goodbye", 99)))
;;
;; Complete the following define-type representing the abstract syntax of nestedPairs.
;; Your define-type must have variants called Pair-number, Pair-string and Pair-pair.

(define-type NestedPair
  [Pair-number (theNumber number?)]
  ; add your variants here
  [Pair-string (thePair string?)]
  [Pair-pair (lhs NestedPair?) (rhs NestedPair?)])

; Make sure the above syntax works as expecte
(test (Pair-number 10) (Pair-number 10))
(test (Pair-string "10") (Pair-string "10"))
(test (Pair-pair (Pair-number 10) (Pair-string "10")) (Pair-pair (Pair-number 10) (Pair-string "10")))
(test (Pair-pair (Pair-string "10") (Pair-number 10)) (Pair-pair (Pair-string "10") (Pair-number 10)))
