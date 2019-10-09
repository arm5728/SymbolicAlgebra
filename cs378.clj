; cs378.clj                Gordon S. Novak Jr.       29 Jan 19

; (load-file "/u/novak/cs378/cs378.clj")
;                    tst.xyz.core
(ns user
  (:use clojure.test )
  (:require [clojure.string :as str] ))
;            [clojure.math.numeric-tower :as math]

(def lstnum '(76 85 71 83 84 89 96 84 98 97 75 85 92 64 89 87 90 65 100))

; test whether x is a cons
(defn consb? [x] (and (seq? x) (not (empty? x))))

; test whether x is a cons
(defmacro cons? [x]
  (if (seq? x)
      (list 'consb? x)
      (list 'and (list 'seq? x) (list 'not (list 'empty? x)))))

; test whether v is a variable for pattern matching,
; i.e. v is a symbol that begins with ?, such as ?x
(defn varp [v]
  (and (symbol? v)
       (str/starts-with? (name v) "?") ) )

; look up a symbol in an association list, same as assoc in lisp.
; (assocl 'ut '((rice owl) (ut bevo) (a&m dog)))  =  (ut bevo)
(defn assocl [key lst]
  (if (empty? lst)
      nil
      (if (= (first (first lst)) key)
          (first lst)
          (assocl key (rest lst)) ) ) )

; test whether two list structures (trees) are equal
; (equal '((a b) c) '((a b) c))  =  true
(defn equal [x y]
  (if (cons? x)
      (and (cons? y)
           (equal (first x) (first y))
           (equal (rest x) (rest y)))
      (= x y) ))

; test for empty list.  Same as empty?
(defn null? [x] (or (= x nil) (= x '()) ) )

; pattern matching function
(defn matchb [pat inp bindings]
  (if (and (seq? bindings) (not (empty? bindings)))
      (if (cons? pat)
          (and (cons? inp)
               (matchb (rest pat) 
                       (rest inp)
                       (matchb (first pat)
                               (first inp) bindings)))
          (if (varp pat)
              (if (not (empty? (assocl pat bindings)))
                  (and (equal inp
                        (second (assocl pat bindings)))
                       bindings)
                  (cons (list pat
                              (if (vector? inp)
                                  (apply list inp) ; convert vector to list
                                  inp))
                        bindings))
              (and (= pat inp) bindings)))) )

; pattern matching
(defn match [pat inp]  (matchb pat inp '((t t))))

; substitute old for new in form
; (subst 'fish 'beef '(beef taco))  =  (fish taco)
(defn subst [new old form]
  (if (cons? form)
      (cons (subst new old (first form))
            (subst new old (rest form)))
      (if (= form old)
          new
          form) ) )

; substitute from an association list into form
; (sublis '((rose peach) (smell taste))
;         '(a rose by any other name would smell as sweet))
;    =  (a peach by any other name would taste as sweet)
(defn sublis [alist form]
  (if (cons? form)
      (cons (sublis alist (first form))
            (sublis alist (rest form)))
      (let [binding (assocl form alist)]
          (if binding
              (second binding)
              form) ) ) )

; make a copy of a tree structure: compare to subst and sublis
(defn copy-tree [form]
  (if (cons? form)
      (cons (copy-tree (first form))
            (copy-tree (rest form)))
      form) )

; transform an input according to a pattern-pair
; (transform '((i aint got no ?x) (i do not have any ?x))
;            '(i aint got no bananas))
;      =   (i do not have any bananas)
(defn transform [pattern-pair input]
  (let [bindings (match (first pattern-pair) input)]
    (if bindings
        (sublis bindings (second pattern-pair)) ) ))

; parts of an expression: operator, left-hand side, right-hand side
(defn op [e] (first e))
(defn lhs [e] (second e))
(defn rhs [e] (first (rest (rest e))))

; append two lists: copies the first, reuses the second
; (append '(a b c) '(d e))  =  (a b c d e)
(defn append [x y]
  (if (empty? x)
      y
      (cons (first x)
            (append (rest x) y)) ) )

; test if item is in list; returns rest of list starting with item
; (member 'dick '(tom dick harry))  =  (dick harry)
(defn member [item lst]
  (if (empty? lst)
      nil
      (if (= item (first lst))
          lst
          (member item (rest lst)) ) ) )

; intersection of two sets
; (intersection '(a b c) '(a c e))  =  (a c)     or  (c a)
(defn intersection [x y]
  (if (empty? x)
      '()
      (if (member (first x) y)
          (cons (first x)
                (intersection (rest x) y))
          (intersection (rest x) y) ) ) )

(defn trrevb [lst answer]
  (if (empty? lst)
      answer
      (trrevb (rest lst)
              (cons (first lst) answer)) ) )

; tail-recursive reverse
; (trrev '(a b c))  =  (c b a)

(defn trrev [lst] (trrevb lst '()))

(defn lengthb [lst answer]
  (if (empty? lst)         ; test for base case
      answer               ; answer for base case
      (lengthb (rest lst)  ; recursive call
               (+ answer 1)) ) )   ; update answer

; length of a list
; (length '(a b c))  =  3
(defn length [lst]
  (lengthb lst 0))         ; init extra variable

(defn square [x] (* x x))

(defn abs [x] (if (< x 0) (- x) x) )

(defn sqrt [x] (Math/sqrt x))
(defn exp [x] (Math/exp x))
(defn log [x] (Math/log x))
(defn sin [x] (Math/sin x))
(defn cos [x] (Math/cos x))
(defn tan [x] (Math/tan x))
(defn atan2 [y x] (Math/atan2 y x))

; exponent, x to the nth power
(defn expt [x n]
  (if (or (float? x) (double? x))
      (Math/pow x n)
      (if (= n 0)
          1
          (if (> n 0)
              (* x (expt x (- n 1)))
              (/ 1 (expt x (- n))) ) ) ) )

; test whether x is a cons
(defn cons? [x] (and (seq? x) (not (empty? x))))

; test whether the predicate pred is true of every item in lst
;   (every (fn [x] (> x 3)) '(4 5 6))  =  true
(defn every [pred lst]
  (if (empty? lst)
      true
      (and (pred (first lst))
           (every pred (rest lst))) ) )

; test if list x is a subset of list y
(defn subset? [x y] (every (fn [z] (member z y)) x))

; test if list se4t x equals list set y
(defn set= [x y] (and (subset? x y) (subset? y x)) )

; third thing in a list.
; (third '(a b c d))  =  c
(defn third [lst] (first (rest (rest lst))))

; cause something to be quoted, unless it is self-quoting.
; (kwote 'foo)  =  (quote foo)
; (kwote '(quote foo))  =  (quote foo)
; (kwote 3)  =  3
(defn kwote [x]
  (if (or (number? x)
          (and (cons? x)
               (= (first x) 'quote)))
      x
      (list 'quote x)))

; (mapcat fn lst) is like mapcan in Lisp.

