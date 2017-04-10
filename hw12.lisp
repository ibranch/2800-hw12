; **************** BEGIN INITIALIZATION FOR ACL2s B MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);

#|
Pete Manolios
Fri Jan 27 09:39:00 EST 2012
----------------------------

Made changes for spring 2012.


Pete Manolios
Thu Jan 27 18:53:33 EST 2011
----------------------------

The Beginner level is the next level after Bare Bones level.

|#

; Put CCG book first in order, since it seems this results in faster loading of this mode.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "ccg/ccg" :uncertified-okp nil :dir :acl2s-modes :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "base-theory" :dir :acl2s-modes)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "custom" :dir :acl2s-modes :uncertified-okp nil :ttags :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading trace-star and evalable-ld-printing books.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "trace-star" :uncertified-okp nil :dir :acl2s-modes :ttags ((:acl2s-interaction)) :load-compiled-file nil)
(include-book "hacking/evalable-ld-printing" :uncertified-okp nil :dir :system :ttags ((:evalable-ld-printing)) :load-compiled-file nil)

;theory for beginner mode
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s beginner theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "beginner-theory" :dir :acl2s-modes :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s Beginner mode.") (value :invisible))
;Settings specific to ACL2s Beginner mode.
(acl2s-beginner-settings)

; why why why why 
(acl2::xdoc acl2s::defunc) ; almost 3 seconds

(cw "~@0Beginner mode loaded.~%~@1"
    #+acl2s-startup "${NoMoReSnIp}$~%" #-acl2s-startup ""
    #+acl2s-startup "${SnIpMeHeRe}$~%" #-acl2s-startup "")


(acl2::in-package "ACL2S B")

; ***************** END INITIALIZATION FOR ACL2s B MODE ******************* ;
;$ACL2s-SMode$;Beginner
#|

CS 2800 Homework 12 - Spring 2017

This homework is to be done in a group of 2-3 students. 

If your group does not already exist:

 * One group member will create a group in BlackBoard
 
 * Other group members then join the group
 
 Submitting:
 
 * Homework is submitted by one group member. Therefore make sure the person
   submitting actually does so. In previous terms when everyone needed
   to submit we regularly had one person forget but the other submissions
   meant the team did not get a zero. Now if you forget, your team gets 0.
   - It wouldn't be a bad idea for group members to send confirmation 
     emails to each other to reduce anxiety.

 * Submit the homework file (this file) on Blackboard.  Do not rename 
   this file.  There will be a 10 point penalty for this.

 * You must list the names of ALL group members below, using the given
   format. This way we can confirm group membership with the BB groups.
   If you fail to follow these instructions, it costs us time and
   it will cost you points, so please read carefully.


Names of ALL group members: Izaak Branch, Chris Kenyon

Note: There will be a 10 pt penalty if your names do not follow 
this format.
|#

#|
Induction, Programming, and Tail Recursion Proofs

This assignment is designed to serve as a review and prepare you
for exam 2.  Thus, although this is due after the exam, it's definitely
adventageous to practically finish this homework before the exam.  At
the very least you should look at all the questions and be confident you can
do them.

Also, since we've done 11 homeworks already, I'm pretty sure you know what
the rules are for doing proofs, programming, and showing your work. If you
are confused, follow the instructions on previous assignments.  This includes
naming conventions for tail recursive functions, testing, how we format 
equational reasoning proofs, and how we indicate substitutions.

How you approach a proof is not necessarily obvious and even your TAs and
instructors have to try a proof multiple ways. It's fine to try the wrong 
IS at first and then adjust. If you can figure out what inductive assumptions
and stopping conditions you need for a proof before starting, that's even better.
The point being: a false start to your proof doesn't imply (via MP) that you
don't understand the topic but practice reduces the number of false starts.
This assignment will hopefully give you that practice.  Thus do it on your own
and merge it with your partner's later.

|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Section A: Admissibility, Measure Functions and Induction Schemes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|
First, let's review the conditions necessary for a function to be admitted in
ACL2s (I'm paraphrasing below):
1) The function f is a new function symbol
2) The input variables are distinct variable symbols
3) The body of the function is well formed term, possibly using a recursive
call to f and mentioning no variables freely (ie only the input variables)
4) The function is terminating
5) IC=>OC is a theorem
6) The body contract holds under the assumption that the IC holds (ie there
isn't a body contract violation if the input contract is true)


OK.  Now onto the questions.

For each function fn below (f1...f5), determine if the function fn is admissible:

If fn is admissible: 
   1) provide a measure function mn that can be used to prove it terminates
   2) Write the proof obligations for fn using mn that can show it terminates.
   3) Convince yourself that the function terminates (no need for a formal proof)
   4) Write the induction scheme that fn gives rise to.

If fn is NOT admissible, 
   1) Give your justification as to why (conditions 1-6 above).
      a) If the problem is syntactic (admissibility conditions 1-3) then tell us what
         part of the function has a problem.
      b) If the issue is with conditions 4-6, then give an input that will illustrate
         the violation.
   2) Give the (invalid) induction scheme that fn gives rise to.
|#

#|
A1.
(defunc f1 (x y z)
  :input-contract (and (natp x) (natp y) (listp z))
  :output-contract (natp (f1 x y z))
  (cond ((equal x 0) (+ y (len z)))
        ((endp z)    (+ x y))
        ((<= y 1)    (+ x (f1 (- x 1) 0 (rest z))))
        (t           (f1 x (- y 2) z))))

1)
(defunc m1 (x y z)
 :input-contract (and (natp x) (natp y) (listp z))
 :output-contract (natp (m1 x y z))
 (if (or (equal x 0) (endp z))
     0
     (+ x y (len z))))
     
2)
For the first recursive call:
(implies (and (natp x) (natp y) (listp z) (<= y 1))
         (< (m1 (- x 1) y (rest z)) (m1 x y z)))
         
For the second recursive call:
(implies (and (natp x) (natp y) (listp z) (> y 1))
         (< (m1 x (- y 2) z) (m1 x y z)))
         
3)
(natp x) /\ (natp y) /\ (listp z) /\ (<= y 1) =>
  ((m1 (- x 1) y (rest z)) = (+ (- x 1) y (len (rest z))) < (+ x y z) = (m1 x y z))

(natp x) /\ (natp y) /\ (listp z) /\ (> y 1) =>
  ((m1 x (- y 2) z) = (+ x (- y 2) z) < (+ x y z) = (m1 x y z))
  
4)
1. ~IC => phi
2. IC /\ (equal x 0) => phi
3. IC /\ (not (equal x 0)) /\ (endp z) => phi
4. IC /\ (not (equal x 0)) /\ (not (endp z)) /\ (<= y 1) /\ phi|((x (- x 1) (y 0) (z (rest z))) => phi
5. IC /\ (not (equal x 0)) /\ (not (endp z)) /\ (> y 1) /\ phi|((y (- y 2))) => phi

|#

(defdata lor (listof rational))

#|
A2.
;; Remember, induction schemes rely on  converting a function to an equivalent
;; cond statement.

(defunc f2 (x y)
  :input-contract (and (lorp x)(lorp y))
  :output-contract (lorp (f2 x y))
  (if (endp x)
    y
    (if (not (endp y))
      (if (<= (first x)(first y))
        (cons (first x) (f2 (rest x) y))
        (cons (first y) (f2 x (rest y))))
      x)))

1)      
(defunc m2 (x y)
 :ic (and (lorp x) (lorp y))
 :oc (natp (m2 x y))
 (if (or (endp x) (endp y))
     0
     (+ (len x) (len y))))
     
2)
First Case:
(implies (and (lorp x) (lorp y) (<= (first x)(first y)))
         (< (m2 (rest x) y) (m2 x y)))
         
Second Case:
(implies (and (lorp x) (lorp y) (not (<= (first x)(first y))))
         (< (m2 x (rest y)) (m2 x y)))
         
3)
(lorp x) /\ (lorp y) /\ (<= (first x) (first x)) =>
  (m2 (rest x) y) = (+ (len (rest x)) (len y)) < (+ (len x) (len y)) = (m2 x y)
  
(lorp x) /\ (lorp y) /\ (not (<= (first x) (first x))) =>
  (m2 x (rest y)) = (+ (len x) (len (rest y))) < (+ (len x) (len y)) = (m2 x y)
  
4)
1. ~IC => phi
2. IC /\ (endp x) => phi
3. IC /\ (not (endp x)) /\ (endp y) => phi
4. IC /\ (not (endp x)) /\ (not (endp y)) /\ (<= (first x) (first y)) /\ phi|((x (rest x)) => phi
5. IC /\ (not (endp x)) /\ (not (endp y)) /\ (> (first x) (first y)) /\ phi|((y (rest y)) => phi

|#

;; No need to consider the admissibility of evenp.  Just f3
(defunc evenp (i)
  :input-contract (integerp i)
  :output-contract (booleanp (evenp i))
  (integerp (/ i 2)))#|ACL2s-ToDo-Line|#


#|
A3.
(defunc f3 (x)
  :input-contract (integerp x)
  :output-contract (natp (f3 x))
  (cond ((> x 5)   (+ 1 (f3 (- x 1))))
        ((< x -5)  (- 2 (f3 (+ x 1))))
        ((evenp x) x)
        (t         (+ 3 (f3 (* 3 x))))))

1)
This function is not admissible because it does not terminate.
Any value of X that fulfills (> (abs x) 5) will cause this.
All X > 5 will monotonically decrease to 5, once X = 5 the function will be called on X=15
and the cycle will repeat forever -- decrease to 5, go to 15, decrease to 5...
All X < -5 will monotonically increase to -5, once X = -5 the function will be called on X=-15
and the cycle will again repeat forever.

2)
1. ~IC => phi
2. IC /\ (> x 5) /\ phi|((x (- x 1))) => phi
3. IC /\ (< x -5) /\ phi|((x (+ x 1)) => phi
4. IC /\ (<= (abs x) 5) /\ (evenp x) => phi
5. IC /\ (<= (abs x) 5) /\ (not (evenp x)) /\ phi|((x (* x 3)) => phi


|#

(defdata lon (listof nat))

#|
A4.
(defunc f4 (x y)
  :input-contract (and (natp x)(lonp y))
  :output-contract (natp (f4 x y))
  (cond ((endp y)  0)
        ((equal x (first y))  (+ 1 (f4 (+ x 1) (rest y))))
        (t                    (f4 (+ x 1) (rest y)))))

1)
(defunc m4 (x y)
 :ic (and (natp x) (lonp y))
 :oc (natp (m4 x y))
 (len y))
 
2)
(implies (and (natp x) (lonp y))
         (< (m4 (+ x 1) (rest y)) (m4 x y)))

;; Is it necessary to say something about (endp y)? Technically the above breaks
;; if (endp y) because of a contract failure (calling (rest '()) is invalid)
         
3)
(natp x) /\ (lonp y) =>
 (m4 (+ x 1) (rest y)) = (len (rest y)) < (len y) = (m4 x y)
 
4)
1. ~IC => phi
2. IC /\ (endp y) => phi
3. IC /\ (not (endp y)) /\ phi|((x (+ x 1)) (y (rest y))) => phi

|#

#|
A5.
(defunc f5 (e l1 l2)
  :input-contract (and (listp l1)(listp l2))
  :output-contract (natp (f5 e l1 l2))
  (cond ((endp l1)  (len l2))
        ((endp l2)  (f5 e (rest l1) (cons e l2)))
        (t          (f5 e (cons e l1)(rest l2)))))

1)
This function is not admissible because it does not terminate.
E = 3
L1 = '(1 2)
L2 = '()

First pass, we are in the second cond so we evaluate and call with
E = 3
L1 = '(1)
L2 = '(3)

Second pass, we are in the third cond, so we evaluate to
E = 3
L1 = '(3 1)
L2 = '()

And this pattern with L2 having 0 elements and L1 having 2 elements,
then L2 and L1 both having 1 element, will continue in perpetuity.

2)
1. ~IC => phi
2. IC /\ (endp l1) => phi
3. IC /\ (not (endp l1)) /\ (endp l2) /\ phi|((l1 (rest l1) (l2 (cons e l2))) => phi
4. IC /\ (not (endp l1)) /\ (not (endp l2)) /\ phi|((l1 (cons e l1)) (l2 (rest l2))) => phi

|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section B: The Revenge of rem-smally
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; You probably thought that question was well behind
;; you. No such luck. Let's revisit our two mod functions
;; from the start of term and let's actually PROVE
;; that they spit out the same value.
;; Rem was renamed mod to hopefully reduce confusion with 
;; "remove" or other possible abbreviations.....and yes.  Mod
;; could be modify but we used the term mod regularly in CS 1800.
;;
;; Here is a modified solution from HW02:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; mod-similar: Nat x Nat-{0} -> Nat
;;
;; (mod-similar x y) returns the remainder of the integer division of 
;; x by y assuming that x and y are relatively the same size.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defunc mod-similar (x y)
  :input-contract (and (natp x)(posp y))
  :output-contract (natp (mod-similar x y))
  (if (< x y)
    x
    (mod-similar (- x y) y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; mod-smally: Nat x Nat-{0} -> Nat
;;
;; (mod-smally x y) returns the remainder of the integer division of 
;; x by y assuming that y is relatively small compared to x.
(defunc mod-smally (x y)
  :input-contract (and (natp x)(posp y))
  :output-contract (natp (mod-smally x y))
  (if (< x y)
    x
    (if (natp (/ x y))
      0
      (+ 1 (mod-smally (- x 1) y)))))

#| Prove that mod-smally = mod-similar.  You will likely need a lemma or two. 
The solution file uses the induction scheme mod-similar gives rise to but you are 
not forced to use this.

You can also assume the following (you can prove G1 if you want extra practice):
Given G1: (natp x) /\ (posp y) /\ (< x y) => ((mod-smally x y) = x)
Given G2: (natp x) /\ (posp y) /\ (natp z) /\ (equal (* y z)  x) =>  (natp (/ x y))
Given G3: (natp a) /\ (natp b) /\ (posp y) /\ (natp (/ a y)) /\ (natp (/ b y)) => (natp (/ (+ a b) y))
...............

|#


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section C: Swap-count
;; This question is OPTINAL.....yes ALL of section C
;; is optional.  Sections D onwards are not optional.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Consider the following functions.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; swap-all: All x All x List -> List
;; Goes through list l and replaces all occurances of element e
;; with element f.
(defunc swap-all (e f l)
  :input-contract (listp l)
  :output-contract (listp (swap-all e f l))
  (cond ((endp l)            l)
        ((equal e (first l)) (cons f (swap-all e f (rest l))))
        (t                   (cons (first l)(swap-all e f (rest l))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; count: All x List -> Nat
;; Counts the number of occurences of element e in list l.
(defunc count (e l)
  :input-contract (listp l)
  :output-contract (natp (count e l))
  (cond ((endp l)            0)
        ((equal e (first l)) (+ 1 (count e (rest l))))
        (t                   (count e (rest l)))))

;; Here is a function showing how the number of elements change with swap-all
(thm (implies (listp l)(equal (len l)(len (swap-all e f l)))))

(defthm count-swap-thm 
  (implies (and (not (equal e f))(listp l))
           (equal (+ (count f l)(count e l)) 
                  (count f (swap-all e f l)))))
#| 
 OK.  Look at the theorem above. ACL2s has proved this in under a second
 and is making you look bad.  You can't let this stand.
 Reclaim your honor and prove count-swap-thm yourself.  
 Make sure you identify the induction scheme used.
 ......................
 
 
 |#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;D.  Yes tser
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|
D1.Take the function tser (rest backwards) below which takes a 
list l and returns the list with the last element in the list removed.
|#
(defunc tser (l)
  :input-contract (and (listp l)(consp l))
  :output-contract (listp (tser l))
  (if (endp (rest l))
    nil
    (cons (first l) (tser (rest l)))))

(check= (tser '(1 2 3 4)) '(1 2 3))
(check= (tser '(1)) nil)
#|
Now prove the following conjecture:
phi_tser: (listp l) /\ (consp l) => ((rev (rest (rev l))) = (tser l))
      
Clearly identify your induction scheme and the function it is derived from.

You may need a lemma.  For the sake of your own sanity here's the lemma
I used (you will need to prove it if you use it):
L1 - (listp X)/\ (not (endp X)) /\ (listp Y) 
      => ((rest (app (rev X) Y)) = (app (rest (rev X)) Y) 

HINT: The proof for L1 DOES NOT NEED INDUCTION.  In fact you could do it
within the main function but when I saw it I assumed that the proof would
be complicated. I initially tried to prove L1 with 
induction without thinking about it and I got stuck (since I was trying
to change things to look like my inductive hypothesis).  The proof is simpler
than it may seem provided you consider the app first.
...................

|#


#|
D2. 
Write a tail recursive version of tser (described above) named tser-t with
variables x and acc (the accumulator).

NOTE 1: If you are worried about efficiency, feel free to use rev* instead
of rev since we know they are equivalent from class.

NOTE 2: For additional practice, trying the proof with 
tser* calling (rev* (tser-t x nil)).  Just don't pass this other proof in.

Here is the function tser* (do not change it).
|#

........ <Write tser-t here> ........

(defunc tser* (x)
  :input-contract (and (listp x)(consp x))
  :output-contract (listp (tser* x))
  (tser-t x nil))

#|

b) Write the generalized lemma (L_tser) describing the relationship 
between  tser-t, acc and tser.  Feel free to include your sample code calls
you used to determine the relationship (you should definitely do this even
if you don't include this in your solution)
(tser-t '(1 2 3 4) nil)   (tser '(1 2 3 4)) = '(1 2 3)
(tser-t '(2 3 4) '(1))    (tser '(2 3 4)) = ??????
..............

c) Main Proof: Assuming L_tser is valid, prove the following conjecture
phi_tser: (listp x)/\(consp x) => ((tser* x) = (tser x))
......................


d) Prove L_tser.  Make sure you clearly identify the induction scheme you
used and the function it's derived from.
..................

|#

#|
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
E Removing outliers

Given that the end of term is fast approaching, my mind drifts
to statistical analysis and figuring out how students did on an
exam or assignment.  However, for the mean (or average) grade to
be meaningful I need to ensure that grades are normally distributed
(not part of the homework) and outliers are removed.....so how do we
do that?

First, we need to calculate the mean of a list of grades, determine
what is considered an outlier (we will simplifly this by stating 
> 40% from the mean is an outlier), remote outliers, and then
re-calculate the mean. If the list is empty, the mean is 0.

Now let's make this potentially faster by converting all of these functions
to be tail recursive.  However, since we are taking the average
of these scores, the order in a list doesn't matter. Thus the tail recurive
filter call can return elements in the reverse order without impacting
the average.  
|#
(defdata lopr (range rational (0 <= _ )))

(defunc abs (r)
  :input-contract (rationalp r)
  :output-contract (loprp (abs r))
  (if (< r 0)
    (unary-- r)
    r))

(defunc sum-lr (lr)
  :input-contract (lorp lr)
  :output-contract (rationalp (sum-lr lr))
  (if (endp lr)
    0
    (+ (first lr) (sum-lr (rest lr)))))

(defunc mean (lr)
  :input-contract (lorp lr)
  :output-contract (rationalp (mean lr))
  (if (endp lr)
    0
    (/ (sum-lr lr) (len lr))))

(defunc outlierp (r m d)
  :input-contract (and (rationalp r)(rationalp m)(loprp d))
  :output-contract (booleanp (outlierp r m d))
  (> (abs (- r m)) d))

(defunc filter-out (lr m d)
  :input-contract (and (lorp lr)(rationalp m)(loprp d))
  :output-contract (lorp (filter-out lr m d))
  (cond ((endp lr) lr)
        ((outlierp (first lr) m d) (filter-out (rest lr) m d))
        (t                       (cons (first lr)(filter-out (rest lr) m d)))))

;; You can ignore the next line. It is used to admit filter-mean
(acl2::in-theory (acl2::disable abs-definition-rule))

(defunc filter-mean (lr)
  :input-contract (lorp lr)
  :output-contract (rationalp (filter-mean lr))
  (let* ((m (mean lr))
         (d (abs (* 4/10 m))))
    (mean (filter-out lr m d))))


;;1) Write filter-out-t (no need for a filter-out*), sum-lr-t 
;;  (no need for a sum-lr*), and mean*
;; Notice that non-recursive functions like mean* and mean can be shown to be
;; equal if their recursive calls are equal for the same inputs (no induction needed)

............................


(defunc filter-mean* (lr)
  :input-contract (lorp lr)
  :output-contract (rationalp (filter-mean* lr))
  (let* ((m (mean* lr))
        (d (abs (* 4/10 m))))
    (mean* (filter-out-t lr m d nil))))

#|
2) Prove that filtered-mean* = filtered-mean
Notice that this will break our proof pattern a bit since filter-out and filter-out-t
should return the values in a different order. You will need a number of lemmas for this
proof.
................

|#


#|
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
G. A Heap of Work

Consider the binary heap data definition above.

A heap is a semi-ordered tree-based data structure such that the "top" or root node of 
a heap is the smallest element in the structure.  This is considered a min heap.  A max heap 
(not discussed here) has the largest value as the root node. A binary heap is a binary tree 
such that the value of the two children of any given node must be larger than the parent's 
value.  Hence a heap may look like this.
    3
 5     6
7 8   7 9

Calling pop on this heap gives the following
    5 
 7     6
  8   7 9

Popping again gives:
    6
 7     7
  8     9
  
Inserting the value 5 results in the following structure:
    6
 7     7
5 8     9

And then a series of operations which bubble the 5 up to the appropriate point
    5
 6     7
7 8     9

For more information on heaps see: https://en.wikipedia.org/wiki/Heap_(data_structure)

We will consider the following functions:
Insert: adds a value to the heap. The position of the value within the heap will vary
depending on the implementation
emptyp: Returns a boolean whether a heap is empty or not.
Pop: Remove the root node of the heap and adjust the heap accordingly.

G1.
What other basic functions should a heap have if implemented in ACL2s? Only write functions 
that cannot be created by a series of other basic functions.  

For example, function "heap-size" which returns the number of values in the heap 
would not be acceptable because it can be written  as a series of pop operations until 
the heap is empty.

* Give at least 2 "independent functions" that cannot be defined in terms of insert, emptyp,
or pop.
* You do not need to write the functions and your answers should be relatively simple but 
you need to clearly identify what the function does (like the the functions listed above).
* Feel free to implement the functions if you want to. Your answer will be a lot more 
obvious in such a case.
......................

|#
:logic

(defdata BinHeap
  (oneof nil
         (list rational BinHeap BinHeap)))

;; These functions can be difficult to admit so we will not
;; admit them in logic mode.  Your properties in G2 also don't need
;; to be proven as theorems.
:program

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; new-node: Rational x BinHeap x BinHeap -> BinHeap
;; (newnode v c1 c2) is a helper function
;; that makes a heap node with v as the value
;; and c1 and c2 as child nodes.
(defunc new-node (v c1 c2)
  :input-contract (and (rationalp v)(BinHeapp c1)(BinHeapp c2))
  :output-contract (BinHeapp (new-node v c1 c2))
  (list v c1 c2))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; emptyp: BinHeap -> Boolean
;; (emptyp h) takse a heap h and returns
;; true if it is empty (has no values)
(defunc emptyp (h)
  :input-contract (BinHeapp h)
  :output-contract (booleanp (emptyp h))
  (equal h nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; heap-size: BinHeap -> Nat
;; (heap-size h) takes a heap h and returns
;; the number of values in it. An empty heap
;; returns 0.
(defunc heap-size (h)
  :input-contract (BinHeapp h)
  :output-contract (natp (heap-size h))
  (if (emptyp h)
    0
    (+ 1 (+ (heap-size (second h))
            (heap-size (third h))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; balance: BinHeap -> BinHeap
;; (balance par) takes a "parent" heap node par 
;; and swaps parent and child values if a child
;; node value is less than the parent's value
;; This works under the assumption that before 
;; insertion the heap is well formed. Thus at MOST 
;; one child can have a smaller value than the parent node.
(defunc balance (par)
  :input-contract (BinHeapp par)
  :output-contract (BinHeapp (balance par))
  (if (emptyp par)  
    par
    (let ((c1 (second par))
          (c2 (third par)))
      (cond ((and (not (emptyp c1))(< (first c1)(first par)))
             (new-node (first c1) 
                       (new-node (first par)(second c1)(third c1))
                       c2))
            ((and (not (emptyp c2))(< (first c2)(first par)))
             (new-node (first c2)  c1
                       (new-node (first par)(second c2)(third c2))))
            (t  par)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; insert: Rational x BinHeap -> BinHeap
;; (insert r h) inserts r at the shallowest
;; branch of the heap and then rebalances the heap
;; up to the root node to ensure the heap structure
;; maintained.
(defunc insert (r h)
  :input-contract (and (rationalp r)(BinHeapp h))
  :output-contract (BinHeapp (insert r h))
  (if (emptyp h)
    (list r nil nil)
    (let ((lDepth (heap-size (second h)))
          (rDepth (heap-size (third h))))
      (if (<= lDepth rDepth)
        (balance (new-node (first h) (insert r (second h)) (third h)))
        (balance (new-node (first h) (second h) (insert r (third h))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; pop: BinHeap -> BinHeap
;; (pop h) removes the root element of the heap 
;; (the min value in the heap),  fixes the structure
;; and then returns the revised heap.
(defunc pop (h)
  :input-contract (BinHeapp h)
  :output-contract (BinHeapp (pop h))
  (cond ((emptyp h)  h)
        ((and (emptyp (second h))(emptyp (third h))) nil)
        ((emptyp (second h)) (third h))
        ((emptyp (third h)) (second h))
        ((< (first (second h))(first (third h))) 
         (list (first (second h)) (pop (second h))(third h)))
        (t  (list (first (third h)) (second h)(pop (third h))))))

;; Valid-heapp and valid-node are not strictly needed for heap definitions but it can help
;; with your testing.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; valid-heapp: BinHeap -> Boolean
;; (valid-heapp h) checks if the value of h is less than
;; or equal to the value of any child nodes.
(defunc valid-node (h)
  :input-contract (BinHeapp h)
  :output-contract (booleanp (valid-node h))
  (cond ((emptyp h) t)
        ((and (emptyp (second h))(emptyp (third h))) t)
        ((emptyp (second h)) (<= (first h)(first (third h))))
        ((emptyp (third h))  (<= (first h)(first (second h))))
        (t (and (<= (first h)(first (second h)))
                (<= (first h)(first (third h)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; valid-heapp: All -> Boolean
;; (valid-heapp h) traverses a heap h to confirm that
;; all child node values are strictly greater than the 
;; parent node values. If h is not a heap than return nil.
(defunc valid-heapp (h)
  :input-contract t
  :output-contract (booleanp (valid-heapp h))
  (if (not (BinHeapp h))
    nil    
    (if (emptyp h)
      t
      (if (valid-node h)
        (and (valid-heapp (second h))
             (valid-heapp (third h)))
        nil))))
  
  (defconst *test-heap* (insert 6 (insert 1 (insert 4 (insert 2 nil)))))
  (check= (valid-heapp *test-heap*) t)
  (check= (valid-heapp (pop *test-heap*)) t)

;; ....................

 
#|
G2.
 Above you can see an implementation of insert, emptyp and pop. For anyone who has 
 implemented a heap before, you'll notice how inefficient this implementation is. 
 In a language like Java, an array can be used and the place to insert the next 
 value is relatively fast. This begs the question: what guarantees does any heap 
 implementation need?
 * Write at least 2 more properties of a min heap that all implementations
   MUST pass. You can include the functions you described in G1.
 * Properties should be independent. A way to show this is to change the implementation
   of the functions and observe only the one property is no longer satisfied. We did
   this for properties of stacks in the lecture.
 * Properties should be written as a ACL2s theorem definition OR as a test?. 
   -If you want to test your functions (if you implemented code for G1), you can write
   test? to test if your properties are likely correct.  
   - If you simply wrote a function description, write the theorem as a comment.
 * See Chapter 8 of the lecture notes for more information about abstract data types
   and independent properties.
   
|#

;; Here are a couple properties
(test? (implies (and (rationalp r)(BinHeapp h)(emptyp h)) 
                (emptyp (pop (insert r h)))))

.................

#| Good luck on the exam everyone. |#