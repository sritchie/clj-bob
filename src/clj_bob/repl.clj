(ns clj-bob.repl
  "a convenience namespace for CIDER, Fireplace, Cursive etc."
  (:refer-clojure :exclude [cons if num + < atom bound? set? var?])
  (:require [clj-bob.lang :refer :all]
            [clj-bob.j-bob :refer :all]
            [clj-bob.little-prover :as book]))

;; Experiment below
;; ------------------------------------------------------------

;; ## J-Bob Appendix

(J-Bob-step (prelude) ;; stuff we know.
            '(car (cons 'ham '(cheese))) ;; thing to rewrite
            '()) ;; list of steps to do the rewrite, first to last.

(J-Bob-step (prelude)
            '(car (cons 'ham '(cheese)))
            '(
              ;; start with whole expression (empty list for focus),
              ;; rewrite using car-cons.
              (() (car-cons 'ham '(cheese)))
              ))

(J-Bob-step (prelude)
            '(equal 'flapjack (atom (cons a b)))
            '(((2) (atom-cons a b))
              (() (equal 'flapjack 'nil))))

(J-Bob-step (prelude)
            '(atom (cdr (cons (car (cons p q)) '())))
            '(((1 1 1) (car-cons p q))
              ((1) (cdr-cons p '()))
              (() (atom '()))))

;; ## Chapter 3

;; 5
(defun pair (x y)
  (cons x (cons y '())))

(defun first-of (p)
  (car p))

(defun second-of (p)
  (car (cdr p)))

;; It's a theorem! Proved with a nice chain.
(dethm first-of-pair (a b)
       (equal (first-of (pair a b)) a))

(dethm second-of-pair (a b)
       (equal (second-of (pair a b)) b))

;; steps:

(comment
  ;; claim:
  (equal (second-of (pair a b)) b)

  ;; law of defun:
  (equal (second-of (cons a (cons b '()))) b)

  ;; law of defun:
  (equal (car (cdr (cons a (cons b '())))) b)

  ;; cons/cdr:
  (equal (car (cons b '())) b)

  ;; cons/car:
  (equal b b)

  ;; equal-same:
  't

  ;; boom!
  )

(defun in-pair? (xs)
  (if (equal (first-of xs) '?)
    't
    (equal (second-of xs) '?)))

(dethm in-first-of-pair (b)
       (equal (in-pair? (pair '? b)) 't))

(comment
  ;; Proof of in-first-of-pair. Rewrite the claim using our axioms.
  ;; claim:
  (equal (in-pair? (pair '? b)) 't)

  ;; law of defun, four times:
  (equal (if (equal (car (cons '? (cons b '()))) '?)
           't
           (equal (car (cdr (cons '? (cons b '())))) '?))
         't)

  ;; cons/car and cons/cdr
  (equal (if (equal '? '?)
           't
           (equal (car (cons b '())) '?))
         't)

  ;; cons/car again
  (equal (if (equal '? '?)
           't
           (equal b '?))
         't)

  ;; equal-same
  (equal (if 't
           't
           (equal b '?))
         't)

  ;; if-true axiom:
  (equal 't 't)

  ;; equal-same:
  't)

(dethm in-second-of-pair (a)
       (equal (in-pair? (pair a '?)) 't))

(comment
  ;; Proof time!

  ;; claim
  (equal (in-pair? (pair a '?)) 't)

  ;; defun twice:
  (equal (if (equal (first-of (cons a (cons '? '()))) '?)
           't
           (equal (second-of (cons a (cons '? '()))) '?))
         't)

  ;; defun again:
  (equal (if (equal (first-of (cons a (cons '? '()))) '?)
           't
           (equal (car (cdr (cons a (cons '? '())))) '?))
         't)

  ;; cons/cdr, cons/car:
  (equal (if (equal (first-of (cons a (cons '? '()))) '?)
           't
           (equal '? '?))
         't)

  ;; equal-same:
  (equal (if (equal (first-of (cons a (cons '? '()))) '?)
           't
           't)
         't)

  ;; if-same, equal-same:
  't
  )

;; ## Chapter 4

(defun list-n? (n l)
  (if (list0? l)
    (if (equal 0 n) 't 'nil)
    (if (atom l)
      nil
      (list-n? (- n 1) (cdr l)))))

;; measure - (size b)
(defun sub (a b)
  (if (atom b)
    (if (equal '? b) a b)
    (cons (sub a (car b))
          (sub a (cdr b)))))

;; Now we need a claim that `sub` is total. We had a measure...
(comment
  (if (natp (size y))
    (if (atom b)
      't
      (if (< (size (car y)) (size y))
        (< (size (cdr y)) (size y))
        'nil))
    'nil))

;; ## Chapter 5
;;
;; Dealing here with recursive function definitions and proving
;; theorems.

(defun remb (xs)
  (if (atom xs)
    '()
    (if (equal (car xs) '?)
      (remb (cdr xs))
      (cons (car xs)
            (remb (cdr xs))))))

(defun memb? (xs)
  (if (atom xs)
    'nil
    (if (equal (car xs) '?)
      't
      (memb? (cdr xs)))))

;; First we proved

(dethm memb?-remb0 (x1)
       (equal (memb? (remb '())) 'nil))

;; is this claim a theorem? Can we prove it?
(dethm memb?-remb1 (x1)
       (equal (memb? (remb (cons x1 '())))
              'nil))

;; Remember, we just learned the insight that you want to rewrite from
;; the inside out. The first focus should be remb.

(comment
  ;;claim:
  (equal (memb? (remb (cons x1 '())))
         'nil)

  ;; use remb:
  (equal (memb? (if (atom (cons x1 '()))
                  '()
                  (if (equal (car (cons x1 '())) '?)
                    (remb (cdr (cons x1 '())))
                    (cons (car (cons x1 '()))
                          (remb (cdr (cons x1 '())))))))
         'nil)

  ;; atom/cons to kill the if question, then if-false:
  (equal (memb? (if (equal (car (cons x1 '())) '?)
                  (remb (cdr (cons x1 '())))
                  (cons (car (cons x1 '()))
                        (remb (cdr (cons x1 '()))))))
         'nil)

  ;; car/cons, cdr/cons for fun:
  (equal (memb? (if (equal x1 '?)
                  (remb '())
                  (cons x1 (remb '()))))
         'nil)

  ;; woah. Here's where they stop me. Can we use another theorem to
  ;; prove this theorem? Oh shittttt. I was going to apply remb again
  ;; internally, twice.
  ;;
  ;; we can use this theorem:
  (dethm memb?-remb0 (x1)
         (equal (memb? (remb '())) 'nil))

  ;;first we have to lift out the ifs using if-same. The goal is to
  ;;get something in the form of the inner (memb? (remb '())), so we
  ;;can use this theorem to kill those applications. so if-same:

  (equal (if (equal x1 '?)
           (memb? (if (equal x1 '?)
                    (remb '())
                    (cons x1 (remb '()))))
           (memb? (if (equal x1 '?)
                    (remb '())
                    (cons x1 (remb '())))))
         'nil)

  ;; We now know something about that question in each branch, so we
  ;; can kill the inner if statements:
  (equal (if (equal x1 '?)
           (memb? (remb '()))
           (memb? (cons x1 (remb '()))))
         'nil)

  ;; this introduces if-lifting, where we can convolute shit
  ;; around. if-same, then if-nest-A, if-nest-E. (Answer and Else are
  ;; what those fuckers stand for.) The other insight is that we want
  ;; to lift ifs OUTWARD when simplifying. Lots of little rules for
  ;; simplifying stuff. Will be cool to see how they get such a short
  ;; implementation of a solver this way.
  ;;
  ;; Now we can use our first theorem to nil out one thing:
  (equal (if (equal x1 '?)
           'nil
           (memb? (cons x1 (remb '()))))
         'nil)

  ;; then use memb? with the else statement:
  (equal (if (equal x1 '?)
           'nil
           (if (atom (cons x1 (remb '())))
             'nil
             (if (equal (car (cons x1 (remb '()))) '?)
               't
               (memb? (cdr (cons x1 (remb '())))))))
         'nil)

  ;; Little shorter. Now atom/cons and if-false:
  (equal (if (equal x1 '?)
           'nil
           (if (equal (car (cons x1 (remb '()))) '?)
             't
             (memb? (cdr (cons x1 (remb '()))))))
         'nil)

  ;; car/cons, cdr/cons:
  (equal (if (equal x1 '?)
           'nil
           (if (equal x1 '?)
             't
             (memb? (remb '()))))
         'nil)

  ;; first theorem again:
  (equal (if (equal x1 '?)
           'nil
           (if (equal x1 '?)
             't
             'nil))
         'nil)

  ;; if-nest-E:
  (equal (if (equal x1 '?)
           'nil
           'nil)
         'nil)

  ;; if-same, then equal-same:
  (equal 'nil 'nil)

  ;; QED!
  ;;
  ;; Pretty cool. Mechanical program rewrites just proves the
  ;; theorems. Pretty insane form of testing if so. The "properties"
  ;; for the functions can be fuzz tested, or you can just fucking
  ;; prove them.
  )

(dethm memb?-remb2 (x1 x2)
       (equal (memb?
               (remb
                (cons x2 (cons x1 '()))))
              'nil))
(comment
  ;; claim: memb? removes question marks from a two-element list.
  (equal (memb?
          (remb
           (cons x2 (cons x1 '()))))
         'nil)

  ;; inner first, so use remb:
  (equal (memb?
          (if (atom (cons x2 (cons x1 '())))
            '()
            (if (equal (car (cons x2 (cons x1 '()))) '?)
              (remb (cdr (cons x2 (cons x1 '()))))
              (cons (car (cons x2 (cons x1 '())))
                    (remb (cdr (cons x2 (cons x1 '()))))))))
         'nil)

  ;; then atom/cons, if-false, car/cons, cdr/cons:
  (equal (memb?
          (if (equal x2 '?)
            (remb (cons x1 '()))
            (cons x2 (remb (cons x1 '())))))
         'nil)

  ;; pull ifs out
  (equal (if (equal x2 '?)
           (memb? (remb (cons x1 '())))
           (memb? (cons x2 (remb (cons x1 '())))))
         'nil)

  ;; oh shit, now we can use our old friend memb?/remb1:
  (equal (if (equal x2 '?)
           'nil
           (memb? (cons x2 (remb (cons x1 '())))))
         'nil)

  ;; memb? again:
  (equal (if (equal x2 '?)
           'nil
           (if (atom (cons x2 (remb (cons x1 '()))))
             'nil
             (if (equal (car (cons x2 (remb (cons x1 '())))) '?)
               't
               (memb? (cdr (cons x2 (remb (cons x1 '()))))))))
         'nil)

  ;; atom/cons, car/cons, cdr/cons, if-nest-E:
  (equal (if (equal x2 '?)
           'nil
           (memb? (remb (cons x1 '()))))
         'nil)

  ;; memb?-remb1 again and we're done:
  (equal (if (equal x2 '?)
           'nil
           'nil)
         'nil)

  ;; QED.
  )

;; Chapter 5's very cool. Showing that we're building up a library of
;; proofs. Obviously we're going to be able to recursively define this
;; stuff. This is getting toward inductive proofs, where instead of
;; just showing a single list, you can show that it's true for one
;; list, and on and on. Not sure how that's going to work, but it's
;; going to be very cool!
;;
;; The list reverse/reverse proof is also cool, though "left as an
;; exercise to the reader". I guess we could deal with it by proving
;; what happens when you reverse a no element list twice, then a one
;; element list twice, and getting a feel for the pattern before
;; checking out the inductive step. You don't just leap to this shit
;; and hope that it works. Anyway, on to chapter 6!

;; ## Chapter 6 - Think It Through

(dethm memb?-remb (xs)
       (equal (memb? (remb xs)) 'nil))

(comment
  ;; The claim is that memb? will never find a question mark after
  ;; they've all been removed from remb.
  (equal (memb? (remb xs)) 'nil)

  ;; okay, so they state that THIS is the inductive claim we're trying
  ;; to prove. The original claim's nested in here.
  (if (atom xs)
    (equal (memb? (remb xs)) 'nil)
    (if (equal (memb? (remb (cdr xs))) 'nil)
      (equal (memb? (remb xs)) 'nil)
      't))

  ;; which parts of the if answer and else are identical? everything,
  ;; just xs and (cdr xs) switched.

  ;; we can begin the proof now by looking at the inductive claim.
  (if (atom xs)
    (equal (memb? (remb xs)) 'nil)
    (if (equal (memb? (remb (cdr xs))) 'nil)
      (equal (memb? (remb xs)) 'nil)
      't))

  ;; first use remb in the first if answer? (so we can kill the base case.)
  (if (atom xs)
    (equal (memb? (if (atom xs)
                    '()
                    (if (equal (car xs) '?)
                      (remb (cdr xs))
                      (cons (car xs)
                            (remb (cdr xs))))))
           'nil)
    (if (equal (memb? (remb (cdr xs))) 'nil)
      (equal (memb? (remb xs)) 'nil)
      't))

  ;; I see an if-nest-A!
  (if (atom xs)
    (equal (memb? '()) 'nil)
    (if (equal (memb? (remb (cdr xs))) 'nil)
      (equal (memb? (remb xs)) 'nil)
      't))

  ;; now the first part reduces to memb?/remb0. But we don't have
  ;; those anymore, so just do thise steps again and use memb? here.
  (if (atom xs)
    (equal (if (atom '())
             'nil
             (if (equal (car '()) '?)
               't
               (memb? (cdr '())))) 'nil)
    (if (equal (memb? (remb (cdr '()))) 'nil)
      (equal (memb? (remb xs)) 'nil)
      't))

  ;; (atom '()) is 't, so if-true, then equal-same:
  (if (atom xs)
    't
    (if (equal (memb? (remb (cdr xs))) 'nil)
      (equal (memb? (remb xs)) 'nil)
      't))

  ;; now we can either look at the cdr case, or the case for non-empty
  ;; lists. Follow the book and look at the (remb xs) case with remb:
  (if (atom xs)
    't
    (if (equal (memb? (remb (cdr xs))) 'nil)
      (equal
       (memb? (if (atom xs)
                '()
                (if (equal (car xs) '?)
                  (remb (cdr xs))
                  (cons (car xs)
                        (remb (cdr xs))))))
       'nil)
      't))

  ;; oh shit - we know by if-nest-E that (atom xs) is false in this
  ;; branch. Also pull the if-statement up twice:
  (if (atom xs)
    't
    (if (equal (memb? (remb (cdr xs))) 'nil)
      (if (equal (car xs) '?)
        (equal (memb? (remb (cdr xs))) 'nil)
        (equal (memb? (cons (car xs) (remb (cdr xs))))
               'nil))
      't))

  ;; now, look at the "inductive premise", the cdr thing. NICE! In
  ;; that if, it gives us an equality we can use.
  (if (atom xs)
    't
    (if (equal (memb? (remb (cdr xs))) 'nil)
      (if (equal (car xs) '?)
        't
        (equal (memb? (cons (car xs) (remb (cdr xs))))
               'nil))
      't))


  ;; The book notes NOT to rewrite (remb (cdr xs)), since we might be
  ;; able to use the inductive premise to rewrite that shit. So, we'll
  ;; keep that one around. Maybe we use memb?, then?
  (if (atom xs)
    't
    (if (equal (memb? (remb (cdr xs))) 'nil)
      (if (equal (car xs) '?)
        't
        (equal (if (atom (cons (car xs) (remb (cdr xs))))
                 'nil
                 (if (equal (car (cons (car xs) (remb (cdr xs)))) '?)
                   't
                   (memb? (cdr (cons (car xs) (remb (cdr xs)))))))
               'nil))
      't))

  ;; atom/cons, if-false, car/cons, cdr/cons:
  (if (atom xs)
    't
    (if (equal (memb? (remb (cdr xs))) 'nil)
      (if (equal (car xs) '?)
        't
        (equal (if (equal (car xs) '?)
                 't
                 (memb? (remb (cdr xs)))) ;; the inductive premise!
               'nil))
      't))

  ;; Now we can SEE the inductive premise again. First we can use
  ;; if-nest-E to kill the (equal (car xs) '?) deal.
  (if (atom xs)
    't
    (if (equal (memb? (remb (cdr xs))) 'nil)
      (if (equal (car xs) '?)
        't
        (equal (memb? (remb (cdr xs))) 'nil))
      't))

  ;; then again for the inductive premise:
  (if (atom xs)
    't
    (if (equal (memb? (remb (cdr xs))) 'nil)
      (if (equal (car xs) '?)
        't
        't)
      't))

  ;; boom! if-same three times:
  't

  ;; QED. that proves the original claim:
  (if (atom xs)
    (equal (memb? (remb xs)) 'nil)
    (if (equal (memb? (remb (cdr xs))) 'nil)
      (equal (memb? (remb xs)) 'nil)
      't))
  )

;; Chapter 6 introduced inductive proofs, and the form for inductive
;; proofs on lists. Prove the base case, basically. The idea is that
;; if you can get a base case down, then you can use that to prove the
;; next case up. The odd thing is that this uses explicit recursion,
;; whereas I remember the inductive proofs in dependently typed agda
;; examples to actually go the other way. Define the data structure
;; using a base case, and then a way to jump up from the base
;; case. They're the same thing, really.

;; ## Chapter 7

;; define ctx? ;; returns true if x contains'?, false otherwise.

;; measure - (size x)
(defun ctx? (x)
  (if (atom x)
    (equal x '?)
    (if (ctx? (car x))
      't
      (ctx? (cdr x)))))

;; what's the claim that ctx? is total?

(comment
  (if (natp (size x))
    (if (atom x)
      't
      (if (< (size (car x)) (size x))
        ;; weird, yeah, so I guess if the measure gets smaller, if
        ;; it's TRUE, then we don't care at all about the (cdr x)
        ;; claim.
        (if (ctx? (car x))
          't
          (< (size (cdr x)) (size x)))
        '()))
    '())

  ;; Other than my note above the measure sort of looks like the
  ;; function definition. We just have to handle all the branches, and
  ;; places where recursive calls happen.

  ;; use natp/size to kill the outer if, then size/car and size/cdr to
  ;; to change up the inner ifs:
  (if (atom x)
    't
    (if 't
      ;; weird, yeah, so I guess if the measure gets smaller, if
      ;; it's TRUE, then we don't care at all about the (cdr x)
      ;; claim.
      (if (ctx? (car x))
        't
        't)
      '()))

  ;; then if-same, if-true, if-same to prove it.
  't

  ;; This proves the totality claim. So cool!
  )

;; next - recall sub:
(defun sub (x y)
  (if (atom y)
    (if (equal '? y) x y)
    (cons (sub x (car y))
          (sub x (cdr y)))))

;; state the claim that if x and y contain '?, then so does (sub x y).
(comment
  ;; Looks like we'll have to use ctx?.
  (if (ctx? x)
    (if (ctx? y)
      (equal (ctx? (sub x y)) 't)
      't)
    't)

  ;; next question - "is it a theorem?" - it's a claim... we have to
  ;; prove it to find out if it's a theorem or not. The difference
  ;; with the previous theorems is that we recurse twice. We call ctx?
  ;; on (car x) AND (cdr x).
  ;;
  ;; Now we can try to prove our claim. Here's the inductive
  ;; claim. Remember that y is the one that's shrinking.
  (if (atom y)
    (if (ctx? x)
      (if (ctx? y)
        (equal (ctx? (sub x y)) 't)
        't)
      't)
    (if (if (ctx? x)
          (if (ctx? (car y))
            (equal (ctx? (sub x (car y))) 't)
            't)
          't)
      (if (if (ctx? x)
            (if (ctx? (cdr y))
              (equal (ctx? (sub x (cdr y))) 't)
              't)
            't)
        (if (ctx? x)
          (if (ctx? y)
            (equal (ctx? (sub x y)) 't)
            't)
          't)
        't)
      't))

  ;; now we have an inductive premise for car, AND an inductive
  ;; premise for cdr. I think we can if-lift the ctx shit out.
  (if (ctx? x)
    (if (atom y)
      (if (ctx? y)
        (equal (ctx? (sub x y)) 't)
        't)
      (if (if (ctx? (car y))
            (equal (ctx? (sub x (car y))) 't)
            't)
        (if (if (ctx? (cdr y))
              (equal (ctx? (sub x (cdr y))) 't)
              't)
          (if (ctx? y)
            (equal (ctx? (sub x y)) 't)
            't)
          't)
        't))
    't)

  ;; (insight - combine ifs. If we have a bunch of ifs that are the
  ;; same, we can use if lifting to pull them out to a level where we
  ;; can combine them all.)

  ;; next, as before, we want to handle the case where we have an atom
  ;; by using sub. Then we can use if-nest-A to kill the internal (if
  ;; (atom y),,,)
  (if (ctx? x)
    (if (atom y)
      (if (ctx? y)
        (if (equal '? y)
          (equal (ctx? x) 't)
          (equal (ctx? y) 't))
        't)
      (if (if (ctx? (car y))
            (equal (ctx? (sub x (car y))) 't)
            't)
        (if (if (ctx? (cdr y))
              (equal (ctx? (sub x (cdr y))) 't)
              't)
          (if (ctx? y)
            (equal (ctx? (sub x y)) 't)
            't)
          't)
        't))
    't)

  ;; now we hit a roadblock. I would have assumed that since we have
  ;; ctx? in the question to if, we can just assume that it equals 't
  ;; if we pass. But looks like we'll actually need another, trivial
  ;; theorem:
  (dethm ctx?-t (x)
         (if (ctx? x)
           (equal (ctx? x) 't)
           't))

  ;; Now we have to make an inductive claim here, since that recurses
  ;; internally. Recursive shit is getting TRICKY... So, we can use
  ;; that theorem if we prove it eventually. But I guess it's okay to
  ;; leave it for now. Let's use it! We can rewrite the two internal
  ;; (ctx? x) and (ctx? y), then use if-same twice to kill the
  ;; internal ifs, proving the base case.
  (if (ctx? x)
    (if (atom y)
      't
      (if (if (ctx? (car y))
            (equal (ctx? (sub x (car y))) 't)
            't)
        (if (if (ctx? (cdr y))
              (equal (ctx? (sub x (cdr y))) 't)
              't)
          (if (ctx? y)
            (equal (ctx? (sub x y)) 't)
            't)
          't)
        't))
    't)

  ;; next, look at the bottom application of sub. Then use the same
  ;; if-lifting trick a bunch of times.
  (if (ctx? x)
    (if (atom y)
      't
      (if (if (ctx? (car y))
            (equal (ctx? (sub x (car y))) 't)
            't)
        (if (if (ctx? (cdr y))
              (equal (ctx? (sub x (cdr y))) 't)
              't)
          (if (ctx? y)
            (if (atom y)
              (if (equal '? y)
                (equal (ctx? x) 't)
                (equal (ctx? y) 't))
              (equal (ctx? (cons (sub x (car y))
                                 (sub x (cdr y))))
                     't))
            't)
          't)
        't))
    't)

  ;; same as before, use ctx?/t and if-nest-E, then ctx? in the same
  ;; inner branch.
  (if (ctx? x)
    (if (atom y)
      't
      (if (if (ctx? (car y))
            (equal (ctx? (sub x (car y))) 't)
            't)
        (if (if (ctx? (cdr y))
              (equal (ctx? (sub x (cdr y))) 't)
              't)
          (if (ctx? y)
            (equal (if (atom (cons (sub x (car y))
                                   (sub x (cdr y))))
                     (equal (cons (sub x (car y))
                                  (sub x (cdr y))) '?)
                     (if (ctx? (car (cons (sub x (car y))
                                          (sub x (cdr y)))))
                       't
                       (ctx? (cdr (cons (sub x (car y))
                                        (sub x (cdr y)))))))
                   't)
            't)
          't)
        't))
    't)

  ;; shit is getting huge! (No fucking way I can do this in just a
  ;; notebook, by the way.) atom/cons, if-false, car/cons,
  ;; cdr/cons... and NOW we share some inner questions! rewrite the
  ;; bottom (ctx? y) using ctx, and kill it with if-nest-E, then
  ;; if-lift out the (ctx? (car y)):
  (if (ctx? x)
    (if (atom y)
      't
      (if (ctx? (car y))
        (if (equal (ctx? (sub x (car y))) 't)
          (if (if (ctx? (cdr y))
                (equal (ctx? (sub x (cdr y))) 't)
                't)
            (equal (if (ctx? (sub x (car y)))
                     't
                     (ctx? (sub x (cdr y))))
                   't)
            't)
          't)
        (if (if (ctx? (cdr y))
              (equal (ctx? (sub x (cdr y))) 't)
              't)
          (if (ctx? (cdr y))
            (equal (if (ctx? (sub x (car y)))
                     't
                     (ctx? (sub x (cdr y))))
                   't)
            't)
          't)))
    't)

  ;; AH! Now we have the inductive premise, that the recursion on (car
  ;; x) is true. We can hold that to be true inside that if branch,
  ;; then go ahead and if-lift (ctx? (cdr y)) back out and start to
  ;; rewrite the inner question. Once again we'll have an inductive
  ;; premise we can use, the one on (cdr x).
  't

  ;; BOOM! Except we're not quite done... since we assumed that we
  ;; could rewrite the (ctx? x) to 't. We have to prove that theorem
  ;; now. Is that a "lemma"?
  (dethm ctx?-t (x)
         (if (ctx? x)
           (equal (ctx? x) 't)
           't))

  ;; New inductive claim:
  (if (atom x)
    (if (ctx? x)
      (equal (ctx? x) 't)
      't)
    (if (if (ctx? (car x))
          (equal (ctx? (car x)) 't)
          't)
      (if (if (ctx? (cdr x))
            (equal (ctx? (cdr x)) 't)
            't)
        (if (ctx? x)
          (equal (ctx? x) 't)
          't)
        't)
      't))

  ;; as always, tackle the base case first by subbing ctx:
  (if (atom x)
    (if (equal x '?)
      (equal (equal x '?) 't)
      't)
    (if (if (ctx? (car x))
          (equal (ctx? (car x)) 't)
          't)
      (if (if (ctx? (cdr x))
            (equal (ctx? (cdr x)) 't)
            't)
        (if (ctx? x)
          (equal (ctx? x) 't)
          't)
        't)
      't))

  ;; we can do the next step because in the true branch, we KNOW that
  ;; x is '?, so that all collapses.
  (if (atom x)
    't
    (if (if (ctx? (car x))
          (equal (ctx? (car x)) 't)
          't)
      (if (if (ctx? (cdr x))
            (equal (ctx? (cdr x)) 't)
            't)
        (if (ctx? x)
          (equal (ctx? x) 't)
          't)
        't)
      't))

  ;; then tackle the bottom case again. Don't touch inductive
  ;; premises. Also use if-nest-E to kill the (atom x) questions.
  ;; yet. Then lift out the (ctx? (car x)) question a few times:
  (if (atom x)
    't
    (if (ctx? (car x))
      't
      (if (if (ctx? (cdr x))
            (equal (ctx? (cdr x)) 't)
            't)
        (if (ctx? (cdr x))
          (equal (ctx? (cdr x)) 't)
          't)
        't)))

  ;; finally lift out (ctx? (cdr x)) and BOOM!
  't
  )

;; that's it for chapter 7. Now on to chapter 8.

;; ## Chapter 8

;; measure - (size xs)
(defun set? (xs)
  (if (atom xs)
    't
    (if (member? (car xs) (cdr xs))
      'nil
      (set? (cdr xs)))))

;; This one looks trickier, because to prove it we have some induction
;; to on THREE branches.
;;

(comment
  ;; here's the claim to show that member? is total:
  (if (atom xs)
    't
    (if (equal x (car xs))
      't
      (< (size (cdr xs)) (size xs))))

  ;; and we can fucking win with the size/cdr claim. 't. BOOM.
  ;;
  ;; Next step's to prove that set? is total. OH! We can refer to
  ;;OTHER total functions inside the totality claim, and we already
  ;;proved member? to be total. That's fine. We just can't recursively
  ;;call set? again in the if question, like I tried to do when I
  ;;first wrote this claim out. BOOM, makes sense.
  ;;
  ;; Here's the claim:
  (if (atom xs)
    't
    (if (member? (car xs) (cdr xs))
      't
      (< (size (cdr xs)) (size xs))))

  ;; just like before, nobody cares about the question, since
  ;; everything reduces to 't.
  )

;; "here is the definition of atoms. Can we state and prove a claim
;; about it?
(declare add-atoms)
(defun atoms (x)
  (add-atoms x '()))

;; not if we don't know what add-atoms is. But, they give it to us
;; in the next section.
;;
;; So this builds a set, and smashes down any lists you give it.
(defun add-atoms (x ys)
  (if (atom x)
    (if (member? x ys)
      ys
      (cons x ys))
    (add-atoms (car x) (add-atoms (cdr x) ys))))

;; lemme guess. The proof is going to be that add-atoms always returns
;; a set, as checked by set?
;;
;; we now need to know whether it's total or not. Here's a guess at
;; the totality claim, stripping out the bullshit check that size
;; returns a natural number:
(comment
  (if (atom x)
    't
    (if (< (size (car x)) (size x))
      (if (< (size (cdr x)) (size x))
        't
        'nil)
      't))

  ;; I think this is busted because the recursive call actually feeds
  ;; into itself. Maybe...

  (if (atom x)
    't
    (if (< (size (cdr x)) (size x))
      (if (< (size (add-atoms (cdr x) ys))  (size x))
        (if (< (size (car x)) (size x))
          't
          'nil)
        'nil)
      ))

  ;; also totally busted. Here's a better way to think about it. take
  ;; the measure:

  (size x)

  ;; and sub in the x and y from the recursive call:
  (add-atoms (car x) (add-atoms (cdr x) ys))

  ;; one sub gives us
  (size (car x))

  ;; for the outer application. Then for the inner recursive
  ;; application...
  (size (cdr x))

  ;; then we get a little talk on conjunction. AND.
  ;;
  ;; Then, as I showed above (but a little handwavey this time), they
  ;;state that because the recursive call only happens when x isn't an
  ;;atom, this is all we have to deal with. final totality claim:
  (if (atom x)
    't
    (if (< (size (car x)) (size x))
      (< (size (cdr x)) (size x))
      'nil))

  ;; almost what I had before. Difference is that we don't have to
  ;; deal with ys at all. In fact ys does NOT decrease, so that would
  ;; fuck me up. ys is getting bigger as x gets transferred
  ;; over. That's the whole point.
  ;;
  ;; whoops. frame 29 says that this is not actually the totality
  ;; claim.
  ;;
  ;; Oh. It's because we're missing the outer bullshit.
  (if (natp (size x))
    (if (atom x)
      't
      (if (< (size (car x)) (size x))
        (< (size (cdr x)) (size x))
        'nil))
    'nil)

  ;; the totality claim always has to have that stuff, even if we're
  ;; just going to strip it away immediately for a measure like size.
  )

;; and that's chapter 8!

;; ## Chapter 9 - Changing the Rules.
;;
;; reminder of add-atoms:
(defun add-atoms (x ys)
  (if (atom x)
    (if (member? x ys)
      ys
      (cons x ys))
    (add-atoms (car x) (add-atoms (cdr x) ys))))

(dethm set?-atoms (a)
       (equal (set? (atoms a)) 't))

;; Boom. So when we calls 'atoms' on some shit, we always get a set
;; back out. because atoms is (add-atoms a '()). Helper functions for
;; the win. Let's try to prove it.

(comment
  ;; claim:
  (equal (set? (atoms a)) 't)

  ;; use atoms:
  (equal (set? (add-atoms a '())) 't)

  ;; Hmm. Then the book wants us to use star induction to prove this
  ;; claim. Remember:
  ;; (if (atom x) C (if Ccar (if Ccdr C 't) 't))
  ;;
  ;; So they want us to make a separate claim that we can prove... but
  ;; it's just the guts. Odd.

  (dethm set?-add-atoms (a)
         (equal (set? (add-atoms a '())) 't))

  ;; Here we can use star induction, since we have two recursions
  ;; internally. New claim with star induction:

  (if (atom a)
    (equal (set? (add-atoms a '())) 't)
    (if (equal (set? (add-atoms (car a) '())) 't)
      (if (equal (set? (add-atoms (cdr a) '())) 't)
        (equal (set? (add-atoms a '())) 't)
        't)
      't))

  ;; then let's use add-atoms on the bottom bullshit. (I think if we
  ;; used it on the answer of (atom a) we'd get something simpler.

  (if (atom a)
    (equal (set? (add-atoms a '())) 't)
    (if (equal (set? (add-atoms (car a) '())) 't)
      (if (equal (set? (add-atoms (cdr a) '())) 't)
        (equal (set? (add-atoms (car a) (add-atoms (cdr a) '())))
               't)
        't)
      't))

  ;; As they point out, star induction is NOT helping us, since our
  ;; inductive premise doesn't match the recursive application. So
  ;; there's no way to simplify this fucker out.

  ;; okay. According to the book start with a more general claim than
  (equal (set? (add-atoms a '())) 't)

  ;; so,
  (equal (set? (add-atoms a bs)) 't)

  ;; since according to the book we need the arguments to all be
  ;; variables. It'll still work to prove the original claim if it's
  ;; true, of course. As they point out, it's NOT true:
  (equal (set? (add-atoms a '(b b))) 't)

  ;; is false. For it to be true, bs has to be a set as well.

  (if (set? bs)
    (equal (set? (add-atoms a bs)) 't)
    't)

  ;; claim:
  (dethm set?-add-atoms (a bs)
         (if (set? bs)
           (equal (set? (add-atoms a bs)) 't)
           't))

  ;; "what must the inductive claim state?" It's going to be a new
  ;; kind of inductive claim. Here's a rat's nest...
  (if (atom a)
    (if (set? bs)
      (equal (set? (add-atoms a bs)) 't)
      't)
    (if (if (set? bs)
          (equal (set? (add-atoms (car a) bs)) 't)
          't)
      (if (if (set? bs)
            (equal (set? (add-atoms (cdr a) bs)) 't)
            't)
        (if (set? bs)
          (equal (set? (add-atoms (car a) (add-atoms (cdr a) bs))) 't)
          't)
        't)
      't))

  ;; here's the right answer:
  (if (atom a)
    (if (set? bs)
      (equal (set? (add-atoms a bs)) 't)
      't)
    (if (if (set? (add-atoms (cdr a) bs)) ;; remember this :)
          (equal (set? (add-atoms (car a) (add-atoms (cdr a) bs))) 't)
          't)
      (if (if (set? bs)
            (equal (set? (add-atoms (cdr a) bs)) 't)
            't)
        (if (set? bs)
          (equal (set? (add-atoms a bs)) 't)
          't)
        't)
      't))

  ;; So the key is to remember that we're checking induction on each
  ;; of the recursive applications from the outside in, or from the
  ;; top down. No big deal. I guess it doesn't really matter with a
  ;; conjunction like this.
  ;;
  ;; In the outer one, the first one, we replaced `bs` with (add-atoms
  ;; (cdr a) bs) and `a` with `(car a)`. Those are the arguments to
  ;; that outer recursive call. Then we checked the inner recursive
  ;; call, where a becomes `(cdr a)` and `bs` stays `bs`.
  ;;
  ;; Inside those, we finally check the actual claim again. Basically
  ;; if the claim is true for the recursive calls, then it's going to
  ;; be true for the final call. That's what we want to prove. These
  ;; are the inductive premises, and we check the conjunction of those
  ;; with the original claim on the original arguments.
  ;;
  ;; Stating the claim is the tough part for sure!
  ;;
  ;; They point out that you'll run into trouble if you have ifs
  ;; inside the arguments of a recursive function call. Get those
  ;; fuckers out first using if-lifting.
  ;;
  ;; now that we have our claim we can start getting it on. use
  ;; add-atoms internally in the first branch... then if-nest-A,
  ;; if-lifting... now we need another claim:
  (dethm set?-t (x)
         (if (set? x)
           (equal (set? x) 't)
           't))

  ;; that'll let us do a transformation to 't. Next, go to the else
  ;; branch and use set?:
  (if (atom a)
    (if (set? bs)
      (if (member? a bs)
        't
        (equal (if (atom (cons a bs))
                 't
                 (if (member? (car (cons a bs)) (cdr (cons a bs)))
                   'nil
                   (set? (cdr (cons a bs)))))
               't))
      't)
    (if (if (set? (add-atoms (cdr a) bs)) ;; remember this :)
          (equal (set? (add-atoms (car a) (add-atoms (cdr a) bs))) 't)
          't)
      (if (if (set? bs)
            (equal (set? (add-atoms (cdr a) bs)) 't)
            't)
        (if (set? bs)
          (equal (set? (add-atoms a bs)) 't)
          't)
        't)
      't))

  ;; then atom/cons, car/cons, cdr/cons, if-nest-E, set?-t, if-same:
  (if (atom a)
    't
    (if (if (set? (add-atoms (cdr a) bs)) ;; remember this :)
          (equal (set? (add-atoms (car a) (add-atoms (cdr a) bs))) 't)
          't)
      (if (if (set? bs)
            (equal (set? (add-atoms (cdr a) bs)) 't)
            't)
        (if (set? bs)
          (equal (set? (add-atoms a bs)) 't)
          't)
        't)
      't))

  ;; Boom. That's the (atom a) part of the claim. Now we just need the
  ;; recursive stuff. if-lift next:
  (if (atom a)
    't
    (if (set? bs)
      (if (if (set? (add-atoms (cdr a) bs))
            (equal (set? (add-atoms (car a) (add-atoms (cdr a) bs))) 't)
            't)
        (if (equal (set? (add-atoms (cdr a) bs)) 't)
          (equal (set? (add-atoms a bs)) 't)
          't)
        't)
      't))

  ;; Gets us some serious cred. if-lift again... I didn't realize we
  ;; can probably use set?-t here, so lift the (set? (add-atoms (cdr
  ;; a) bs)) out.
  (if (atom a)
    't
    (if (set? bs)
      (if (set? (add-atoms (cdr a) bs))
        (if (equal (set? (add-atoms (car a) (add-atoms (cdr a) bs))) 't)
          (equal (set? (add-atoms a bs)) 't)
          't)
        't)
      't))

  ;; Fuck, I oversimplified. I guess we also need to prove that
  (dethm set?-nil (xs)
         (if (set? xs)
           't
           (equal (set? xs) 'nil)))

  ;; Now we can use add-atoms inside. That's going to get us some
  ;; inductive premise shit going! Then use if-nest-E on (atom
  ;; a)... and we're done.
  't

  ;; so there's that. Two theorems left to prove. set?-nil and:
  (dethm set?-t (xs)
         (if (set? xs)
           (equal (set? xs) 't)
           't))

  ;; Let's do this guy first. set recurs on cdr, so we need an
  ;; inductive premise again. List induction this time. We know that
  ;; member? is good to go for a totality, so we don't need to worry
  ;; about those calls. Claim:
  (if (atom xs)
    (if (set? xs)
      (equal (set? xs) 't)
      't)
    (if (if (set? (cdr xs))
          (equal (set? (cdr xs)) 't)
          't)
      (if (set? xs)
        (equal (set? xs) 't)
        't)
      't))

  ;; top part goes fast using set?
  (if (atom xs)
    't
    (if (if (set? (cdr xs))
          (equal (set? (cdr xs)) 't)
          't)
      (if (set? xs)
        (equal (set? xs) 't)
        't)
      't))

  ;; rewrite bottom TWO set? applications using set?. Do the question
  ;; AND the thing inside equals. Then you can do some lifting and get
  ;; that shit done.
  't

  ;; Back to the book. (I feel like the proof for set?-nil goes the
  ;; same way.) Now it's time to prove this little fucker:
  (dethm set?-atoms (a)
         (equal (set? (atoms a)) 't))

  ;; First we use add-atoms. Claim:
  (equal (set? (add-atoms a '())) 't)

  ;; we need a premise before we can use
  (dethm set?-add-atoms (a bs)
         (if (set? bs)
           (equal (set? (add-atoms a bs)) 't)
           't))


  ;; Hmm, this is funky. Use if-true:
  (if 't
    (equal (set? (add-atoms a '())) 't)
    't)

  ;; then we can use the body of set, where xs is '(), to sub in for
  ;; "true". Because I guess if-true lets us supply any else
  ;; expression we like, because we'll never get there!
  (if 't
    't
    (if (member? (car '()) (cdr '()))
      'nil
      (set? (cdr '()))))

  ;; sub this in above, and sub (atom '()) to grab the original body
  ;; of set? back:
  (if (if (atom '())
        't
        (if (member? (car '()) (cdr '()))
          'nil
          (set? (cdr '()))))
    (equal (set? (add-atoms a '())) 't)
    't)

  ;; Then I guess we can use defun backwards?
  (if (set? '())
    (equal (set? (add-atoms a '())) 't)
    't)

  ;; Now we can use set?-add-atoms, where a is a, and bs is '(). Final
  ;; thing is set?-nil:
  (dethm set?-nil (xs)
         (if (set? xs)
           't
           (equal (set? xs) 'nil))))

;; and that's it for chapter 9. On to the final chapter!!

;; ## Chapter 10

(comment
  (rotate
   ((((french . toast) . and) . maple) . syrup))
  ;;=> (((french . toast) . and) (maple . syrup))

  ;;rotate gets
  ((french . toast) (and . (maple . syrup)))

  ;; rotate again:
  (french . (toast . (and . (maple . syrup))))

  )

;; nailed the definition. No measure, since we don't recurse at all.
(defun rotate (x)
  (cons (car (car x))
        (cons (cdr (car x))
              (cdr x))))

;; is this a theorem?
(dethm rotate-cons (x y z)
       (equal (rotate (cons (cons x y) z))
              (cons x (cons y z))))

(comment
  ;; it's a claim!
  (equal (rotate (cons (cons x y) z))
         (cons x (cons y z)))

  ;; use rotate:
  (equal (cons (car (car (cons (cons x y) z)))
               (cons (cdr (car (cons (cons x y) z)))
                     (cdr (cons (cons x y) z))))
         (cons x (cons y z)))

  ;; car/cons, cdr/cons:
  (equal (cons x (cons y z))
         (cons x (cons y z)))

  ;; equal-same:
  't

  ;; done!

  ;; this shit is WAY more powerful than just doing fuzz testing. This
  ;; function is just true.
  )

;; moving on to `align`.
(defun align (x)
  (if (atom x)
    x
    (if (atom (car x))
      (cons (car x) (align (cdr x)))
      (align (rotate x)))))

(comment
  ;; now we have recursion NOT just on cdr. hmm.
  ;;
  ;; proof of total? Can't remember how to do this! Oh. Remember, make
  ;;sure the measure's smaller. Here's the proof of totality:
  (if (atom x)
    't
    (if (atom (car x))
      (< (size (cdr x)) (size x))
      (< (size (rotate x))
         (size x))))

  ;; this is with (natp (size x)) removed, of course. Next, size/cdr...
  (if (atom x)
    't
    (if (atom (car x))
      't
      (< (size (rotate x))
         (size x))))

  ;;then we do a new thing and break the x open:
  (if (atom x)
    't
    (if (atom (car x))
      't
      (< (size (rotate (cons (car x) (cdr x))))
         (size (cons (car x) (cdr x))))))

  ;; then again internally. I think we're aiming to use the other
  ;; theorem we just proved! Reminder:
  (dethm rotate-cons (x y z)
         (equal (rotate (cons (cons x y) z))
                (cons x (cons y z))))

  ;; back to it. cons/car+cdr again:
  (if (atom x)
    't
    (if (atom (car x))
      't
      (< (size (rotate (cons (cons
                              (car (car x))
                              (cdr (car x)))
                             (cdr x))))
         (size (cons (cons (car (car x))
                           (cdr (car x)))
                     (cdr x))))))

  ;; now... x is (car (car x)), y is (cdr (car x)), z is (cdr x). So
  ;; using rotate-cons, we get that line is equal to
  (cons (car (car x))
        (cons (cdr (car x)) (cdr x)))

  ;; so back to:
  (if (atom x)
    't
    (if (atom (car x))
      't
      (< (size (cons
                (car (car x))
                (cons (cdr (car x))
                      (cdr x))))
         (size (cons
                (cons (car (car x))
                      (cdr (car x)))
                (cdr x))))))

  ;; As the book points out, it doesn't exactly look like this last
  ;; fucker is true. It looks like some rearranging just occurs (and
  ;; we know that that's what happens from the function definition.)
  ;; (so size isn't the right thing to do, unless the first deal is an
  ;; atom, in which case we do recurse properly.
  ;;
  ;; This doesn't necessarily mean that the function isn't total! It
  ;; just means that we need to pick a better measure.

  )

(defun wt (x)
  (if (atom x)
    1
    (+ (* 2 (wt (car x)))
       (wt (cdr x)))))

(comment
  ;; interesting... and the measure of THIS fucker is (size x). We
  ;; probably have to show that this is total, if we want to use it in
  ;; the totality claim.

  (if (atom x)
    't
    (if (< (size (car x)) (size x))
      (< (size (cdr x)) (size x))
      'nil))

  ;; easy. 't. Now we need to prove that align is total, using this
  ;; DIFFERENT measure.
  (if (natp (wt x))
    (if (atom x)
      't
      (if (atom (car x))
        (< (wt (cdr x)) (wt x))
        (< (wt (rotate x))
           (wt x))))
    'nil)

  ;; we need an extra little theorem:
  (dethm natp-wt (x) (equal (natp (wt x)) 't))

  ;; that lets us move on:
  (if (atom x)
    't
    (if (atom (car x))
      (< (wt (cdr x)) (wt x))
      (< (wt (rotate x))
         (wt x))))

  ;; now, as we always do, we target the actual thing, not the
  ;; inductive premise.
  (if (atom x)
    't
    (if (atom (car x))
      (< (wt (cdr x))
         (+ (wt (cdr x))
            (+ (wt (car x))
               (wt (car x)))))
      (< (wt (rotate x))
         (wt x))))

  ;; now we can sub in wt again...
  (if (atom x)
    't
    (if (atom (car x))
      (< (wt (cdr x))
         (+ (wt (cdr x))
            (+ (if (atom (car x))
                 1
                 (+ (* 2 (wt (car (car x))))
                    (wt (cdr (car x)))))
               (if (atom x)
                 1
                 (+ (* 2 (wt (car (car x))))
                    (wt (cdr (car x))))))))
      (< (wt (rotate x))
         (wt x))))

  ;; then use if-nest-A on (atom (car x)).
  (if (atom x)
    't
    (if (atom (car x))
      't
      (< (wt (rotate x))
         (wt x))))

  ;; a shorter way to do this is with an intermediate claim we think
  ;; we can prove later:

  (dethm wt-pos (x)
         (equal (< 0 (wt x)) 't))

  ;; if we FIRST had subtracted out our shit (the common (wt (cdr
  ;; x))), then used this premise, we could have skipped subbing in
  ;; the definition.
  ;;
  ;; also I forgot that we have to prove that we're going to get a
  ;; natural number out of wt to use some of these premises.

  ;; time to use rotate. Because otherwise we'll not be able to kill
  ;; that, since it's not inside wt. then use wt... then use atom/cons
  ;; to kill the statement. Then car/cons and cdr cons. then same with
  ;; the final (wt x).
  (if (atom x)
    't
    (if (atom (car x))
      't
      (< (+ (+ (wt (car (car x)))
               (wt (car (car x))))
            (+ (+ (wt (cdr (car x)))
                  (wt (cdr (car x))))
               (wt (cdr x))))
         (+ (+ (wt (car x))
               (wt (car x)))
            (wt (cdr x))))))

  ;; Using common-addends... and associate commute-+ to get the (wt
  ;; (cdr x)) out. Then us wt AGAIN twice...
  (if (atom x)
    't
    (if (atom (car x))
      't
      (< (+ (+ (wt (car (car x)))
               (wt (car (car x))))
            (+ (wt (cdr (car x)))
               (wt (cdr (car x)))))
         (+ (+ (+ (wt (car (car x)))
                  (wt (car (car x))))
               (wt (cdr (car x))))
            (+ (+ (wt (car (car x)))
                  (wt (car (car x))))
               (wt (cdr (car x))))))))

  ;; now shit's huge, BUT we can do some cancelling.
  (if (atom x)
    't
    (if (atom (car x))
      't
      (< 0 (+ (wt (car (car x)))
              (wt (car (car x)))))))

  ;; and again we have a theorem that wt is positive... I also added
  ;; in the premise about wt cdr car x being positive, because we
  ;; needed that shit above to do major replacement.
  (if (atom x)
    't
    (if (atom (car x))
      't
      (if (natp (wt (cdr (car x))))
        (< 0 (+ (wt (car (car x)))
                (wt (car (car x)))))
        't)))

  ;; we can rewrite the inner if because it's true, and so is the
  ;; positive theorem for wt:
  (if (atom x)
    't
    (if (atom (car x))
      't
      (if (< 0 (wt (car (car x))))
        (< 0 (+ (wt (car (car x)))
                (wt (car (car x)))))
        't)))

  ;; by positives-+ we're set!
  't

  ;; it's hard to be so mechanical with proofs that involve
  ;; numbers. So easy to just eyeball it and kill terms.
  )

;; final step? prove this:
(dethm align-align (x)
       (equal (align (align x))
              (align x)))

(comment
  ;; this IS likely to be true... because if something's aligned,
  ;; aligning it again shouldn't change it.

  ;; now we need an inductive version of the claim to deal with the
  ;; internal recursion. Time to use defun induction! Basically follow
  ;; the guts... just remember that we always have to check, if the
  ;; recursive condition is true, then the actual condition is still
  ;; true.
  (if (atom x)
    (equal (align (align x))
           (align x))
    (if (atom (car x))
      (if (equal (align (align (cdr x)))
                 (align (cdr x)))
        (equal (align (align x))
               (align x))
        't)
      (if (equal (align (align (rotate x)))
                 (align (rotate x)))
        (equal (align (align x))
               (align x))
        't)))

  ;; off to the fucking RACES! Start with the base case. rewrite from
  ;; the inside out. then if-nest-A, then align again. Boom. Base case
  ;; is tackled.
  (if (atom x)
    't
    (if (atom (car x))
      (if (equal (align (align (cdr x)))
                 (align (cdr x)))
        (equal (align (align x))
               (align x))
        't)
      (if (equal (align (align (rotate x)))
                 (align (rotate x)))
        (equal (align (align x))
               (align x))
        't)))

  ;; next... probably start with the align definition deep
  ;; inside. Then if-nest-A on (atom (car x))
  (if (atom x)
    't
    (if (atom (car x))
      (if (equal (align (align (cdr x)))
                 (align (cdr x)))
        (equal (align (cons (car x) (align (cdr x))))
               (cons (car x) (align (cdr x))))
        't)
      (if (equal (align (align (rotate x)))
                 (align (rotate x)))
        (equal (align (align x))
               (align x))
        't)))

  ;; next steps! align again!
  (if (atom x)
    't
    (if (atom (car x))
      (if (equal (align (align (cdr x)))
                 (align (cdr x)))
        (equal (cons (car x) (align (align (cdr x))))
               (cons (car x) (align (cdr x))))
        't)
      (if (equal (align (align (rotate x)))
                 (align (rotate x)))
        (equal (align (align x))
               (align x))
        't)))

  ;; then equal-if... to replace the inner (equal (align (align (cdr
  ;; x))) (align (cdr x))). then equal-same.
  (if (atom x)
    't
    (if (atom (car x))
      't
      (if (equal (align (align (rotate x)))
                 (align (rotate x)))
        (equal (align (align x))
               (align x))
        't)))

  ;; align again internally, then if-nest-A.
  't
  )

;; very cool.
