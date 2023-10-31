#lang racket

;; Cycle(Odd) -> List × List
(define split-odd-cycle
  (lambda (c)  ;; (assert (odd? c))
    (letrec ([l (length c)]
             [n (/ (add1 l) 2)]
             [f (lambda (l i xs ys)
                  (match l
                    [`() `(,xs ,ys)]
                    [`(,a . ,d)
                     (if (< i n)
                         (f d (add1 i) (append xs `(,a)) ys)
                         (f d (add1 i) xs (append ys `(,a))))]))])
      (f c 0 null null))))

#;
(split-odd-cycle '(1 2 3 4 5 6 7))
;; => '((1 2 3 4) (5 6 7))



;; List × List -> Cycle
(define suture-lists
  (lambda (ll)
    (match ll
      [`((,x) ()) `(,x)]       ;; for odd
      [`((,x) (,y)) `(,x ,y)]  ;; for even
      [`((,x . ,xs^)
         (,y . ,ys^))
       (let ([c^ (suture-lists `(,xs^ ,ys^))])
         `(,x ,y ,@c^))])))

#;
(suture-lists '((1 2 3 4) (5 6 7)))
;; => '(1 5 2 6 3 7 4)
#;
(suture-lists '((■ □) (✦ ✧)))
;; => '(■ ✦ □ ✧)



;; Cycle(Odd) -> Cycle(Odd)
(define sqrt-odd-cycle
  (lambda (c)
    (suture-lists (split-odd-cycle c))))

#;
(sqrt-odd-cycle '(1 2 3 4 5 6 7))
;; => '(1 5 2 6 3 7 4)




;; Cycle(Even) -> Cycle(Even)
;; -- what's the cost of introducing a fresh pair-cycle?
(define sqrt-even-cycle
  (lambda (c)  ;; (assert (even? lc))
    (letrec ([gencyc (lambda (n)
                       (if (zero? n)
                           null
                           (cons (gensym) (gencyc (sub1 n)))))]
             [c0 (gencyc (length c))])
      (suture-lists `(,c ,c0)))))


(define sqrt-even-2-cycles suture-lists)

;; an even-length list whose elements' lengths are the same (even)
(define sqrt-even-list-of-cycles
  (lambda (lc)  ;; (assert (even? lc))
    (match lc
      [`() null]
      [`(,c1 ,c2 . ,cs^)
       (let ([c0 (sqrt-even-2-cycles `(,c1 ,c2))]
             [cs (sqrt-even-list-of-cycles cs^)])
         (cons c0 cs))])))

#;
(sqrt-even-cycle '(1 2 3 4))
;; => '(1 _ 2 _ 3 _ 4 _)

#;
(sqrt-even-list-of-cycles '((1 2) (3 4) (5 6) (7 8)))
;; => '((1 3 2 4) (5 7 6 8))
#;
(sqrt-even-list-of-cycles '((1 2 3 4) (5 6 7 8)))
;; => '((1 5 2 6 3 7 4 8))




;; A PermC is a permuataion in cycle representation like
;; '((1 3 5) (2 4) (6 7))

;; PermC -> Maybe PermC
;; get one classical square root
(define sqrt0
  (lambda (p)
    (letrec ([oc (filter (lambda (c) (odd? (length c))) p)]
             [ec (filter (lambda (c) (even? (length c))) p)]
             [sqrt-oc (map sqrt-odd-cycle oc)])
      1)))

;; we need an algorithm
;; given a list of cycles with different lengths
;; return a list of lists of cycles whose lengths are the same
;; e.g.
;; input  ((1 2) (3 4) (5 6) (a b c d) (w x y z) (■))
;; output [((1 2) (3 4) (5 6)) ((a b c d) (w x y z)) ((■))]


;; PermC -> PermC
;; get one non-classical square root
;; -- generate cycle-pair for every single even cycle
;; -- easiest for implementation
(define sqrt1
  (lambda (p)
    (letrec ([oc (filter (lambda (c) (odd? (length c))) p)]
             [ec (filter (lambda (c) (even? (length c))) p)]
             [sqrt-oc (map sqrt-odd-cycle oc)]
             [sqrt-ec (map sqrt-even-cycle ec)])
      (append sqrt-oc sqrt-ec))))


;; PermC -> PermC
;; get one non-classical square root
;; -- a more refined algorithm?
(define sqrt2
  (lambda (p)
    1))




(sqrt1 '((1 2 3) (4 5) (6) (7 8)))
;; => '((1 3 2) (6) (4 _ 5 _) (7 _ 8 _))

#;
(sqrt0 '((1 2 3) (4 5) (6) (7 8)))
;; => '((1 3 2) (6) (4 7 5 8))

#;
(sqrt0 '((1 2 3) (4 5) (6) (7 8) (a b)))
;; => ???

#;
(sqrt2 '((1 2 3) (4 5) (6) (7 8) (a b)))
;; => '((1 3 2) (6) (4 7 5 8) (a _ b _))




;;;;;;;;;;;;;;;; more examples ;;;;;;;;;;;;;;;;;;;

(sqrt1 '((1) (2) (3) (4) (5) (6) (7 8)))
(sqrt1 '((1 2 3 4 5) (a b c d e) (x y)))
