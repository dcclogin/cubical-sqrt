#lang racket
(provide sqrt-odd-cycle
         sqrt-even-cycle
         sqrtc0
         sqrtc1
         sqrtc2)


;; Cycle(Odd) -> List × List
(define (split-odd-cycle c) ;; (assert (odd? c))
  (let-values ([(xs ys) (split-at-right c (quotient (length c) 2))])
    (list xs ys)))

#;
(split-odd-cycle '(1 2 3 4 5 6 7))
;; => '((1 2 3 4) (5 6 7))



;; List × List -> Cycle
(define (suture-lists ll)
  (match ll
    [`((,x) ()) `(,x)]       ;; for odd
    [`((,x) (,y)) `(,x ,y)]  ;; for even
    [`((,x . ,xs^)
       (,y . ,ys^))
     (let ([c^ (suture-lists `(,xs^ ,ys^))])
       `(,x ,y ,@c^))]))

#;
(suture-lists '((1 2 3 4) (5 6 7)))
;; => '(1 5 2 6 3 7 4)
#;
(suture-lists '((■ □) (✦ ✧)))
;; => '(■ ✦ □ ✧)



;; Cycle(Odd) -> Cycle(Odd)
(define (sqrt-odd-cycle c)
  (suture-lists (split-odd-cycle c)))

#;
(sqrt-odd-cycle '(1 2 3 4 5 6 7))
;; => '(1 5 2 6 3 7 4)




;; Cycle(Even) -> Cycle(Even)
;; -- what's the cost of introducing a fresh pair-cycle?
(define (sqrt-even-cycle c)
  (letrec ([gencyc (lambda (n)
                     (if (zero? n)
                         null
                         (cons (gensym) (gencyc (sub1 n)))))]
           [c0 (gencyc (length c))])
    (suture-lists `(,c ,c0))))


(define sqrt-even-2-cycles suture-lists)

;; an even-length list whose elements' lengths are the same (even)
(define (sqrt-even-list-of-cycles lc)
  (match lc
    [`() null]
    [`(,c1 ,c2 . ,cs^)
     (let ([c0 (sqrt-even-2-cycles `(,c1 ,c2))]
           [cs (sqrt-even-list-of-cycles cs^)])
       (cons c0 cs))]))

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
;; !!! temporarily works only if all cycles in ec is of length 2 (i.e. swaps) !!!
(define (sqrtc0 p)
  (letrec ([oc (filter (lambda (c) (odd? (length c))) p)]
           [ec (filter (lambda (c) (even? (length c))) p)]
           [sqrt-oc (map sqrt-odd-cycle oc)])
    (if (odd? (length ec))
        (error 'sqrtc0 "no classical square roots for the permutation ~s" p)
        (let ([sqrt-ec (sqrt-even-list-of-cycles ec)])
          (append sqrt-oc sqrt-ec)))))


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
(define (sqrtc1 p)
  (letrec ([oc (filter (lambda (c) (odd? (length c))) p)]
           [ec (filter (lambda (c) (even? (length c))) p)]
           [sqrt-oc (map sqrt-odd-cycle oc)]
           [sqrt-ec (map sqrt-even-cycle ec)])
    (append sqrt-oc sqrt-ec)))


;; PermC -> PermC
;; get one non-classical square root
;; -- a more refined algorithm?
;; !!! temporarily works only if all cycles in ec is of length 2 !!!
(define (sqrtc2 p)
  (letrec ([oc (filter (lambda (c) (odd? (length c))) p)]
           [ec (filter (lambda (c) (even? (length c))) p)]
           [sqrt-oc (map sqrt-odd-cycle oc)])
    (if (odd? (length ec))
        (match ec
          [`(,a . ,d)
           (let* ([a* (sqrt-even-cycle a)]
                  [sqrt-d (sqrt-even-list-of-cycles d)]
                  [sqrt-ec (cons a* sqrt-d)])
             (append sqrt-oc sqrt-ec))])
        (let ([sqrt-ec (sqrt-even-list-of-cycles ec)])
          (append sqrt-oc sqrt-ec)))))



#;
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

#;
(sqrt1 '((1) (2) (3) (4) (5) (6) (7 8)))
#;
(sqrt1 '((1 2 3 4 5) (a b c d e) (x y)))
