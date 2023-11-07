#lang racket
(require "FunLib.rkt")
(require "RevFun.rkt")
(require "Cycles.rkt")
(require rackunit)

;; ([n] -> [n]) -> ([m] -> [m])
(define (sqrtf1 f n)
  (let* ([domain (get-domain n)]
         [cycles (sqrtc1 (to-cycles f domain))]
         [√f (to-func cycles)])
    √f))

(define (sqrtf2 f n)
  (let* ([domain (get-domain n)]
         [cycles (sqrtc2 (to-cycles f domain))]
         [√f (to-func cycles)])
    √f))

(define (sqrtf0 f n)
  (let* ([domain (get-domain n)]
         [cycles (sqrtc0 (to-cycles f domain))]
         [√f (to-func cycles)])
    √f))





;; tests sqrt0 : produce one classical square root or error
(println "-- classical --")

(check-equal?
 (sqrtc0 (to-cycles f1 (get-domain 7)))
 '((1 3 2) (4 6 5 7)))

(check-equal?
 (to-cycles (sqrtf0 f1 7)
            (get-domain 7))
 '((1 3 2) (4 6 5 7)))

(check-equal?
 (to-cycles (squaref (sqrtf0 f1 7))
            (get-domain 7))
 '((1 2 3) (4 5) (6 7)))

(check-exn
 exn:fail?
 (lambda ()
   (sqrtc0 (to-cycles swap (get-domain 2)))))

(check-exn
 exn:fail?
 (lambda ()
   (sqrtc0 (to-cycles cx (get-domain 4)))))

(check-exn
 exn:fail?
 (lambda ()
   (sqrtc0 (to-cycles ccx (get-domain 8)))))




;; tests sqrtc1 : produce a 'naively non-classical' square root
(println "-- naively non-classical --")

(check-match
 (sqrtc1 (to-cycles f1 (get-domain 7)))
 (list (list 1 3 2) (list 4 _ 5 _) (list 6 _ 7 _)))

(check-match
 (to-cycles (sqrtf1 f1 7)
            (get-domain 7))
 (list (list 1 3 2) (list 4 _ 5 _) (list 6 _ 7 _)))

(check-equal?
 (to-cycles (squaref (sqrtf1 f1 7))
            (get-domain 7))
 '((1 2 3) (4 5) (6 7)))

(check-equal?
 (sqrtc1 (to-cycles id (get-domain 6)))
 '((1) (2) (3) (4) (5) (6)))

(check-match
 (sqrtc1 (to-cycles swap (get-domain 2)))
 (list (list 1 _ 2 _)))

(check-match
 (sqrtc1 (to-cycles cx (get-domain 4)))
 (list '(1) '(2) (list 3 _ 4 _)))

(check-match
 (sqrtc1 (to-cycles ccx (get-domain 8)))
 (list '(1) '(2) '(3) '(4) '(5) '(6) (list 7 _ 8 _)))








;; test sqrt2 : produce a 'refined non-classical' square root
(println "-- refined non-classical --")

(check-equal?
 (sqrtc0 (to-cycles f1 (get-domain 7)))
 '((1 3 2) (4 6 5 7)))

(check-equal?
 (to-cycles (sqrtf0 f1 7)
            (get-domain 7))
 '((1 3 2) (4 6 5 7)))

(check-equal?
 (to-cycles (squaref (sqrtf0 f1 7))
            (get-domain 7))
 '((1 2 3) (4 5) (6 7)))

(check-match
 (sqrtc2 (to-cycles swap (get-domain 2)))
 (list (list 1 _ 2 _)))

(check-match
 (sqrtc2 (to-cycles cx (get-domain 4)))
 (list '(1) '(2) (list 3 _ 4 _)))

(check-match
 (sqrtc2 (to-cycles ccx (get-domain 8)))
 (list '(1) '(2) '(3) '(4) '(5) '(6) (list 7 _ 8 _)))
