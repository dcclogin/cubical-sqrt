#lang racket
(provide (all-defined-out))


;; domains of reversible functions on finite types are regularized to be {1,2,3,...}

(define (f1 n)
  (match n
    [1 2] [2 3] [3 1]
    [4 5] [5 4]
    [6 7] [7 6]))

(define (swap n)
  (match n
    [1 2] [2 1]))

;; domain unspecified
(define (id n) n)

(define (cx n)
  (match n
    [1 1] [2 2]
    [3 4] [4 3]))

(define (ccx n)
  (match n
    [1 1] [2 2] [3 3] [4 4] [5 5] [6 6]
    [7 8] [8 7]))


(define (compose f g)
  (lambda (x)
    (f (g x))))

(define (squaref f)
  (compose f f))
