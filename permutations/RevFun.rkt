#lang racket
(require "FunLib.rkt")
(provide get-domain to-cycles)

(define (snoc elem ls)
  (match ls
    ['() (list elem)]
    [`(,a . ,d)
     `(,a . ,(snoc elem d))]))


(define (remvl xl ls)
  (match ls
    ['() null]
    [`(,a . ,d)
     (if (memq a xl)
         (remvl xl d)
         `(,a . ,(remvl xl d)))]))


(define (get-domain n)
  (if (zero? n)
      null
      (snoc n (get-domain (sub1 n)))))


;;
(define (get-cycle f init-x)
  (let loop ([x init-x]
             [c null])
    (let ([next-x (f x)])
      (cond
        [(eqv? next-x init-x) (snoc x c)]
        [else (let ([c* (snoc x c)])
                (loop next-x c*))]))))



;; (f : [n] -> [n]) -> List -> PermC
(define (to-cycles f domain)
  (let loop ([restl domain]
             [cycles null])
    (cond
      [(null? restl) cycles]
      [else (let* ([init-x (car restl)]
                   [c (get-cycle f init-x)]
                   [restl* (remvl c restl)]
                   [cycles* (snoc c cycles)])
              (loop restl* cycles*))])))








;; tests

#|
(remvl '(1 2 3) '(1 2 3 4 5 6 7))
(get-domain 7)
(f1 1)
(snoc 'x '(a b c))
(get-cycle f1 1)
(get-cycle f1 4)
(get-cycle f1 6)
(get-cycle f1 2)
(to-cycles f1 (get-domain 7))
(to-cycles swap (get-domain 2))
(to-cycles id (get-domain 10))
(to-cycles ccx (get-domain 8))
|#
