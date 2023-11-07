#lang racket
(require "FunLib.rkt")
(provide get-domain to-cycles cycle-to-func to-func)

(define (snoc elem ls)
  (match ls
    ['() (list elem)]
    [`(,a . ,d)
     `(,a . ,(snoc elem d))]))

;; remove all elements in xl from ls
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


;; translate a single cycle to function
(define (cycle-to-func c)
  (lambda (x)
    (match (memq x c)
      [#f #f]
      [`(,x) (car c)]
      [`(,a . ,d) (car d)])))


;; PermC -> ([n] -> [n])
(define (to-func cycles)
  (let ([fs (map cycle-to-func cycles)])
    (lambda (x)
      (let ([vs (map (lambda (f) (f x)) fs)])
        (foldr (lambda (x y) (or x y)) #f vs)))))





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

#|
(memq 'x '(1 x 2 3))
(memq 'x '(2 3 x))
((cycle-to-func '(1 2 3)) 3)
(foldr (lambda (x y) (or x y)) #f '(#f #f 3 #f))
((to-func '((1 2 3) (4 5) (6 7))) 5)
|#
