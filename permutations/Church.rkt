#lang racket
(require rackunit)

; Church numerals (X -> X) -> (X -> X)

(define (church->number f)
  ((f add1) 0))

(define church-zero
  (λ (s) (λ (z) z)))

(define (church-add1 f)
  (λ (s) (λ (z) (s ((f s) z)))))

(define (number->church n)
  (cond
    [(zero? n) church-zero]
    [else (church-add1 (number->church (sub1 n)))]))

(check-equal? (church->number (λ (f) (λ (x) x))) 0)
(check-equal? (church->number (λ (f) (λ (x) (f (f x))))) 2)
(check-equal? (church->number (number->church 1)) 1)

; function composition is multiplication
(check-equal? (church->number (compose (number->church 2) (number->church 3))) 6)

; hence square numbers are square functions
(check-equal? (church->number (compose (number->church 3) (number->church 3))) 9)
(check-equal? (church->number (compose (number->church 4) (number->church 4))) 16)