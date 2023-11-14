#lang racket
(require "FunLib.rkt")
(provide cycles-to-adjacent-tps tps-to-func)


;; mind the "direction" of sequential composition


;; convert a cycle to a sequence of transpositions
(define (cycle-to-tps c)
  (match c
    [`(,a) null]
    [`(,a ,b) (if (< a b)
                  (list (cons a b))
                  (list (cons b a)))]
    [`(,a ,b . ,c^)
     (let ([pr (if (< a b) (cons a b) (cons b a))])
       (cons pr (cycle-to-tps `(,b . ,c^))))]))

#;
(cycle-to-tps '(1 2)) ;; => '((1 . 2))
#;
(cycle-to-tps '(1 2 3 4)) ;; => '((1 . 2) (2 . 3) (3 . 4))
#;
(cycle-to-tps '(1 3 4 2)) ;; => '((1 . 3) (3 . 4) (2 . 4))


(define (tp-to-adjacent-tps tp)
  (match tp  ;; (assert (< a b))
    [`(,a . ,b) #:when (eqv? b (add1 a)) (list tp)]
    [`(,a . ,b)
     (let* ([tp* (cons a (add1 a))]
            [tps* (tp-to-adjacent-tps (cons (add1 a) b))]
            [tps `(,tp* ,@tps* ,tp*)])
       tps)]))

#;
(tp-to-adjacent-tps '(2 . 4)) ;; => '((2 . 3) (3 . 4) (2 . 3))
#;
(tp-to-adjacent-tps '(1 . 5)) ;; => '((1 . 2) (2 . 3) (3 . 4) (4 . 5) (3 . 4) (2 . 3) (1 . 2))


(define flatten-l1
  (lambda (ls)
    (match ls
      ['() ls]
      [`(,a . ,d) `(,@a . ,(flatten-l1 d))])))

#;
(flatten-l1 '(((1 . 5)) ((2 . 4)) ()))

(define (cycles-to-adjacent-tps cs)
  (let* ([tpsl (map cycle-to-tps cs)]
         [tps* (flatten-l1 tpsl)]
         [tps (flatten-l1 (map tp-to-adjacent-tps tps*))])
    tps))

#;
(cycles-to-adjacent-tps '((1 5) (2 4) (3)))
;; => '((1 . 2) (2 . 3) (3 . 4) (4 . 5) (3 . 4) (2 . 3) (1 . 2) (2 . 3) (3 . 4) (2 . 3))


(define (tp-to-func tp)
  (match tp
    [`(,a . ,b)
     (lambda (x)
       (cond
         [(eqv? x a) b]
         [(eqv? x b) a]
         [else x]))]))


(define (tps-to-func tps)
  (let ([fs (map tp-to-func tps)])
    (foldr compose id fs)))

#;
((tps-to-func '((1 . 3) (3 . 5))) 5) ;; => 1
#;
((tps-to-func (tp-to-adjacent-tps '(1 . 5))) 2) ;; => 1
#;
((tps-to-func (cycles-to-adjacent-tps '((1 5) (2 4) (3)))) 4) ;; => 2
#;
((tps-to-func '((1 . 2) (2 . 3) (1 . 2) (3 . 4) (2 . 3) (1 . 2) (4 . 5) (3 . 4) (2 . 3) (1 . 2))) 3)
