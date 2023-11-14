#lang racket
(provide bubble-sort)

;; idempotent
(define (constT b)
  (match b
    [#t b]
    [#f (not b)]))


;; i : the index of the list
(define (one-pass1 ls i)
  (match ls
    [`(,a) (list (list a) #f null)]
    [`(,a ,b . ,ls^)
     (if (> a b)
         (match-let
             ([`(,ls* ,v ,acc) (one-pass1 (cons a ls^) (add1 i))])
           (list `(,b . ,ls*) (constT v) (cons `(,i . ,(add1 i)) acc)))
         (match-let
             ([`(,ls* ,v ,acc) (one-pass1 (cons b ls^) (add1 i))])
           (list `(,a . ,ls*) v acc)))]))

(define (one-pass ls) (one-pass1 ls 1))

#|
(one-pass '(2 1))
(one-pass '(1 2))
(one-pass '(5 4 3 2 1))
(one-pass '(1 2 3 4 5))
|#


(define (bubble-sort ls)
  (let loop ([ls ls] [ac null])
    (match (one-pass ls)
      [`(,ls* #f ,acc) (values ls* (reverse (append ac acc)))]
      [`(,ls* #t ,acc) (loop ls* (append ac acc))]))

  #;
  (match (one-pass ls)
    [`(,ls* #f ,acc) ls*]
    [`(,ls* #t ,acc) (bubble-sort ls*)]))


(bubble-sort '(10 9 7 4 2))
#;
(bubble-sort '(4 5 2 3 1))


;; does logic programming help
;; -- generate permutations <-> sorting
;; -- square <-> square root
