#lang racket
(require "FunLib.rkt")
(require "RevFun.rkt")
(require "Cycles.rkt")





;; tests sqrt0 : produce one classical square root

;; tests sqrt1 : produce a 'naively non-classical' square root

(sqrt1 (to-cycles f1 (get-domain 7)))
(sqrt1 (to-cycles id (get-domain 6)))
(sqrt1 (to-cycles swap (get-domain 2)))
(sqrt1 (to-cycles ccx (get-domain 8)))

;; test sqrt2 : produce a 'refined non-classical' square root
