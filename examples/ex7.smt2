; pi = (5 * y != 4 * x)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (not(= (* 5 y) (* 4 x))))
(check-sat)