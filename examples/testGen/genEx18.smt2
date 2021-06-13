(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
= (* (- 5) y) (+ (+ (+ (* 5 x1) (/ x4 2)) (/ x3 4)) (* (- 5) x2))
))
