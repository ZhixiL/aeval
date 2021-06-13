(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
> (/ y 4) (+ (+ (+ (* (- 5) x1) (/ x4 4)) (/ x3 2)) (* 4 x2))
))
