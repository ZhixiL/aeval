(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
> (+ (+ (+ (* 3 x1) (/ x4 4)) (* (- 4) x3)) (* 3 x2)) (* (- 5) y)
))
