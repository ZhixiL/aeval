(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
> (* (- 4) y) (+ (+ (+ (* (- 3) x1) (/ x4 2)) (* (- 4) x3)) (* (- 5) x2))
))
