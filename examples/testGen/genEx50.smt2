(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (
> (+ (+ (/ x1 4) (/ x2 2)) (* 3 x3)) (* 5 y)
) (
> (+ (/ x1 2) (/ x2 2)) (* (- 4) y)
)
))
