(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
< (+ (+ (* 5 x1) (* (- 3) x2)) (* 3 x3)) (* (- 5) y)
) (
< (+ (* (- 3) x1) 4 ) (* 4 y)
)) (
> (* (- 4) y) (+ (+ (/ x1 2) (* (- 5) x2)) 3 )
)
))
