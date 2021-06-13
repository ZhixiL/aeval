(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
>= (/ y 3) (+ (+ (+ (+ (* 4 x1) (* 3 x4)) (* 4 x3)) (* 5 x2)) 1 )
) (
= (+ (* 3 x2) (* (- 4) x1)) (* (- 5) y)
)) (
> (+ (* (- 5) x1) 1 ) (* (- 4) y)
)
))
