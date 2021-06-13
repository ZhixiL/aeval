(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
<= (/ y 3) (+ (+ (* 4 x1) (/ x2 2)) (/ x3 3))
) (
>= (* 5 y) (+ (* (- 4) x1) 1 )
)) (
>= (* (- 5) y) (* (- 4) x1)
)
))
