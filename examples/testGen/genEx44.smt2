(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (
>= (* 3 y) (+ (+ (/ x1 4) (* 4 x2)) 3 )
) (
<= (+ (* (- 4) x1) 4 ) (* 4 y)
)
))
