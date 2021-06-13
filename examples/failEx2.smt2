(declare-fun y () Int)
(declare-fun x1 () Int)

(assert (
and (
>= (* (- 5) y) (+ (* (- 3) x1) 3 )
) (
= (/ y 2) (/ x1 4)
)
))
