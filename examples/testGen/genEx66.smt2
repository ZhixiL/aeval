(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (
> (/ y 3) (+ (+ (/ x1 4) (* 5 x2)) 4 )
) (
< (* (- 4) y) (+ (+ (* 5 x1) (/ x2 2)) 3 )
)
))
