(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (
< (/ x1 4) (/ y 2)
) (
<= (+ (/ x1 3) (* (- 3) x2)) (* 3 y)
)
))
