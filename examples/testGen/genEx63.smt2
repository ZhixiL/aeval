(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
<= (+ (* (- 4) x1) 3 ) (* (- 3) y)
) (
<= (* 4 y) (+ (+ (/ x1 2) (/ x2 2)) 2 )
)) (
= (* (- 4) y) (+ (+ (* (- 4) x1) (* (- 3) x2)) 1 )
)
))
