(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
= (/ y 3) (+ (+ (* 3 x1) (/ x2 3)) 3 )
) (
< (+ (+ (* (- 4) x3) (/ x2 2)) (/ x1 2)) (/ y 4)
)) (and (
< (+ (* 5 x1) 2 ) (* (- 5) y)
) (
= (/ y 2) (+ (+ (* (- 3) x2) (* (- 4) x1)) 2 )
))
))
