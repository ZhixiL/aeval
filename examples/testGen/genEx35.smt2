(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
not (= (* (- 4) y) (+ (+ (+ (/ x1 3) (/ x2 4)) (* 5 x3)) 3 ))
) (
< (* 5 y) (+ (+ (+ (* 4 x3) (/ x1 2)) (* (- 3) x2)) 1 )
)) (and (
<= (+ (+ (+ (/ x1 2) (/ x3 3)) (* 3 x2)) 3 ) (* (- 5) y)
) (
<= (/ x1 4) (/ y 4)
))
))
