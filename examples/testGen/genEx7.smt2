(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
> (/ y 4) (/ x1 4)
) (
not (= (/ y 4) (+ (+ (/ x1 2) (/ x2 3)) 4 ))
)) (and (
<= (/ y 3) (+ (+ (* 4 x3) (/ x2 2)) (* 3 x1))
) (
> (+ (+ (* 5 x2) (/ x1 4)) (/ x3 3)) (* (- 4) y)
))
))
