(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
not (= (* (- 5) y) (+ (+ (+ (/ x1 3) (/ x4 2)) (* (- 3) x3)) (* (- 4) x2)))
) (
<= (+ (* 4 x2) (* (- 3) x1)) (* (- 5) y)
)) (and (
not (= (/ y 3) (+ (+ (+ (+ (/ x1 3) (* 3 x3)) (/ x4 3)) (* (- 5) x2)) 3 ))
) (
< (+ (+ (/ x3 4) (/ x1 4)) (* (- 3) x2)) (* (- 3) y)
))
))
