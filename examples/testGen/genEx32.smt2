(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (
>= (* (- 4) y) (+ (+ (* 5 x1) (* 5 x2)) 1 )
) (
not (= (/ y 3) (+ (+ (+ (+ (* (- 3) x3) (* (- 3) x4)) (* 4 x2)) (* (- 4) x1)) 1 ))
)
))
