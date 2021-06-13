(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (and (
< (* 5 y) (+ (+ (* (- 3) x1) (* (- 5) x2)) (* 3 x3))
) (
not (= (/ y 4) (+ (/ x1 2) 2 ))
)) (and (
> (/ x1 4) (/ y 4)
) (
>= (+ (/ x1 3) (* 3 x2)) (/ y 3)
))
))
