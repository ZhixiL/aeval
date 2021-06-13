(declare-fun y () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (
and (
< (/ y 3) (+ (* 4 x1) 4 )
) (
not (= (/ y 3) (+ (+ (* 3 x1) (* 3 x2)) (* 4 x3)))
)
))
