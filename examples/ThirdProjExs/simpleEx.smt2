(assert (forall ((x1 Int) (x2 Int))
    (exists ((y Int))
        (and (>= y x1) (>= y x2) (or (= y x1) (= y x2))))))

(assert (
(forall ( (x1 Int) (x2 Int))
(exists ((y Int))
and (and (
= (/ y 3) (+ (/ x1 2) 4 )
) (
not (= (+ (+ (+ (/ x1 3) (/ x2 4)) (* (- 4) x3)) 4 ) (* (- 5) y))
)) (and (
>= (* (- 5) y) (+ (/ x1 3) (/ x2 4))
) (
= (+ (* (- 4) x2) (* 4 x1)) (* 4 y)
))
))))%     