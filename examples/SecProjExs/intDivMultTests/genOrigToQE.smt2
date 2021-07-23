(declare-fun x1 () Int)
(declare-fun x2 () Int)

(assert (exists ((y Int))
  (let ((a!1 (<= (* 5 (div (* 3 y) 7)) x1)))
    (and a!1 (> (* 2 y) x2)))))
(assert (let ((a!1 (* 2 (- (* (+ x1 1) 7) 1))))
  (or (>= (* 15 x2) a!1) (>= (div (* 15 x2) 30) (div a!1 30)))))
(check-sat)