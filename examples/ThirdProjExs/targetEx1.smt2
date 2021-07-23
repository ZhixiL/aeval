(assert (forall ((x1 Int) (x2 Int))
  (exists ((y Int))
    (=> (and (< 0 x1) (< x1 (- x2 100)))
      (and (<= x1 (* 3 y)) (<= (* 2 y) x2))))))