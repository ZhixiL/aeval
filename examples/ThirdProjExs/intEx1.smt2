(assert (forall ((x1 Int) (x2 Int))
(exists ((y Int)) 
(and (>= y x1) (>= y x2) (or (= y x1) (= y x2)))
)))