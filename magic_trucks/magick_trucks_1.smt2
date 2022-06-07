; 8 Trucks with capacity 8000 Kg have to transport different goods.
; 3 trucks have cooling facilities for the goods that need it.
; For simplicity we assume that the cooled trucks are 1, 2 and 3.


(declare-fun T (Int Int) Int)
; (Truck number, Good type) -> Amount
; Good types mapping for function T and (amount of pallets):
;	1 - Nuzzles  (4)
;   2 - Prittles (n)
;   3 - Skipples (8)
;   4 - Crottles (10)
;   5 - Dupples  (20)

(declare-fun n () Int)
; Number of prittles pallets

(assert (and
; Output of T must be >= 0
; (forall ((t Int) (g Int)) (>= 0 (T t g)))

; Transport all pallets for goods with known amount
(= 4 (+ (T 1 1) (T 2 1) (T 3 1) (T 4 1) (T 5 1) (T 6 1) (T 7 1) (T 8 1)))
(= n (+ (T 1 2) (T 2 2) (T 3 2) (T 4 2) (T 5 2) (T 6 2) (T 7 2) (T 8 2)))
(= 8 (+ (T 1 3) (T 2 3) (T 3 3) (T 4 3) (T 5 3) (T 6 3) (T 7 3) (T 8 3)))
(= 10 (+ (T 1 4) (T 2 4) (T 3 4) (T 4 4) (T 5 4) (T 6 4) (T 7 4) (T 8 4)))
(= 20 (+ (T 1 5) (T 2 5) (T 3 5) (T 4 5) (T 5 5) (T 6 5) (T 7 5) (T 8 5)))

; Weight limit for each truck
(>= 8000 (+ (* 800 (T 1 1)) (* 1100 (T 1 2)) (* 1000 (T 1 3)) (* 2500 (T 1 4)) (* 200 (T 1 5))))
(>= 8000 (+ (* 800 (T 2 1)) (* 1100 (T 2 2)) (* 1000 (T 2 3)) (* 2500 (T 2 4)) (* 200 (T 2 5))))
(>= 8000 (+ (* 800 (T 3 1)) (* 1100 (T 3 2)) (* 1000 (T 3 3)) (* 2500 (T 3 4)) (* 200 (T 3 5))))
(>= 8000 (+ (* 800 (T 4 1)) (* 1100 (T 4 2)) (* 1000 (T 4 3)) (* 2500 (T 4 4)) (* 200 (T 4 5))))
(>= 8000 (+ (* 800 (T 5 1)) (* 1100 (T 5 2)) (* 1000 (T 5 3)) (* 2500 (T 5 4)) (* 200 (T 5 5))))
(>= 8000 (+ (* 800 (T 6 1)) (* 1100 (T 6 2)) (* 1000 (T 6 3)) (* 2500 (T 6 4)) (* 200 (T 6 5))))
(>= 8000 (+ (* 800 (T 7 1)) (* 1100 (T 7 2)) (* 1000 (T 7 3)) (* 2500 (T 7 4)) (* 200 (T 7 5))))
(>= 8000 (+ (* 800 (T 8 1)) (* 1100 (T 8 2)) (* 1000 (T 8 3)) (* 2500 (T 8 4)) (* 200 (T 8 5))))

; Number of pallets is greater than or equal to 0
(<= 0 (T 1 1)) (<= 0 (T 2 1)) (<= 0 (T 3 1)) (<= 0 (T 4 1))
(<= 0 (T 5 1)) (<= 0 (T 6 1)) (<= 0 (T 7 1)) (<= 0 (T 8 1))

(<= 0 (T 1 2)) (<= 0 (T 2 2)) (<= 0 (T 3 2)) (<= 0 (T 4 2))
(<= 0 (T 5 2)) (<= 0 (T 6 2)) (<= 0 (T 7 2)) (<= 0 (T 8 2))

(<= 0 (T 1 3)) (<= 0 (T 2 3)) (<= 0 (T 3 3)) (<= 0 (T 4 3))
(<= 0 (T 5 3)) (<= 0 (T 6 3)) (<= 0 (T 7 3)) (<= 0 (T 8 3))

(<= 0 (T 1 4)) (<= 0 (T 2 4)) (<= 0 (T 3 4)) (<= 0 (T 4 4))
(<= 0 (T 5 4)) (<= 0 (T 6 4)) (<= 0 (T 7 4)) (<= 0 (T 8 4))

(<= 0 (T 1 5)) (<= 0 (T 2 5)) (<= 0 (T 3 5)) (<= 0 (T 4 5))
(<= 0 (T 5 5)) (<= 0 (T 6 5)) (<= 0 (T 7 5)) (<= 0 (T 8 5))

; At most 8 pallets per truck
(>= 8 (+ (T 1 1) (T 1 2) (T 1 3) (T 1 4) (T 1 5)))
(>= 8 (+ (T 2 1) (T 2 2) (T 2 3) (T 2 4) (T 2 5)))
(>= 8 (+ (T 3 1) (T 3 2) (T 3 3) (T 3 4) (T 3 5)))
(>= 8 (+ (T 4 1) (T 4 2) (T 4 3) (T 4 4) (T 4 5)))
(>= 8 (+ (T 5 1) (T 5 2) (T 5 3) (T 5 4) (T 5 5)))
(>= 8 (+ (T 6 1) (T 6 2) (T 6 3) (T 6 4) (T 6 5)))
(>= 8 (+ (T 7 1) (T 7 2) (T 7 3) (T 7 4) (T 7 5)))
(>= 8 (+ (T 8 1) (T 8 2) (T 8 3) (T 8 4) (T 8 5)))

; Skipples need to be cooled, thereby they can only be transported
; by trucks 1, 2 or 3.
(= 0 (T 4 3)) (= 0 (T 5 3)) (= 0 (T 6 3)) (= 0 (T 7 3)) (= 0 (T 8 3))

; Nuzzles are very valuable not two on the same truck
(>= 1 (T 1 1)) (>= 1 (T 2 1)) (>= 1 (T 3 1)) (>= 1 (T 4 1)) 
(>= 1 (T 5 1)) (>= 1 (T 6 1)) (>= 1 (T 7 1)) (>= 1 (T 8 1))

))

; Goal
(maximize n)

; Optimizaiton + Optimum values
(check-sat)
(get-objectives)
