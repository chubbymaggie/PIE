(set-option :produce-models true)
(set-option :strings-fmf true)

(set-logic QF_S)

(declare-const s0 String)
(declare-const r String)
(declare-const i Int)
(declare-const j Int)
(declare-const x Int)

(assert (> (str.len s0) 0))
(assert (and (>= i 0) (< i (str.len s0))))
(assert (and (>= j i) (< j (str.len s0))))

;; Invariant :: (r == s0.substr(i, x - i)) /\ (x <= j+1)

(define-fun post_check () Bool
            (=> (and (and (= r (str.substr s0 i (- x i))) (<= x (+ j 1))) (not (<= x j)))
                (= r (str.substr s0 i (+ 1 (- j i))))))

(assert (not post_check))
(check-sat)

(get-value (s0 r i j x))
