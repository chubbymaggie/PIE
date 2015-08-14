(set-option :produce-models true)
(set-option :strings-fmf true)

(set-logic QF_S)

(declare-const s0 String)
(declare-const s1 String)
(declare-const r String)
(declare-const i Int)

;; Invariant :: r = s0 ++ s1[0:i]

(define-fun ind_check () Bool
            (=> (and (< i (str.len s1)) (= r (str.++ s0 (str.substr s1 0 i))))
                (= (str.++ r (str.at s1 i)) (str.++ s0 (str.substr s1 0 (+ i 1))))))

(assert (not ind_check))
(check-sat)

(get-value (s0 s1 r i))
