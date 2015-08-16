(set-option :produce-models true)
(set-option :strings-fmf true)

(set-logic QF_S)

(declare-const r String)
(declare-const i Int)

;; Invariant :: (len(r) == 2i + 1) /\ (r = "a" \/ contains(r, "(a)"))

(define-fun pre_check () Bool
            (=> (and (= i 0) (= r "a"))
                (and (= (str.len r) (+ 1 (* 2 i))) (or (= r "a") (str.contains r "(a)")))))

(assert (not pre_check))
(check-sat)

(get-value (r i))
