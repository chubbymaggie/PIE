(set-option :produce-models true)
(set-option :strings-fmf true)

(set-logic QF_S)

(declare-const r String)
(declare-const i Int)

;; Invariant :: (len(r) == 2i + 1) /\ (r = "a" \/ contains(r, "(a)"))

(define-fun ind_check () Bool
            (=> (and (= (str.len r) (+ 1 (* 2 i)))
                     (or (= r "a") (str.contains r "(a)")))
                (and (= (str.len (str.++ "(" r ")")) (+ 1 (* 2 (+ i 1))))
                     (or (= (str.++ "(" r ")") "a") (str.contains (str.++ "(" r ")") "(a)")))))

(assert (not ind_check))
(check-sat)

(get-value (r i))
