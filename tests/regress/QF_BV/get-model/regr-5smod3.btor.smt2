(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (= (bvand (bvadd x #x01) (bvor y #x0f)) #x0a))
(check-sat)
(get-model)

