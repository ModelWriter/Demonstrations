;Requirements_Theory Begin
(set-option :print-success false)
(set-option :produce-models true)
(set-option :produce-unsat-cores true)
(set-option :produce-assignments true)
(set-logic UF)

(declare-datatypes () ((Requirement Requirement12 Requirement2 Requirement13 Requirement1 Requirement11 Requirement10 Requirement9 Requirement16 Requirement15 Requirement8 Requirement14 Requirement7 Requirement4 Requirement3 Requirement5 Requirement6)))

(declare-fun requires (Requirement Requirement) Bool)
(declare-fun refines (Requirement Requirement) Bool)
(declare-fun p_refines (Requirement Requirement) Bool)
(declare-fun conflicts (Requirement Requirement) Bool)
(declare-fun _equals (Requirement Requirement) Bool)

(assert (!(requires Requirement13 Requirement16):named requ_13_16))
(assert (!(requires Requirement11 Requirement15):named requ_11_15))
(assert (!(requires Requirement11 Requirement14):named requ_11_14))
(assert (!(requires Requirement10 Requirement14):named requ_10_14))
(assert (!(requires Requirement10 Requirement13):named requ_10_13))
(assert (!(requires Requirement10 Requirement12):named requ_10_12))
(assert (!(requires Requirement15 Requirement16):named requ_15_16))
(assert (!(requires Requirement14 Requirement16):named requ_14_16))
(assert (!(requires Requirement7 Requirement8):named requ_7_8))
(assert (!(requires Requirement7 Requirement9):named requ_7_9))
(assert (!(requires Requirement3 Requirement9):named requ_3_9))
(assert (!(requires Requirement5 Requirement9):named requ_5_9))
(assert (!(refines Requirement6 Requirement8):named refi_6_8))

(define-fun contains ((x!0 Requirement) (x!1 Requirement)) Bool 
(ite ( and (= x!0 Requirement1) (= x!1 Requirement2)) true
(ite ( and (= x!0 Requirement1) (= x!1 Requirement5)) true
(ite ( and (= x!0 Requirement1) (= x!1 Requirement3)) true
(ite ( and (= x!0 Requirement1) (= x!1 Requirement6)) true
(ite ( and (= x!0 Requirement1) (= x!1 Requirement4)) true
(ite ( and (= x!0 Requirement1) (= x!1 Requirement7)) true
(ite ( and (= x!0 Requirement9) (= x!1 Requirement10)) true
(ite ( and (= x!0 Requirement9) (= x!1 Requirement11)) true
false)))))))))

; Non-reflexive requires
(assert
  (forall ((r Requirement))
    (not (requires r r))
  )
)

; Non-Symmetric requires
(assert
  (forall ((r1 Requirement)(r2 Requirement))
    (=> (requires r1 r2) (not (requires r2 r1)))
  )
)

; Transitive requires
(assert 
  (forall ((r1 Requirement) (r2 Requirement) (r3 Requirement)) 
    (=> (and (requires r1 r2) (requires r2 r3))
      (requires r1 r3)
    )
  )
)

; Non-reflexive refines
(assert
  (forall ((r Requirement))
    (not (refines r r))
  )
)

; Non-Symmetric refines
(assert
  (forall ((r1 Requirement)(r2 Requirement))
    (=> (refines r1 r2) (not (refines r2 r1)))
  )
)

; Transitive refines
(assert 
  (forall ((r1 Requirement) (r2 Requirement) (r3 Requirement)) 
    (=> (and (refines r1 r2) (refines r2 r3))
      (refines r1 r3)
    )
  )
)

; Non-reflexive p_refines
(assert
  (forall ((r Requirement))
    (not (p_refines r r))
  )
)

; Non-Symmetric p_refines
(assert
  (forall ((r1 Requirement)(r2 Requirement))
    (=> (p_refines r1 r2) (not (p_refines r2 r1)))
  )
)

; Transitive p_refines
(assert 
  (forall ((r1 Requirement) (r2 Requirement) (r3 Requirement)) 
    (=> (and (p_refines r1 r2) (p_refines r2 r3))
      (p_refines r1 r3)
    )
  )
)

; Non-reflexive conflicts
(assert
  (forall ((r Requirement))
    (not (conflicts r r))
  )
)

; Symmetric conflicts
(assert
  (forall ((r1 Requirement)(r2 Requirement))
    (=> (conflicts r1 r2) (conflicts r2 r1))
  )
)

; Reflexive _equals
(assert
  (forall ((r Requirement))
    (_equals r r)
  )
)

; Symmetric _equals
(assert
  (forall ((r1 Requirement)(r2 Requirement))
    (=> (_equals r1 r2) (_equals r2 r1))
  )
)

; Transitive _equals
(assert 
  (forall ((r1 Requirement) (r2 Requirement) (r3 Requirement)) 
    (=> (and (_equals r1 r2) (_equals r2 r3))
      (_equals r1 r3)
    )
  )
)

; There is at most one relation between two requirements
(assert
  (forall ((r1 Requirement) (r2 Requirement))
    ( and
      (=> (requires r1 r2) (not (refines r1 r2)))
      (=> (requires r1 r2) (not (contains r1 r2)))
      (=> (requires r1 r2) (not (p_refines r1 r2)))
      (=> (requires r1 r2) (not (_equals r1 r2)))
      (=> (requires r1 r2) (not (conflicts r1 r2)))
      
      (=> (requires r1 r2) (not (refines r2 r1)))
      (=> (requires r1 r2) (not (contains r2 r1)))
      (=> (requires r1 r2) (not (p_refines r2 r1)))
      (=> (requires r1 r2) (not (_equals r2 r1)))
      (=> (requires r1 r2) (not (conflicts r2 r1)))
      
      (=> (refines r1 r2) (not (requires r1 r2)))
      (=> (refines r1 r2) (not (contains r1 r2)))
      (=> (refines r1 r2) (not (p_refines r1 r2)))
      (=> (refines r1 r2) (not (_equals r1 r2)))
      (=> (refines r1 r2) (not (conflicts r1 r2)))
      
      (=> (refines r1 r2) (not (requires r2 r1)))
      (=> (refines r1 r2) (not (contains r2 r1)))
      (=> (refines r1 r2) (not (p_refines r2 r1)))
      (=> (refines r1 r2) (not (_equals r2 r1)))
      (=> (refines r1 r2) (not (conflicts r2 r1)))
      
      (=> (contains r1 r2) (not (requires r1 r2)))
      (=> (contains r1 r2) (not (refines r1 r2)))
      (=> (contains r1 r2) (not (p_refines r1 r2)))
      (=> (contains r1 r2) (not (_equals r1 r2)))
      (=> (contains r1 r2) (not (conflicts r1 r2)))
      
      (=> (contains r1 r2) (not (requires r2 r1)))
      (=> (contains r1 r2) (not (refines r2 r1)))
      (=> (contains r1 r2) (not (p_refines r2 r1)))
      (=> (contains r1 r2) (not (_equals r2 r1)))
      (=> (contains r1 r2) (not (conflicts r2 r1)))
      
      (=> (p_refines r1 r2) (not (requires r1 r2)))
      (=> (p_refines r1 r2) (not (refines r1 r2)))
      (=> (p_refines r1 r2) (not (contains r1 r2)))
      (=> (p_refines r1 r2) (not (_equals r1 r2)))
      (=> (p_refines r1 r2) (not (conflicts r1 r2)))
      
      (=> (p_refines r1 r2) (not (requires r2 r1)))
      (=> (p_refines r1 r2) (not (refines r2 r1)))
      (=> (p_refines r1 r2) (not (contains r2 r1)))
      (=> (p_refines r1 r2) (not (_equals r2 r1)))
      (=> (p_refines r1 r2) (not (conflicts r2 r1)))
      
      (=> (_equals r1 r2) (not (requires r1 r2)))
      (=> (_equals r1 r2) (not (refines r1 r2)))
      (=> (_equals r1 r2) (not (contains r1 r2)))
      (=> (_equals r1 r2) (not (p_refines r1 r2)))
      (=> (_equals r1 r2) (not (conflicts r1 r2)))
      
      (=> (_equals r1 r2) (not (requires r2 r1)))
      (=> (_equals r1 r2) (not (refines r2 r1)))
      (=> (_equals r1 r2) (not (contains r2 r1)))
      (=> (_equals r1 r2) (not (p_refines r2 r1)))
      (=> (_equals r1 r2) (not (conflicts r2 r1)))
      
      (=> (conflicts r1 r2) (not (requires r1 r2)))
      (=> (conflicts r1 r2) (not (refines r1 r2)))
      (=> (conflicts r1 r2) (not (contains r1 r2)))
      (=> (conflicts r1 r2) (not (p_refines r1 r2)))
      (=> (conflicts r1 r2) (not (_equals r1 r2)))
      
      (=> (conflicts r1 r2) (not (requires r2 r1)))
      (=> (conflicts r1 r2) (not (refines r2 r1)))
      (=> (conflicts r1 r2) (not (contains r2 r1)))
      (=> (conflicts r1 r2) (not (p_refines r2 r1)))
      (=> (conflicts r1 r2) (not (_equals r2 r1)))
    )
  )
)

; _equals facts
(assert 
  (forall ((r1 Requirement) (r2 Requirement) (r3 Requirement)) 
    ( and 
      (=> (and (_equals r1 r2) (requires r2 r3)) (requires r1 r3))
      (=> (and (_equals r1 r2) (refines r2 r3)) (refines r1 r3))
      (=> (and (_equals r1 r2) (p_refines r2 r3)) (p_refines r1 r3))
      (=> (and (_equals r1 r2) (conflicts r2 r3)) (conflicts r1 r3))
      
      (=> (and (requires r1 r2) (_equals r2 r3)) (requires r1 r3))
      (=> (and (refines r1 r2) (_equals r2 r3)) (refines r1 r3))
      (=> (and (p_refines r1 r2) (_equals r2 r3)) (p_refines r1 r3))
      (=> (and (conflicts r1 r2) (_equals r2 r3)) (conflicts r1 r3))
    )
  )
)

; infer requires facts
(assert 
  (forall ((r1 Requirement) (r2 Requirement) (r3 Requirement)) 
    ( and 
      (=> (and (requires r1 r2) (refines r2 r3) (not (refines r1 r3)) (not (contains r1 r3))) (requires r1 r3))
      (=> (and (refines r1 r2) (requires r2 r3) (not (refines r1 r3)) (not (contains r1 r3))) (requires r1 r3))
      (=> (and (requires r1 r2) (contains r2 r3) (not (refines r1 r3)) (not (contains r1 r3))) (requires r1 r3))
      (=> (and (contains r1 r2) (requires r2 r3) (not (refines r1 r3)) (not (contains r1 r3))) (requires r1 r3))
    )
  )
)

; infer refines facts
(assert 
  (forall ((r1 Requirement) (r2 Requirement) (r3 Requirement)) 
    ( and 
      (=> (and (contains r1 r2) (refines r2 r3)) (refines r1 r3))
      (=> (and (refines r1 r2) (contains r2 r3)) (refines r1 r3))
    )
  )
)

; infer p_refines facts
(assert 
  (forall ((r1 Requirement) (r2 Requirement) (r3 Requirement)) 
    ( and 
      (=> (and (contains r1 r2) (p_refines r2 r3)) (p_refines r1 r3))
      (=> (and (refines r1 r2) (p_refines r2 r3)) (p_refines r1 r3))
      (=> (and (p_refines r1 r2) (refines r2 r3)) (p_refines r1 r3))
    )
  )
)

; infer conflicts facts
(assert 
  (forall ((r1 Requirement) (r2 Requirement) (r3 Requirement)) 
    (=> (and (or (requires r1 r2) (refines r1 r2) (contains r1 r2)) (conflicts r2 r3)) (conflicts r1 r3))
  )
)

; Requirements_Theory End

(check-sat)
(get-model)
(get-unsat-core)
(exit)
