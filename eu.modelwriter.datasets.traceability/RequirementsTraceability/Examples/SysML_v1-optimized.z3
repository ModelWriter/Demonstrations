;Requirements_Theory Begin
(set-option :print-success false)
(set-option :produce-models true)
(set-option :produce-unsat-cores true)
(set-option :produce-assignments true)
(set-logic UF)

; Example Begin

(declare-datatypes () ((Requirement Requirement12 Requirement2 Requirement13 Requirement1 Requirement11 Requirement10 Requirement9 Requirement16 Requirement15 Requirement8 Requirement14 Requirement7 Requirement4 Requirement3 Requirement5 Requirement6)))

(declare-fun requires (Requirement Requirement) Bool)
(declare-fun contains (Requirement Requirement) Bool)
(declare-fun refines (Requirement Requirement) Bool)
(declare-fun p_refines (Requirement Requirement) Bool)
(declare-fun conflicts (Requirement Requirement) Bool)
(declare-fun _equals (Requirement Requirement) Bool)

(assert (!(requires Requirement13 Requirement16):named req_13_16))
(assert (!(contains Requirement1 Requirement2):named con_1_2))
(assert (!(contains Requirement1 Requirement5):named con_1_5))
(assert (!(contains Requirement1 Requirement3):named con_1_3))
(assert (!(contains Requirement1 Requirement6):named con_1_6))
(assert (!(contains Requirement1 Requirement4):named con_1_4))
(assert (!(contains Requirement1 Requirement7):named con_1_7))
(assert (!(requires Requirement11 Requirement15):named req_11_15))
(assert (!(requires Requirement11 Requirement14):named req_11_14))
(assert (!(requires Requirement10 Requirement14):named req_10_14))
(assert (!(requires Requirement10 Requirement13):named req_10_13))
(assert (!(requires Requirement10 Requirement12):named req_10_12))
(assert (!(contains Requirement9 Requirement10):named con_9_10))
(assert (!(contains Requirement9 Requirement11):named con_9_11))
(assert (!(requires Requirement15 Requirement16):named req_15_16))
(assert (!(requires Requirement14 Requirement16):named req_14_16))
(assert (!(requires Requirement7 Requirement8):named req_7_8))
(assert (!(requires Requirement7 Requirement9):named req_7_9))
(assert (!(requires Requirement3 Requirement9):named req_3_9))
(assert (!(requires Requirement5 Requirement9):named req_5_9))
(assert (!(refines Requirement6 Requirement8):named ref_6_8))

; Example End

(assert
  (forall ((r Requirement))
    ( and
      (_equals r r)
      (not (conflicts r r))
      (not (p_refines r r))
      (not (refines r r))
      (not (contains r r))
      (not (requires r r))
    )
  )
)


(assert
  (forall ((r1 Requirement) (r2 Requirement))
    ( and
      (=> (requires r1 r2) (and (not (requires r2 r1)) (not (refines r1 r2)) (not (refines r2 r1)) (not (contains r1 r2)) (not (contains r2 r1)) (not (p_refines r1 r2)) (not (p_refines r2 r1)) (not (_equals r1 r2)) (not (_equals r2 r1)) (not (conflicts r1 r2)) (not (conflicts r2 r1))))
      (=> (refines r1 r2) (and (not (refines r2 r1)) (not (requires r1 r2)) (not (requires r2 r1)) (not (contains r1 r2)) (not (contains r2 r1)) (not (p_refines r1 r2)) (not (p_refines r2 r1)) (not (_equals r1 r2)) (not (_equals r2 r1)) (not (conflicts r1 r2)) (not (conflicts r2 r1))))
      (=> (contains r1 r2) (and (not (contains r2 r1)) (not (refines r1 r2)) (not (refines r2 r1)) (not (requires r1 r2)) (not (requires r2 r1)) (not (p_refines r1 r2)) (not (p_refines r2 r1)) (not (_equals r1 r2)) (not (_equals r2 r1)) (not (conflicts r1 r2)) (not (conflicts r2 r1))))
      (=> (p_refines r1 r2) (and (not (p_refines r2 r1)) (not (refines r1 r2)) (not (refines r2 r1)) (not (contains r1 r2)) (not (contains r2 r1)) (not (requires r1 r2)) (not (requires r2 r1)) (not (_equals r1 r2)) (not (_equals r2 r1)) (not (conflicts r1 r2)) (not (conflicts r2 r1))))      
      (=> (_equals r1 r2) (and (_equals r2 r1) (not (refines r1 r2)) (not (refines r2 r1)) (not (contains r1 r2)) (not (contains r2 r1)) (not (p_refines r1 r2)) (not (p_refines r2 r1)) (not (requires r1 r2)) (not (requires r2 r1)) (not (conflicts r1 r2)) (not (conflicts r2 r1))))
      (=> (conflicts r1 r2) (and (conflicts r2 r1) (not (refines r1 r2)) (not (refines r2 r1)) (not (contains r1 r2)) (not (contains r2 r1)) (not (p_refines r1 r2)) (not (p_refines r2 r1)) (not (_equals r1 r2)) (not (_equals r2 r1)) (not (requires r1 r2)) (not (requires r2 r1))))
    )
  )
)


; infering
(assert 
  (forall ((r1 Requirement) (r2 Requirement) (r3 Requirement)) 
    ( and 
      (=> (and (or (requires r1 r2) (refines r1 r2) (contains r1 r2)) (conflicts r2 r3)) (conflicts r1 r3))
      (=> (and (contains r1 r2) (p_refines r2 r3)) (p_refines r1 r3))
      (=> (and (refines r1 r2) (p_refines r2 r3)) (p_refines r1 r3))
      (=> (and (p_refines r1 r2) (refines r2 r3)) (p_refines r1 r3))
      (=> (and (contains r1 r2) (refines r2 r3)) (refines r1 r3))
      (=> (and (refines r1 r2) (contains r2 r3)) (refines r1 r3))
      (=> (and (requires r1 r2) (refines r2 r3) (not (refines r1 r3)) (not (contains r1 r3))) (requires r1 r3))
      (=> (and (refines r1 r2) (requires r2 r3) (not (refines r1 r3)) (not (contains r1 r3))) (requires r1 r3))
      (=> (and (requires r1 r2) (contains r2 r3) (not (refines r1 r3)) (not (contains r1 r3))) (requires r1 r3))
      (=> (and (contains r1 r2) (requires r2 r3) (not (refines r1 r3)) (not (contains r1 r3))) (requires r1 r3))

      (=> (and (_equals r1 r2) (requires r2 r3)) (requires r1 r3))
      (=> (and (_equals r1 r2) (refines r2 r3)) (refines r1 r3))
      (=> (and (_equals r1 r2) (p_refines r2 r3)) (p_refines r1 r3))
      (=> (and (_equals r1 r2) (contains r2 r3)) (contains r1 r3))
      (=> (and (_equals r1 r2) (conflicts r2 r3)) (conflicts r1 r3))
      
      (=> (and (requires r1 r2) (_equals r2 r3)) (requires r1 r3))
      (=> (and (refines r1 r2) (_equals r2 r3)) (refines r1 r3))
      (=> (and (p_refines r1 r2) (_equals r2 r3)) (p_refines r1 r3))
      (=> (and (contains r1 r2) (_equals r2 r3)) (contains r1 r3))
      (=> (and (conflicts r1 r2) (_equals r2 r3)) (conflicts r1 r3))

      (=> (and (p_refines r1 r2) (p_refines r2 r3))(p_refines r1 r3))
      (=> (and (refines r1 r2) (refines r2 r3))(refines r1 r3))
      (=> (and (contains r1 r2) (contains r2 r3))(contains r1 r3))
      (=> (and (requires r1 r2) (requires r2 r3))(requires r1 r3))
      (=> (and (_equals r1 r2) (_equals r2 r3))(_equals r1 r3))
    )
  )
)

; Requirements_Theory End

(check-sat)
;(get-model)
(get-unsat-core)
