;Requirements_Theory Begin
(set-option :print-success false)
(set-option :produce-models true)
(set-option :produce-unsat-cores true)
(set-option :produce-assignments true)
(set-logic UF)

; Example Begin

(declare-datatypes () ((Requirement Requirement12 Requirement45 Requirement28 Requirement1 Requirement47 Requirement18 Requirement43 Requirement10 Requirement26 Requirement16 Requirement9 Requirement7 Requirement14 Requirement21 Requirement35 Requirement25 Requirement31 Requirement3 Requirement33 Requirement5 Requirement38 Requirement23 Requirement37 Requirement41 Requirement2 Requirement19 Requirement44 Requirement42 Requirement13 Requirement29 Requirement11 Requirement27 Requirement17 Requirement15 Requirement8 Requirement46 Requirement20 Requirement34 Requirement32 Requirement4 Requirement30 Requirement24 Requirement22 Requirement36 Requirement40 Requirement6 Requirement39)))

(declare-fun requires (Requirement Requirement) Bool)
(declare-fun contains (Requirement Requirement) Bool)
(declare-fun refines (Requirement Requirement) Bool)
(declare-fun p_refines (Requirement Requirement) Bool)
(declare-fun conflicts (Requirement Requirement) Bool)
(declare-fun _equals (Requirement Requirement) Bool)

(assert (conflicts Requirement12 Requirement9))
(assert (conflicts Requirement12 Requirement11))
(assert (conflicts Requirement12 Requirement10))
(assert (requires Requirement12 Requirement18))
(assert (requires Requirement12 Requirement17))
(assert (refines Requirement12 Requirement8))
(assert (conflicts Requirement28 Requirement29))
(assert (refines Requirement28 Requirement27))
(assert (requires Requirement47 Requirement46))
(assert (requires Requirement47 Requirement45))
(assert (requires Requirement47 Requirement44))
(assert (refines Requirement18 Requirement16))
(assert (conflicts Requirement10 Requirement9))
(assert (conflicts Requirement10 Requirement12))
(assert (conflicts Requirement10 Requirement11))
(assert (requires Requirement10 Requirement18))
(assert (refines Requirement10 Requirement8))
(assert (requires Requirement26 Requirement38))
(assert (requires Requirement26 Requirement34))
(assert (requires Requirement26 Requirement36))
(assert (requires Requirement26 Requirement35))
(assert (requires Requirement26 Requirement33))
(assert (refines Requirement26 Requirement25))
(assert (conflicts Requirement9 Requirement12))
(assert (conflicts Requirement9 Requirement10))
(assert (conflicts Requirement9 Requirement11))
(assert (requires Requirement9 Requirement18))
(assert (refines Requirement9 Requirement8))
(assert (refines Requirement7 Requirement4))
(assert (conflicts Requirement14 Requirement15))
(assert (conflicts Requirement14 Requirement13))
(assert (refines Requirement14 Requirement8))
(assert (conflicts Requirement21 Requirement20))
(assert (requires Requirement21 Requirement22))
(assert (refines Requirement21 Requirement19))
(assert (contains Requirement31 Requirement26))
(assert (contains Requirement31 Requirement22))
(assert (conflicts Requirement3 Requirement2))
(assert (refines Requirement3 Requirement1))
(assert (conflicts Requirement5 Requirement11))
(assert (conflicts Requirement5 Requirement6))
(assert (refines Requirement5 Requirement4))
(assert (requires Requirement38 Requirement40))
(assert (requires Requirement38 Requirement41))
(assert (requires Requirement38 Requirement30))
(assert (conflicts Requirement23 Requirement24))
(assert (refines Requirement23 Requirement22))
(assert (requires Requirement37 Requirement25))
(assert (requires Requirement41 Requirement45))
(assert (requires Requirement41 Requirement43))
(assert (requires Requirement41 Requirement30))
(assert (requires Requirement41 Requirement46))
(assert (conflicts Requirement2 Requirement3))
(assert (refines Requirement2 Requirement1))
(assert (requires Requirement19 Requirement25))
(assert (refines Requirement44 Requirement41))
(assert (requires Requirement42 Requirement45))
(assert (requires Requirement42 Requirement46))
(assert (conflicts Requirement13 Requirement15))
(assert (conflicts Requirement13 Requirement6))
(assert (conflicts Requirement13 Requirement14))
(assert (refines Requirement13 Requirement8))
(assert (conflicts Requirement29 Requirement28))
(assert (requires Requirement29 Requirement32))
(assert (requires Requirement29 Requirement30))
(assert (refines Requirement29 Requirement27))
(assert (conflicts Requirement11 Requirement9))
(assert (conflicts Requirement11 Requirement5))
(assert (conflicts Requirement11 Requirement12))
(assert (conflicts Requirement11 Requirement10))
(assert (requires Requirement11 Requirement17))
(assert (refines Requirement11 Requirement8))
(assert (refines Requirement27 Requirement25))
(assert (refines Requirement17 Requirement16))
(assert (conflicts Requirement15 Requirement14))
(assert (conflicts Requirement15 Requirement13))
(assert (requires Requirement15 Requirement6))
(assert (refines Requirement15 Requirement8))
(assert (conflicts Requirement20 Requirement21))
(assert (requires Requirement20 Requirement26))
(assert (refines Requirement20 Requirement19))
(assert (requires Requirement34 Requirement40))
(assert (requires Requirement34 Requirement30))
(assert (contains Requirement32 Requirement33))
(assert (contains Requirement32 Requirement38))
(assert (contains Requirement32 Requirement35))
(assert (contains Requirement32 Requirement37))
(assert (contains Requirement32 Requirement34))
(assert (contains Requirement32 Requirement36))
(assert (conflicts Requirement24 Requirement23))
(assert (requires Requirement24 Requirement30))
(assert (requires Requirement24 Requirement40))
(assert (refines Requirement24 Requirement22))
(assert (p_refines Requirement24 Requirement31))
(assert (requires Requirement36 Requirement40))
(assert (requires Requirement36 Requirement30))
(assert (contains Requirement40 Requirement41))
(assert (contains Requirement40 Requirement42))
(assert (conflicts Requirement6 Requirement13))
(assert (conflicts Requirement6 Requirement5))
(assert (refines Requirement6 Requirement4))
(assert (refines Requirement39 Requirement38))

; Example End

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

; Non-reflexive contains
(assert
  (forall ((r Requirement))
    (not (contains r r))
  )
)

; Non-Symmetric contains
(assert
  (forall ((r1 Requirement)(r2 Requirement))
    (=> (contains r1 r2) (not (contains r2 r1)))
  )
)

; Transitive contains
(assert 
  (forall ((r1 Requirement) (r2 Requirement) (r3 Requirement)) 
    (=> (and (contains r1 r2) (contains r2 r3))
      (contains r1 r3)
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
      (=> (and (_equals r1 r2) (contains r2 r3)) (contains r1 r3))
      (=> (and (_equals r1 r2) (conflicts r2 r3)) (conflicts r1 r3))
      
      (=> (and (requires r1 r2) (_equals r2 r3)) (requires r1 r3))
      (=> (and (refines r1 r2) (_equals r2 r3)) (refines r1 r3))
      (=> (and (p_refines r1 r2) (_equals r2 r3)) (p_refines r1 r3))
      (=> (and (contains r1 r2) (_equals r2 r3)) (contains r1 r3))
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
;(get-unsat-core)
