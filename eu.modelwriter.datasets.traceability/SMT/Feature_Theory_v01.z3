; Feature_Theory Begin
(set-option :print-success false)
(set-option :produce-models true)
(set-option :produce-unsat-cores true)
(set-option :produce-assignments true)
(set-logic UF)

; Example Begin
(declare-datatypes () ((Feature a b c d e)))
(declare-rel root (Feature))
(declare-rel depend (Feature Feature))
;(declare-rel mandatory (Feature Feature))
;(declare-rel optional (Feature Feature))
;(declare-rel alternative (Feature Feature))
;(declare-rel _or (Feature Feature))
;(declare-rel requires (Feature Feature))
;(declare-rel excludes (Feature Feature))

;Partial Relations based on the current Instance
(define-fun requires ((x!0 Feature) (x!1 Feature)) Bool false)
(define-fun optional ((x!0 Feature) (x!1 Feature)) Bool false)
(define-fun mandatory ((x!0 Feature) (x!1 Feature)) Bool false)

(define-fun alternative ((x!0 Feature) (x!1 Feature)) Bool
  (ite (and (= x!0 b) (= x!1 d)) true
  (ite (and (= x!0 b) (= x!1 e)) true
    false)))
    
(define-fun _or ((x!0 Feature) (x!1 Feature)) Bool
  (ite (and (= x!0 a) (= x!1 c)) true
  (ite (and (= x!0 a) (= x!1 b)) true
    false)))
    
(define-fun excludes ((x!0 Feature) (x!1 Feature)) Bool
  (ite (and (= x!0 b) (= x!1 c)) true
    false))

;(assert (root a))
;(assert (_or a c))
;(assert (_or a b))
;(assert (alternative b d ))
;(assert (alternative b e))
;(assert (excludes b c))

; Example End

; There is at most one relation between two features
(assert
  (forall ((f1 Feature) (f2 Feature))
    ( and
      (=> (requires f1 f2) (not (mandatory f1 f2)))
      (=> (requires f1 f2) (not (optional f1 f2)))
      (=> (requires f1 f2) (not (alternative f1 f2)))
      (=> (requires f1 f2) (not (_or f1 f2)))
      (=> (requires f1 f2) (not (excludes f1 f2)))
      
      (=> (requires f1 f2) (not (mandatory f2 f1)))
      (=> (requires f1 f2) (not (optional f2 f1)))
      (=> (requires f1 f2) (not (alternative f2 f1)))
      (=> (requires f1 f2) (not (_or f2 f1)))
      (=> (requires f1 f2) (not (excludes f2 f1)))
      
      (=> (mandatory f1 f2) (not (requires f1 f2)))
      (=> (mandatory f1 f2) (not (optional f1 f2)))
      (=> (mandatory f1 f2) (not (alternative f1 f2)))
      (=> (mandatory f1 f2) (not (_or f1 f2)))
      (=> (mandatory f1 f2) (not (excludes f1 f2)))
      
      (=> (mandatory f1 f2) (not (requires f2 f1)))
      (=> (mandatory f1 f2) (not (optional f2 f1)))
      (=> (mandatory f1 f2) (not (alternative f2 f1)))
      (=> (mandatory f1 f2) (not (_or f2 f1)))
      (=> (mandatory f1 f2) (not (excludes f2 f1)))
      
      (=> (optional f1 f2) (not (requires f1 f2)))
      (=> (optional f1 f2) (not (mandatory f1 f2)))
      (=> (optional f1 f2) (not (alternative f1 f2)))
      (=> (optional f1 f2) (not (_or f1 f2)))
      (=> (optional f1 f2) (not (excludes f1 f2)))
      
      (=> (optional f1 f2) (not (requires f2 f1)))
      (=> (optional f1 f2) (not (mandatory f2 f1)))
      (=> (optional f1 f2) (not (alternative f2 f1)))
      (=> (optional f1 f2) (not (_or f2 f1)))
      (=> (optional f1 f2) (not (excludes f2 f1)))
      
      (=> (alternative f1 f2) (not (requires f1 f2)))
      (=> (alternative f1 f2) (not (mandatory f1 f2)))
      (=> (alternative f1 f2) (not (optional f1 f2)))
      (=> (alternative f1 f2) (not (_or f1 f2)))
      (=> (alternative f1 f2) (not (excludes f1 f2)))
      
      (=> (alternative f1 f2) (not (requires f2 f1)))
      (=> (alternative f1 f2) (not (mandatory f2 f1)))
      (=> (alternative f1 f2) (not (optional f2 f1)))
      (=> (alternative f1 f2) (not (_or f2 f1)))
      (=> (alternative f1 f2) (not (excludes f2 f1)))
      
      (=> (_or f1 f2) (not (requires f1 f2)))
      (=> (_or f1 f2) (not (mandatory f1 f2)))
      (=> (_or f1 f2) (not (optional f1 f2)))
      (=> (_or f1 f2) (not (alternative f1 f2)))
      (=> (_or f1 f2) (not (excludes f1 f2)))
      
      (=> (_or f1 f2) (not (requires f2 f1)))
      (=> (_or f1 f2) (not (mandatory f2 f1)))
      (=> (_or f1 f2) (not (optional f2 f1)))
      (=> (_or f1 f2) (not (alternative f2 f1)))
      (=> (_or f1 f2) (not (excludes f2 f1)))
      
      (=> (excludes f1 f2) (not (requires f1 f2)))
      (=> (excludes f1 f2) (not (mandatory f1 f2)))
      (=> (excludes f1 f2) (not (optional f1 f2)))
      (=> (excludes f1 f2) (not (alternative f1 f2)))
      (=> (excludes f1 f2) (not (_or f1 f2)))
      
      (=> (excludes f1 f2) (not (requires f2 f1)))
      (=> (excludes f1 f2) (not (mandatory f2 f1)))
      (=> (excludes f1 f2) (not (optional f2 f1)))
      (=> (excludes f1 f2) (not (alternative f2 f1)))
      (=> (excludes f1 f2) (not (_or f2 f1)))
    )
  )
)

; reflexive depend
(assert
  (forall ((f Feature))
    (depend f f)
  )
)

; Non-reflexive requires
(assert
  (forall ((f Feature))
    (not (requires f f))
  )
)

; Non-reflexive mandatory
(assert
  (forall ((f Feature))
    (not (mandatory f f))
  )
)

; Non-reflexive requires
(assert
  (forall ((f Feature))
    (not (optional f f))
  )
)

; Non-reflexive requires
(assert
  (forall ((f Feature))
    (not (alternative f f))
  )
)

; Non-reflexive requires
(assert
  (forall ((f Feature))
    (not (_or f f))
  )
)

; Non-reflexive requires
(assert
  (forall ((f Feature))
    (not (requires f f))
  )
)

; Non-Symmetric depend
(assert
  (forall ((f1 Feature)(f2 Feature))
    (=> (and (not (= f1 f2))(depend f1 f2)) (not (depend f2 f1)))
  )
)

; Non-Symmetric requires
(assert
  (forall ((f1 Feature)(f2 Feature))
    (=> (requires f1 f2) (not (requires f2 f1)))
  )
)

; Non-Symmetric mandatory
(assert
  (forall ((f1 Feature)(f2 Feature))
    (=> (mandatory f1 f2) (not (mandatory f2 f1)))
  )
)

; Non-Symmetric optional
(assert
  (forall ((f1 Feature)(f2 Feature))
    (=> (optional f1 f2) (not (optional f2 f1)))
  )
)

; Non-Symmetric alternative
(assert
  (forall ((f1 Feature)(f2 Feature))
    (=> (alternative f1 f2) (not (alternative f2 f1)))
  )
)

; Non-Symmetric _or
(assert
  (forall ((f1 Feature)(f2 Feature))
    (=> (_or f1 f2) (not (_or f2 f1)))
  )
)

; transitive depends
(assert
  (forall ((f1 Feature)(f2 Feature)(f3 Feature))
    (=> (and (depend f1 f2)(depend f2 f3)) (depend f1 f3))
  )
)

; All in depend
(assert
  (forall ((f1 Feature)(f2 Feature))
    (=> (or (mandatory f1 f2) (optional f1 f2) (alternative f1 f2) (_or f1 f2)) (depend f1 f2))
  )
)

; there is at least one root
(assert 
  (exists ((f Feature))
    (root f)
  )
)

; if there is a root, there is only one root
(assert
  (forall ((f1 Feature)(f2 Feature))
    (=> (and (root f1)(root f2)) (= f1 f2))
  )
)

; all features depends on the root
(assert 
  (forall ((f1 Feature)(f2 Feature))
    (=> (root f1) (depend f1 f2))
  )
)

; all features excluding root are in the range of at least one "mandatory or optional or alternative or _or" relation
(assert 
  (forall ((f1 Feature))
    (=> (not (root f1))
       (exists ((f2 Feature))
         (or (mandatory f2 f1)(optional f2 f1)(alternative f2 f1)(_or f2 f1))
       )
    )
  )
)

; all features excluding root are in the range of at most one "mandatory or optional or alternative or _or" relation
(assert 
  (forall ((f1 Feature)(f2 Feature)(f3 Feature))
    (=> (not (root f1)) (=> (or (and (mandatory f2 f1) (mandatory f3 f1)) (and (optional f2 f1) (optional f3 f1)) (and (alternative f2 f1)(alternative f3 f1)) (and (_or f2 f1) (_or f3 f1))) (= f2 f3)) )
  )
)

; Feature_Theory End


(check-sat)
;(get-unsat-core)
(get-value (a b c d e))
(get-value ((root a))) ;true
(get-value ((_or a c)))
(get-value ((_or a b)))
(get-value ((alternative b d)))
(get-value ((alternative b e)))
(get-value ((excludes b c)))
(get-value ((excludes c b)))
(get-value ((mandatory a c)))
(get-value ((mandatory b c)))
(get-value ((optional a c)))
(get-value ((requires d a)))
(get-value ((optional c d)))
(get-value ((optional a e)))
(get-value ((= c a)))
(get-model)
