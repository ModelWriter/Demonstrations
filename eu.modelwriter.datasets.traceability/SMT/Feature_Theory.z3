; http://rise4fun.com/Z3/BQfe
; Feature_Theory Begin
(set-option :produce-assignments true)

(declare-sort Feature)

(declare-fun root (Feature) Bool)

(declare-fun depend (Feature Feature) Bool)

(declare-fun mandatory (Feature Feature) Bool)
(declare-fun optional (Feature Feature) Bool)
(declare-fun alternative (Feature Feature) Bool)
(declare-fun _or (Feature Feature) Bool)
(declare-fun requires (Feature Feature) Bool)
(declare-fun excludes (Feature Feature) Bool)

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
    (
      root f
    )
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

; Example Begin



(declare-fun a () Feature)
(declare-fun b () Feature)
(declare-fun c () Feature)

(assert 
  (and (not (= a b)) (not (= b c)) (not (= a c)))
)

; cardinality constraint:
(assert 
  (forall ((x Feature))
          (or (= x a)
              (= x b)
              (= x c)
           )
  )
)

(assert (mandatory a b))
(assert (mandatory a c))

(assert
  (forall ((f1 Feature)(f2 Feature))
    (and 
      (ite 
       (or (and (= f1 a)(= f2 b)) (and (= f1 a)(= f2 c)) )
       (mandatory f1 f2)
       (not (mandatory f1 f2))
      )
      (not (optional f1 f2))
      (not (alternative f1 f2))
      (not (_or f1 f2))
      (not (excludes f1 f2))
      (not (requires f1 f2))
    )
  )
)

; Example End

(check-sat)
(get-value (a b c))
(get-value ((mandatory a b)))
(get-model)

