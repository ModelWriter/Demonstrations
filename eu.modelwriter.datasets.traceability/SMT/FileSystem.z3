(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)

(set-option :produce-unsat-cores true)

;---------------------------------------

;abstract sig FSO {
;parent: lone Dir
;}
;sig Dir extends FSO {
;contents: set FSO
;}
;sig File extends FSO {}

(declare-datatypes () ((FSO dir_1 dir_2 dir_3 dir_4)))

(declare-fun isFSO(FSO) Bool)
(declare-fun isDir(FSO) Bool)
(declare-fun isFile(FSO) Bool)

(assert (forall ((f FSO)) 
  (=> (isDir f) 
    (isFSO f))))

(assert (forall ((f FSO)) 
  (=> (isFile f) 
    (isFSO f))))

(assert (forall ((f FSO)) 
  (=> (isFSO f) 
    (or (isDir f) (isFile f) ) ) ) )
    
(assert (forall ((f FSO)) 
  (=> (isFSO f) 
    (not (and (isDir f) (isFile f) ) ) ) ) )
 
 
(declare-fun parent (FSO FSO) Bool)
(declare-fun oneParent (FSO) FSO)
(declare-fun contents (FSO FSO) Bool)

(assert (forall ((f FSO)(g FSO)) 
  (=> (parent f g) 
    (and (isFSO f) (isDir g)))))

(assert (forall ((f FSO)(g FSO))
    (=> (parent f g)
       (= g (oneParent f)))))      

(assert (forall ((f FSO)(g FSO)) 
  (=> (contents f g) 
    (and (isDir f) (isFSO g)))))

;------------------------------------------------------------

;fact {
;contents = ~parent
;all d:Dir | not(d in d.^contents)
;}

;contents = ~parent
(assert (and (forall ((x FSO)(y FSO)) (=> (contents x y) (parent y x) ) ) 
  (forall ((x FSO)(y FSO)) (=> (parent x y) (contents y x) ) ) ) )

;all d:Dir | not(d in d.^contents)
(declare-fun trContents(Int FSO FSO) Bool)

(assert (forall ((i Int)(f_1 FSO)(f_2 FSO)) 
  (=> (< i 1) 
    (not (trContents i f_1 f_2)) ) ) )

(assert (forall ((f_1 FSO)(f_2 FSO)) 
  (= (trContents 1 f_1 f_2) 
    (contents f_1 f_2) ) ) )

(assert (forall ((i Int)(f_1 FSO)(f_2 FSO)) 
  (=> (> i 1) 
    (= (trContents i f_1 f_2) 
      (or (trContents (- i 1) f_1 f_2) (exists ((w FSO)) (and (trContents (- i 1) f_1 w) (contents w f_2) ) ) ) ) ) ) )

(assert (forall ((d FSO)) 
  (=> (isDir d) 
    (not (exists ((i Int)) (trContents i d d) ) ) ) ) )

;--------------------------------------------------------------------

;assert oneLocation {
;all o:FSO, lone d:FSO|
;o in d.contents
;}

(assert (not (forall ((o FSO)) 
  (forall ((d_1 FSO)(d_2 FSO)) 
    (=> (and (contents d_1 o) (contents d_2 o) ) 
      (= d_1 d_2) ) ) ) ) )


;-------------------------------------------------------------------

;(assert (!(isDir dir_1) :named axiom1))
;(assert (!(isDir dir_2) :named axiom2))
;(assert (!(isDir dir_3) :named axiom3))
;(assert (!(isDir dir_4) :named axiom4))

;(assert (!(contents dir_1 dir_2) :named axiom5))
;(assert (!(contents dir_2 dir_3) :named axiom6))
;(assert (!(contents dir_3 dir_4) :named axiom7))
;(assert (!(contents dir_4 dir_1) :named axiom8))



(check-sat)
(get-unsat-core)


