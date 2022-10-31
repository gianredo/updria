(declare-sort index 0)

;;actual state variables
(declare-fun state (index) Int)
(define-const idle Int 0)
(define-const wait Int 1)
(define-const critical Int 2)
(declare-fun token (index) Int)
(declare-const next_token Int)
(declare-const to_serve Int)

;;abstract predicates
(declare-fun x_state_idle (index) Bool)
(declare-fun x_token_equals_0 (index) Bool)
(declare-fun x_state_crit (index) Bool)
(declare-fun x_next_token_equals_1 () Bool)
(declare-fun x_to_serve_equals_1 () Bool)

;; abstracted initial formula 
(define-fun hat-initial () Bool 
 (forall ((i index)) 
            (and
                (x_state_idle i)
                (x_token_equals_0 i)
                x_next_token_equals_1
                x_to_serve_equals_1
            )

))

;; abstracted property 
(define-fun hat-prop () Bool 
 (forall ((i index) (j index))
    ( => 
        (not (= i j))
        (not (and  
            (x_state_crit i)
            (x_state_crit j)
        ))
    )
 ))

;; formula H 
(define-fun H () Bool 
 (forall ((i index))
    (and
        (iff (x_state_idle i) (= (state i) idle))
        (iff (x_state_crit i) (= (state i) critical))
        (iff (x_token_equals_0 i) (= (token i) 0))
        (iff x_next_token_equals_1 (= next_token 1))
        (iff x_to_serve_equals_1 (= to_serve 1))
    )
 ))



;;(assert (and (not hat-prop) H))
;;;; (check-sat)
;;(get-model)


;;diagram from the model
(define-fun diagram () Bool 
    (exists ((i1 index) (i2 index))
        (and 
            (not (= i1 i2))
            (not x_next_token_equals_1)
            (not x_to_serve_equals_1)
            (not (x_state_idle i1))
            (not (x_state_idle i2))
            (x_state_crit i1)
            (x_state_crit i2)
            (not (x_token_equals_0 i1))
            (not (x_token_equals_0 i2))
        )
))

;;next state variables
(declare-fun state^1 (index) Int)
(declare-fun token^1 (index) Int)
(declare-const next_token^1 Int)
(declare-const to_serve^1 Int)
;;additional variables
(declare-fun state_bar (index) Int)
(declare-fun token_bar (index) Int)
(declare-const next_token_bar Int)
(declare-const to_serve_bar Int)
;;additional variables next
(declare-fun state^1_bar (index) Int)
(declare-fun token^1_bar (index) Int)
(declare-const next_token^1_bar Int)
(declare-const to_serve^1_bar Int)
;;predicates next 
(declare-fun x_state_idle^1 (index) Bool)
(declare-fun x_token_equals_0^1 (index) Bool)
(declare-fun x_state_crit^1 (index) Bool)
(declare-fun x_next_token_equals_1^1 () Bool)
(declare-fun x_to_serve_equals_1^1 () Bool)

;; formula H_next 
(define-fun H_next () Bool 
 (forall ((i index))
    (and
        (iff (x_state_idle^1 i) (= (state^1 i) idle))
        (iff (x_state_crit^1 i) (= (state^1 i) critical))
        (iff (x_token_equals_0^1 i) (= (token^1 i) 0))
        (iff x_next_token_equals_1^1 (= next_token^1 1))
        (iff x_to_serve_equals_1^1 (= to_serve^1 1))
    )
 ))


;;transition formula with bar variables
(define-fun first-rule () Bool
    (exists ((i1 index))
        (and
            (= (state_bar i1) idle)
            (= (state^1_bar i1) wait)
            (= (token^1_bar i1) next_token_bar)
            (= next_token^1_bar  (+ next_token_bar  1))
            (= to_serve_bar  to_serve^1_bar )
            (forall ((j index))
                (=> 
                    (not (= i1 j))
                    (and 
                        (= (state^1_bar  j) (state_bar  j))
                        (= (token^1_bar  j) (token_bar  j))
                    )
                )   
            )
        )       
    )
)

(define-fun second-rule () Bool
    (exists ((i1 index))
        (and
            (= (state_bar  i1) wait)
            (= (state^1_bar  i1) critical)
            (= (token_bar  i1) to_serve_bar )
            (= (token^1_bar  i1) (token_bar  i1))
            (= next_token^1_bar  next_token_bar )
            (= to_serve_bar  to_serve^1_bar )
            (forall ((j index))
                (=> 
                    (not (= i1 j))
                    (and 
                        (= (state^1_bar  j) (state_bar  j))
                        (= (token^1_bar  j) (token_bar  j))
                    )
                )   
            )
        )       
    )
)

(define-fun third-rule () Bool
    (exists ((i1 index))
        (and
            (= (state_bar  i1) critical)
            (= (state^1_bar  i1) idle)
            (= (token^1_bar  i1) 0)
            (= next_token^1_bar  next_token_bar )
            (= to_serve^1_bar  (+ to_serve_bar  1))
            (forall ((j index))
                (=> 
                    (not (= i1 j))
                    (and 
                        (= (state^1_bar  j) (state_bar  j))
                        (= (token^1_bar  j) (token_bar  j))
                    )
                )   
            )
        )       
    )
)

(define-fun trans () Bool
    (or first-rule second-rule third-rule)
 )

;;EQ formula

(define-fun EQ () Bool
    (forall ((i index))
     (and
        (iff (= (state i) idle) (= (state_bar i) idle))
        (iff (= (state i) critical) (= (state_bar i) critical))  
        (iff (= (token i) 0) (= (token_bar i) 0))
        (iff (= next_token 1) (= next_token_bar 1))
        (iff (= to_serve 1) (= to_serve_bar 1)) 
        (iff (= (state^1 i) idle) (= (state^1_bar i) idle))
        (iff (= (state^1 i) critical) (= (state^1_bar i) critical))  
        (iff (= (token^1 i) 0) (= (token^1_bar i) 0))
        (iff (= next_token^1 1) (= next_token^1_bar 1))
        (iff (= to_serve^1 1) (= to_serve^1_bar 1))
)))

;; diagram next
;;diagram from the model
(define-fun diagram_next () Bool 
    (exists ((i1 index) (i2 index))
        (and 
            (not (= i1 i2))
            (not x_next_token_equals_1^1)
            (not x_to_serve_equals_1^1)
            (not (x_state_idle^1 i1))
            (not (x_state_idle^1 i2))
            (x_state_crit^1 i1)
            (x_state_crit^1 i2)
            (not (x_token_equals_0^1 i1))
            (not (x_token_equals_0^1 i2))
        )
))


;; try to generalize diagram 
(define-fun diagram_weaken () Bool 
    (exists ((i1 index) (i2 index))
        (and 
            (not (= i1 i2))
            (x_state_crit i1)
            (x_state_crit i2)
        )
))

(define-fun diagram_next_weaken () Bool 
    (exists ((i1 index) (i2 index))
        (and 
            (not (= i1 i2))
            (x_state_crit^1 i1)
            (x_state_crit^1 i2)
        )
))


;;also this generalisation is ok, maybe better

;; F_0 = I_hat, F_1 = not(diagram_weaker) 
;; no more models
;; no inductive inv

;; F_0 = I_hat, F_1 = not(diagram_weaker), F_2 = True
;; check if F_2 & H & not(bad) is sat

(push 1) 
    (assert (and H (not hat-prop)))
    ;;(check-sat)
    ;;(get-model)
(pop 1)

;;always same model

;;RecBloc(diagram, 2)
(push 1)
    (assert (and (not diagram) H H_next EQ trans diagram_next))
    (check-sat)
    ;;(get-model)
(pop 1)


;; new diagram 
 (define-fun diagram_2 () Bool 
    (exists ((i0 index) (i1 index))
        (and 
            (not (= i0 i1))
            (not (x_state_crit i0))
            (not (x_state_idle i0))
            (not (x_token_equals_0 i0))
            ;;(not x_next_token_equals_1)
            ;;(not x_to_serve_equals_1)        
        )
    )
 )

  (define-fun diagram_2_next () Bool 
    (exists ((i0 index) (i1 index))
        (and 
            (not (= i0 i1))
            (not (x_state_crit^1 i0))
            (not (x_state_idle^1 i0))
            (not (x_token_equals_0^1 i0))
            ;;(not x_next_token_equals_1^1)
            ;;(not x_to_serve_equals_1^1)        
        )
    )
 )


;; RecBloc(diagram_2, 1)
;; F_1 = not(diagram_weaker), F_2 = True

(push 1)
    (assert (and hat-initial (not diagram_2) H H_next trans EQ diagram_2_next))
    (check-sat)
    (get-model)
(pop 1)

;;abstract counterexample. 
;;init diagram
