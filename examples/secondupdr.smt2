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

;; so F_0 = initial-hat
;; F_1 = true

;; F_1 and H and not(phi)
(assert (and true (not hat-prop) H))
(check-sat)
(get-model)


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
