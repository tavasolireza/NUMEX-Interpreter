;; PL Project - Fall 2018
;; NUMEX interpreter

#lang racket
(provide (all-defined-out)) ;; so we can put tests in a second file

;; definition of structures for NUMEX programs

;; CHANGE add the missing ones

(struct var  (string) #:transparent)  ;; a variable, e.g., (var "foo")
(struct num  (int)    #:transparent)  ;; a constant number, e.g., (num 17)
(struct plus  (e1 e2)  #:transparent)  ;; add two expressions
(struct bool (b)      #:transparent)
(struct minus (e1 e2)  #:transparent)
(struct mult (e1 e2)  #:transparent)
(struct div (e1 e2)  #:transparent)
(struct neg  (e1)     #:transparent)
(struct andalso (e1 e2)  #:transparent)
(struct orelse (e1 e2)  #:transparent)
(struct cnd (e1 e2 e3) #:transparent)
(struct iseq (e1 e2) #:transparent)
(struct ifnzero (e1 e2 e3) #:transparent)
(struct ifleq (e1 e2 e3 e4) #:transparent)
(struct with (s e1 e2)  #:transparent)
(struct apair (e1 e2)   #:transparent)
(struct 1st (e1)      #:transparent)
(struct 2nd (e1)     #:transparent)
;(struct munit   ()      #:transparent)
;(struct ismunit (e1)     #:transparent)
;(struct closure (env lam) #:transparent)
;(struct letrec (s1 e1 s2 e2 e3)   #:transparent)
;(struct key (s e)   #:transparent)
;(struct record (k m)   #:transparent)
;(struct record (k r)   #:transparent)
;(struct value (s r)   #:transparent)




(struct lam  (nameopt formal body) #:transparent) ;; a recursive(?) 1-argument function
(struct apply (funexp actual)       #:transparent) ;; function application


(struct munit   ()      #:transparent) ;; unit value -- good for ending a list
(struct ismunit (e)     #:transparent) ;; if e1 is unit then true else false

;; a closure is not in "source" programs; it is what functions evaluate to
(struct closure (env f) #:transparent) 


(struct key  (s e) #:transparent) ;; key holds corresponding value of s which is e
(struct record (k r) #:transparent) ;; record holds several keys
(struct value (s r) #:transparent) ;; value returns corresponding value of s in r

(struct letrec (s1 e1 s2 e2 e3) #:transparent) ;; a letrec expression for recursive definitions

;; Problem 1

(define (racketlist->numexlist xs) (cond
                                     [(null? xs) (munit)]
                                     [#t (apair (car xs) (racketlist->numexlist (cdr xs)))]))

(define (numexlist->racketlist xs) (cond
                                     [(munit? xs) '()]
                                     [#t (cons (apair-e1 xs) (numexlist->racketlist (apair-e2 xs)))]))

;; Problem 2

;; lookup a variable in an environment
;; Complete this function
(define (envlookup env str)
  (cond [(null? env) (error "unbound variable during evaluation" str)]
  	[(equal? (car (car env)) str) (cdr (car env))]
        [#t (envlookup (cdr env) str)] 
		)
 )

;; Complete more cases for other kinds of NUMEX expressions.
;; We will test eval-under-env by calling it directly even though
;; "in real life" it would be a helper function of eval-exp.
(define (eval-under-env e env)
  (cond [(var? e) 
         (envlookup env (var-string e))]
        [(plus? e) 
         (let ([v1 (eval-under-env (plus-e1 e) env)]
               [v2 (eval-under-env (plus-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (+ (num-int v1) 
                       (num-int v2)))
               (error "NUMEX addition applied to non-number")))]
        [(num? e)
         (cond
           [(integer? (num-int e)) e]
           [#t ((error (format "what??: ~v" e)))])]

        [(bool? e)
         (cond
           [(boolean? (bool-b e)) e]
           [#t (error "Not a boolean")])]

        [(neg? e)
         (let ([v1 (eval-under-env (neg-e1 e) env)])
           (cond [(num? v1)
               (num (- (num-int v1)))]
               [(equal? v1 (bool #t)) (bool #f)]
               [(equal? v1 (bool #f)) (bool #t)]
               [(equal? v1 (munit)) (error "Not a valid input for neg")]
               ))]

        [(mult? e)
         (let ([v1 (eval-under-env (mult-e1 e) env)]
               [v2 (eval-under-env (mult-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (* (num-int v1)
                       (num-int v2)))
               (error "NUMEX multiplication applied to non-number")))]

        [(div? e)
         (let ([v1 (eval-under-env (div-e1 e) env)]
               [v2 (eval-under-env (div-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (quotient (num-int v1)
                       (num-int v2)))
               (error "NUMEX division applied to non-number")))]

        [(minus? e)
         (let ([v1 (eval-under-env (minus-e1 e) env)]
               [v2 (eval-under-env (minus-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (- (num-int v1)
                       (num-int v2)))
               (error "NUMEX subtraction applied to non-number")))
         ]


        [(apair? e)
         (let([v1 (eval-under-env (apair-e1 e) env)]
              [v2 (eval-under-env (apair-e2 e) env)])
           (apair v1 v2))
         ]
        
        [(1st? e)
         (let ([v1 (eval-under-env (1st-e1 e) env)])
           (cond
             [(apair? v1) (apair-e1 v1)]
             [#t (error "It's not a pair to have 1st element")]))
         ]

        [(2nd? e)
         (let ([v1 (eval-under-env (2nd-e1 e) env)])
           (cond
             [(apair? v1) (apair-e2 v1)]
             [#t (error "It's not a pair to have 2nd element")]))]

        [(ifnzero? e)
         (let ([v1 (eval-under-env (ifnzero-e1 e) env)])
                   (cond
                     [(num? v1) (cond [(not(equal? (num-int v1) 0)) (eval-under-env (ifnzero-e2 e) env)]
                                      [true (eval-under-env (ifnzero-e3 e) env)])]
                     [#t (error "Cannot evaluate expression")]))
         ]

        [(iseq? e)
         (let ([v1 [eval-under-env (iseq-e1 e) env]]
               [v2 [eval-under-env (iseq-e2 e) env]])
           (cond
             ([and (num? v1) (num? v2)]
              [cond
                ((equal? (num-int v1) (num-int v2)) (bool #t))
                (#t (bool #f))])
             ([and (bool? v1) (bool? v2)]
              [cond
                ((equal? (bool-b v1) (bool-b v2)) (bool #t))
                (#t (bool #f))])
             ([or (and (num? v1) (bool? v2)) (and (bool? v1) (num? v2))]
              [bool #f])
             (#t (error "Invalid equality check input"))))
         ]

        [(ifleq? e)
         (let ([v1 (eval-under-env (ifleq-e1 e) env)]
               [v2 (eval-under-env (ifleq-e2 e) env)])
           (cond
             [(> (num-int v1) (num-int v2)) (eval-under-env (ifleq-e4 e) env)]
             [true (eval-under-env (ifleq-e3 e) env)]))
         ]

        [(andalso? e)
         (let ([v1 [eval-under-env (andalso-e1 e) env]])
           (cond
             ([equal? (bool-b v1) #f]
              [bool #f])
             (#t (let ([v2 [eval-under-env (andalso-e2 e) env]])
                   (cond ([equal? (bool-b v2) #f]
                          [bool #f])
                         (#t [bool #t])
                     )
                   ))
             ))
         ]
        

        [(orelse? e)
         (let ([v1 [eval-under-env (orelse-e1 e) env]])
           (cond
             ([equal? (bool-b v1) #t]
              [bool #t])
             (#t (let ([v2 [eval-under-env (orelse-e2 e) env]])
                   (cond ([equal? (bool-b v2) #f]
                          [bool #f])
                         (#t [bool #t])
                     )
                   ))
             ))
         ]

        [(cnd? e)
         (let ([v1 (eval-under-env (cnd-e1 e) env)])
           (cond
             [(bool? v1) (cond [(equal? (bool-b v1) #t) (eval-under-env (cnd-e2 e) env)]
                              [#t (eval-under-env (cnd-e3 e) env)])]
             [#t (error "Cannot evaluate expression")]))
         ]
        
        [(closure? e) e]
        
        [(lam? e)
         (closure env e)]

        ;I didn't write this all by myself, I got help
        [(apply? e)
         (let ([funClosure (eval-under-env (apply-funexp e) env)])
           (cond
             [(closure? funClosure) (let ([functionDeclaration (closure-f funClosure)])
                                      (let ([evaluatedActual (eval-under-env (apply-actual e) env)])
                                        (eval-under-env-c (lam-body functionDeclaration) (cons (cons (lam-formal functionDeclaration) evaluatedActual)                                                                                  
                                                                                               (cons (cons (lam-nameopt functionDeclaration) funClosure) (closure-env funClosure))))))]
             [#t (error "It's not a closure")]))] 
        
        ;I didn't write this all by myself, I got help
        [(with? e)
         (define wFunc (with-s e))
         (let ([v1 (eval-under-env (with-e1 e) env)])
           (eval-under-env (with-e2 e) (cons (cons wFunc v1) env)))]

        [(ismunit? e)
         (let ([v1 (eval-under-env (ismunit-e e) env)])
           (cond
             [(munit? v1) (bool #t)]
             [#t (bool #f)]))
         ]

        [(munit? e)
           (munit)]

        [(key? e)
         (cond [(string? (key-s e))
             (let ([v (eval-under-env (key-e e) env)])
               (key (key-s e) v)
               )]
             [#t (error "Incorrect Input")]
             )
         ]

        [(record? e)
         (let
             ([v1 (eval-under-env (record-k e) env)]
              [v2 (eval-under-env (record-r e) env)]
              )
           (cond [(key? v1)
               (cond
                 [(or (munit? v2) (record? v2)) e]
                 [#t (error "r is not munit")]
                 )]
               [#t (error "k is not key")]
               ))
         ]

        [(value? e)
         (cond [(and (string? (value-s e)) (record? (value-r e)))
             (let ([v (eval-under-env (value-r e) env)])
               (value (value-s e) v)
               )]
             [#t (error "Incorrect Input")]
             )
         ]
        
        ;; CHANGE add more cases here
        [#t (error (format "bad NUMEX expression: ~v" e))]))

;; Do NOT change
(define (eval-exp e)
  (eval-under-env e null))
        
;; Problem 3

(define (ifmunit e1 e2 e3)
  (cond [(equal? (bool #t) (ismunit e1)) e2]
        [#t e3]
        ))

;I got help
(define (with* bs e2)
  (if (not (null? (car bs)))
      (if (null? (cdr bs))
          (with (car (car bs)) (cdr (car bs)) e2)
          (with (car (car bs)) (cdr (car bs)) (with* (cdr bs) e2)))
      (e2)))

(define (ifneq e1 e2 e3 e4)
  (cond [(not((equal? (iseq e1 e2) (bool #t)))) e3]
        [#t e4]
        ))

;; Problem 4

(define numex-filter "CHANGE")

(define numex-all-gt
  (with "filter" numex-filter
        "CHANGE (notice filter is now in NUMEX scope)"))

;; Challenge Problem

(struct fun-challenge (nameopt formal body freevars) #:transparent) ;; a recursive(?) 1-argument function

;; We will test this function directly, so it must do
;; as described in the assignment
(define (compute-free-vars e) "CHANGE")

;; Do NOT share code with eval-under-env because that will make grading
;; more difficult, so copy most of your interpreter here and make minor changes
(define (eval-under-env-c e env) "CHANGE")

;; Do NOT change this
(define (eval-exp-c e)
  (eval-under-env-c (compute-free-vars e) null))
