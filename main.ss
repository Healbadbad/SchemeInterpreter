; Interpreter Project
; Nathan Blank
; Jeremy Wright

;:  Single-file version of the interpreter.
;; Easier to submit to server, probably harder to use in the development process

; TODOLIST
; Add set! to eval-exp
; Get Lambda working

(load "chez-init.ss") 

(define (trace-all)
  (trace top-level-eval parse-exp apply-prim-proc apply-proc eval-exp)
)

;-------------------+
;                   |
;    DATATYPES      |
;                   |
;-------------------+

; parsed expression

(define-datatype expression expression?  
  [var-exp        ; variable references
   (id symbol?)]
  [lit-exp        ; "Normal" data.  Did I leave out any types?
   (datum
    (lambda (x)
      (ormap 
       (lambda (pred) (pred x))
       (list number? vector? boolean? symbol? string? pair? null?))))]
  [app-exp        ; applications
   (rator expression?)
   (rands (list-of expression?))]  
  [lambda-exp
   (vars (list-of symbol?))
   (exps (list-of expression?))]
  [arblambda-exp
   (vars symbol?)
   (exps (list-of expression?))]
  [pair-lambda-exp
    (vars pair?)
    (exps (list-of expression?))]
  [let-exp
   (version expression?)
   (vars (list-of expression?))
   (exps (list-of expression?))]
  [set-exp
    (id expression?)
    (value expression?)]
  [if-exp
    (condition expression?)
    (if-true expression?)
    (if-false expression?)]
  [one-armed-if-exp
    (condition expression?)
    (if-true expression?)]
  [cond-exp
    (conditions (list-of expression?))
    (bodies (list-of expression?))]
  [begin-exp 
    (bodies (list-of expression?))]
  [or-exp
    (bodies (list-of expression?))]
  [case-exp
    (tocheck expression?)
    (conditions (list-of expression?))
    (bodies (list-of expression?))
  ]

  )
	
	

;; environment type definitions

(define scheme-value?
  (lambda (x) #t))

(define-datatype environment environment?
  (empty-env-record)
  (extended-env-record
   (syms (list-of symbol?))
   (vals (list-of scheme-value?))
   (env environment?)))

; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
  [prim-proc
   (name symbol?)]
  [closure 
   (params (list-of symbol?))
   (bodies (list-of expression?))
   (env environment?)]
  [arbclosure
    (id symbol?)
    (bodies (list-of expression?))
    (env environment?)]
  [pair-closure
    (ids (lambda (x) (all-symbol? x)))
    (bodies (list-of expression?))
    (env environment?)])

(define (all-symbol? x)
  (if (pair? x)
    (and (symbol? (car x))
         (all-symbol? (cdr x)))
    (symbol? x)))

	 
	

;-------------------+
;                   |
;    PARSER         |
;                   |
;-------------------+


; This is a parser for simple Scheme expressions, such as those in EOPL, 3.1 thru 3.3.

; You will want to replace this with your parser that includes more expression types, more options for these types, and error-checking.

; Procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)

(define parse-exp         
  (lambda (datum)
    (cond
     [(symbol? datum) (var-exp datum)]
     [(null? datum) (lit-exp datum)]
     [(number? datum) (lit-exp datum)]
     [(vector? datum) (lit-exp datum)]
     [(boolean? datum) (lit-exp datum)]
     [(string? datum) (lit-exp datum)]
     [(pair? datum)
      (cond
       [(eqv? (car datum) 'lambda)
          (cond [(< (length datum) 3) 
                  (if (list? (2nd datum)) 
                    (eopl:error 'parse-exp "missing body: ~s" datum)
                    (eopl:error 'parse-exp "incorrect length: ~s" datum))]
                [else (if (pair? (2nd datum))
                        (if (list? (2nd datum)) 
                          
                            (if (ormap number? (2nd datum)) 
                                (eopl:error 'parse-exp "formals must be symbols: ~s" datum)
                                (lambda-exp (2nd datum)
                                    (map parse-exp (cddr datum))))
                          (pair-lambda-exp (2nd datum) (map parse-exp (cddr datum))))
                        (if (null? (2nd datum))
                            (arblambda-exp 'x
                                    (map parse-exp (cddr datum)))
                            (arblambda-exp (2nd datum)
                                    (map parse-exp (cddr datum)))) )])]
       ;[(equal? 1st 'lambda)
       ;              (cond 
       ;                    [(and (> l 2)
       ;                          (list? (cadr datum))
       ;                          (andmap symbol? (cadr datum))
       ;                          (set? (cadr datum))) (lambda-exp (cadr datum)
       ;                                                           (map parse-exp (cddr datum)))]) ]
       [(eqv? (car datum) 'if)
          (cond [(or (< (length datum) 3) (> (length datum) 4)) 
                    (if (member 'else datum) 
                      'TODO
                      (eopl:error 'parse-exp "if expression: should have (only) test, then, and else clauses: ~s" datum))]
                [(= (length datum) 3) (apply one-armed-if-exp (map parse-exp (cdr datum)))]
                [else (apply if-exp (map parse-exp (cdr datum)))])]

       [(or (eqv? (car datum) 'let) (eqv? (car datum) 'letrec) (eqv? (car datum) 'let*) ) 
          (cond [(or (< (length datum) 3) ) 
                      (eopl:error 'parse-exp "incorrect length: ~s" datum)]
                [(not (list? (2nd datum))) (eopl:error 'parse-exp "not a proper list: ~s" datum)]
                [(not (andmap list? (2nd datum ))) (eopl:error 'parse-exp "not all proper lists: ~s" datum)]
                [(not (andmap (lambda (pair) (= (length pair) 2)) (2nd datum ))) (eopl:error 'parse-exp "not all proper lists: ~s" datum)]
                [(not (andmap (lambda (pair) (symbol? (1st pair))) (2nd datum ))) (eopl:error 'parse-exp "not all proper lists: ~s" datum)]
                [else (let-exp  (lit-exp (1st datum))
                      (map parse-exp (2nd datum))
                      (map parse-exp (cddr datum)))])]

       [(eqv? (car datum) 'set!)
          (cond [(< (length datum) 3)
                      (eopl:error 'parse-exp "missing  expression: ~s" datum)]
                [(> (length datum) 3) 
                      (eopl:error 'parse-exp "too many parts: ~s" datum)]
                [else (set-exp 
                      (parse-exp (2nd datum))
                      (parse-exp (3rd datum)))])]

       [(eqv? 'quote (car datum))
          (lit-exp (cadr datum))]
       [(eqv? 'cond (car datum))
          (cond-exp (map (lambda (x) (parse-exp (car x) )) (cdr datum)) 
                    (map (lambda (x) (parse-exp (cadr x) )) (cdr datum)) )]
       [(eqv? 'begin (car datum))
          (begin-exp (map parse-exp (cdr datum)))]
       [(eqv? 'or (car datum))
          (or-exp (map parse-exp (cdr datum)))]
       [(eqv? 'case (car datum))
          (case-exp (parse-exp (2nd datum))
                    (map (lambda (x) (lit-exp (car x))) (cddr datum))
                    (map (lambda (y) (parse-exp (cadr y))) (cddr datum)) )]
       
       [(not (list? datum)) (eopl:error 'parse-exp "is not a proper list: ~s" datum)]
       ;[(> (length datusdwam) 2) (map parse-exp datum)]
       [else (app-exp (parse-exp (1st datum))
             (map parse-exp (cdr datum)))])]
     [else (eopl:error 'parse-exp "bad expression: ~s" datum)])))


(define (unparse-exp exp)
  (cases expression exp
    [var-exp (v) v]
  [lit-exp (datum) datum]
  [app-exp (proc exps) (apply list (unparse-exp proc) (map unparse-exp exps))]  
  [lambda-exp (vars exps) (apply list 'lambda vars (map unparse-exp exps))]
  [arblambda-exp (vars exps) (apply list 'lambda (unparse-exp vars) (map unparse-exp exps))]
  [let-exp (version vars exps) (apply list (unparse-exp version) (map unparse-exp vars) (map unparse-exp exps))]
  [set-exp 'a]
  )
)





;-------------------+
;                   |
;   ENVIRONMENTS    |
;                   |
;-------------------+




; Environment definitions for CSSE 304 Scheme interpreter.  Based on EoPL section 2.3

(define empty-env
  (lambda ()
    (empty-env-record)))

(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms vals env)))

(define list-find-position
  (lambda (sym los)
    (list-index (lambda (xsym) (eqv? sym xsym)) los)))

(define list-index
  (lambda (pred ls)
    (cond
     ((null? ls) #f)
     ((pred (car ls)) 0)
     (else (let ((list-index-r (list-index pred (cdr ls))))
	     (if (number? list-index-r)
		 (+ 1 list-index-r)
		 #f))))))

(define apply-env
  (lambda (env sym succeed fail) ; succeed and fail are procedures applied if the var is or isn't found, respectively.
    (cases environment env
      (empty-env-record ()
        (fail))
      (extended-env-record (syms vals env)
	(let ((pos (list-find-position sym syms)))
      	  (if (number? pos)
	      (succeed (list-ref vals pos))
	      (apply-env env sym succeed fail)))))))








;-----------------------+
;                       |
;   SYNTAX EXPANSION    |
;                       |
;-----------------------+


(define (syntax-expand syntax)
  (cases expression syntax
    [lit-exp (datum) (lit-exp datum)]
    [var-exp (datum) (if (eqv? 'else datum) (lit-exp datum) (var-exp datum))]
    [app-exp (rator rands) (app-exp (syntax-expand rator) (map syntax-expand rands))]
    [lambda-exp (agrs bodies) (lambda-exp agrs (map syntax-expand bodies))]
    [arblambda-exp (agr bodies) (arblambda-exp agr (map syntax-expand bodies))]
    [pair-lambda-exp (agrs bodies) (pair-lambda-exp agrs (map syntax-expand bodies))]
    [if-exp (condition if-true if-false) (if-exp (syntax-expand condition) (syntax-expand if-true) (syntax-expand if-false))]
    [one-armed-if-exp (condition if-true) (one-armed-if-exp (syntax-expand condition) (syntax-expand if-true))]

    [let-exp (version vars bodies) ; TODO: add cond for version
        (app-exp (lambda-exp (map cadadr vars) (map syntax-expand bodies)) (map syntax-expand (map caaddr vars)))]
    [cond-exp (conditions bodies) (cond-exp (map syntax-expand conditions) (map syntax-expand bodies))]
    [set-exp (var val) (app-exp (var) (syntax-expand val))] ;TODO: Check null?
    [begin-exp (bodies) (app-exp (lambda-exp '() (map syntax-expand bodies)) (list (lit-exp '())))]
    [or-exp (bodies) 
      (if (null? bodies)
        (lit-exp #f)
        (if (null? (cdr bodies))
          (syntax-expand (car bodies))
          (if-exp (syntax-expand (car bodies)) (syntax-expand (car bodies)) (syntax-expand (or-exp (cdr bodies))))))]
    [case-exp (tocheck conditions bodies)
      (if (null? (cdr bodies))
        (one-armed-if-exp (if (equal? (lit-exp 'else) (car conditions))
          (lit-exp #t)
          (app-exp (var-exp (if (list? (car conditions)) 'member 'eqv?)) (list (syntax-expand tocheck) (syntax-expand (car conditions))) ) )
            (syntax-expand (car bodies)))
        (if-exp
          (app-exp (var-exp (if (list? (car conditions)) 'member 'eqv?)) (list (syntax-expand tocheck) (syntax-expand (car conditions))))
          (syntax-expand (car bodies))
          (syntax-expand (case-exp tocheck (cdr conditions) (cdr bodies)))))
      ;(if null? (cdr bodies))
      ;  (one-armed-if-exp (syntax-expand (car conditions)) (syntax-expand (car bodies)))
      ;  (if-exp (syntax-expand (car conditions)) (syntax-expand (car bodies)) (syntax-expand (case-exp (cdr conditions) (cdr bodies))))
    ]
  )
)



;-------------------+
;                   |
;   INTERPRETER     |
;                   |
;-------------------+



; top-level-eval evaluates a form in the global environment

(define top-level-eval
  (lambda (form env)  
    ; later we may add things that are not expressions.
    (eval-exp form env)))

; eval-exp is the main component of the interpreter

(define eval-exp
  (lambda (exp env)
    (cases expression exp
      [lit-exp (datum) datum]
      [lambda-exp (agrs bodies) (closure agrs bodies env)]
      [arblambda-exp (agr blah) (arbclosure agr blah env)]
      [pair-lambda-exp (args exp) (pair-closure args exp env)]
      [let-exp (version vars executes) ;Should never actually run after syntax-expand
          (let
            ([extended-env (extend-env (get-vars vars) (eval-rands (map caaddr vars) env) env)]) (eval-bodies executes extended-env))]
      [var-exp (id)
				(apply-env env id; look up its value.
      	   (lambda (x) x) ; procedure to call if id is in the environment 
           (lambda () (eopl:error 'apply-env ; procedure to call if id not in env
		          "variable not found in environment: ~s"
			   id)))]

      [if-exp (condition if-true if-false)
              (if (eval-exp condition env)
                (eval-exp if-true env)
                (eval-exp if-false env))]
      [one-armed-if-exp (condition if-true )
              (if (eval-exp condition env)
                (eval-exp if-true env))]

      [cond-exp (conditions bodies) 
        (let loop ([conditions conditions] [bodies bodies])
          (cond [(eqv? (car conditions) 'else) (eval-exp (car bodies) env)]
                [else (if (eval-exp (car conditions) env) (eval-exp (car bodies) env) (loop (cdr conditions) (cdr bodies)))])
        )]
      [app-exp (rator rands)
        (let ([proc-value (eval-exp rator env)]
              [args (eval-rands rands env)])
          (apply-proc proc-value args))]
      [else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)])))

; evaluate the list of operands, putting results into a list

(define (get-vars apps)
  (map cadadr apps)
)



;(define eval-rands
;  (lambda (rands env)
    ;(map eval-exp rands (make-list (length rands) env))))

(define eval-rands
  (lambda (rands env)
    (map (lambda (x) (eval-exp x env)) rands)))

(define (eval-bodies bodies env)
  (let loop ([bodies bodies]) 
    (if (null? (cdr bodies)) 
        (eval-exp (car bodies) env)
        (begin
          (eval-exp (car bodies) env)
          (loop (cdr bodies)))
    )
  )
)

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.
(define (get-lambda-vars apps)
  (map cadr apps)
)

(define apply-proc
  (lambda (proc-value args)
    (cases proc-val proc-value
      [prim-proc (op) (apply-prim-proc op args)]
      [closure (params bodies env) ;(display params) (display args)(display "\n\n\n")
              (let ([new-env (extend-env params args env)])
                            (eval-bodies bodies new-env))]
      [arbclosure (param bodies env)
                    (eval-bodies bodies (extend-env (list param) (list args) env))]
      [pair-closure (params bodies env)
                  (let ([new-env (extend-env
                                   (let helper ([params params])
                                     (if (pair? params)
                                       (cons (car params)
                                             (helper (cdr params)))
                                       (list params)))
                                   (let helper ([params params] [args args])
                                     (if (pair? params)
                                       (cons (car args)
                                             (helper (cdr params) (cdr args)))
                                       (list args))) env)])
                    (eval-bodies bodies new-env))]
			; You will add other cases4
      [else (eopl:error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                    proc-value)])))

(define *prim-proc-names* '(+ - * / add1 sub1 cons equal? eq? eqv? = >= > < quote list list?
 pair? vector vector? vector-ref not zero? null? car cdr caar cadr cadar length list->vector vector->list
 number? symbol? procedure? set! set-car! set-cdr! vector-set! apply map member))

(define init-env         ; for now, our initial global environment only contains 
  (extend-env            ; procedure names.  Recall that an environment associates
     *prim-proc-names*   ;  a value (not an expression) with an identifier.
     (map prim-proc      
          *prim-proc-names*)
     (empty-env)))

; Usually an interpreter must define each 
; built-in procedure individually.  We are "cheating" a little bit.

(define apply-prim-proc
  (lambda (prim-proc args)
    (case prim-proc
      [(+) (apply + args)]
      [(-)  (apply - args)];(display (list args)) (display "\n\n\n")
      [(*) (apply * args)]
      [(/) (apply / args)]
      [(add1) (+ (1st args) 1)]
      [(sub1) (- (1st args) 1)]
      [(cons) (cons (1st args) (2nd args))]
      [(=) (= (1st args) (2nd args))]
      [(eq?) (eq? (1st args) (2nd args))]
      [(eqv?) (eqv? (1st args) (2nd args))]
      [(equal?) (equal? (1st args) (2nd args))]
      [(>=) (>= (1st args) (2nd args))]
      [(>) (> (1st args) (2nd args))]
      [(<) (< (1st args) (2nd args))]
      [(quote) (1st args)]
      [(vector) (apply vector args)]
      [(list) args]
      [(list?) (list? (1st args))]
      [(pair?) (pair? (1st args))]
      ;[(if) (if (eval (1st args)) (2nd args) (3rd args))]
      [(not) (apply not args)]
      [(zero?) (eq? 0 (1st args))]
      [(null?) (apply null? args)]
      [(car) (car (1st args))]
      [(cdr) (cdr (1st args))]
      [(caar) (caar (1st args))]
      [(cadr) (cadr (1st args))]
      [(cadar) (cadar (1st args))]
      ;[(set!) (set! (1st (1st args)) (2nd (1st args)))]
      [(set-car!) (set-car! (1st args) (2nd args))] 
      [(set-cdr!) (set-cdr! (1st args) (2nd args))] 
      [(vector-set!) (vector-set! (1st args) (2nd args) (3rd args))] 
      [(display) (display (1st args))]
      [(newline) (newline (1st args))]
      [(length) (length (1st args))]
      [(list->vector) (list->vector (1st args))]
      [(vector->list) (vector->list (1st args))]
      [(vector?) (vector? (1st args))]
      [(vector-ref) (vector-ref (1st args) (2nd args))]
      [(number?) (number? (1st args))]
      [(symbol?) (symbol? (1st args))]
      [(member) (member (1st args) (2nd args))]
      [(map) (if (or (= (length args) 2) (= (length args) 3)) 
                  (let loop ([proc (1st args)] [newargs (cadr args)])
                      ;(display proc) (display "\n") (display newargs) (display (cdr newargs))(display "\n")
                      ;(map apply-proc (make-list (length newargs) proc) newargs)
                      (if (null? (cdr newargs))
                        (list (apply-proc proc newargs))
                        (cons (apply-proc proc newargs) (loop proc (cdr newargs) ))

                      )
                  )
                  (eopl:error 'apply-prim-proc 
                  "incorrect number of arguments to map: ~s" (length args))
              )]
      [(apply) (car (apply-proc (1st args) (cdr args)))]
      [(procedure?) (if (list? (1st args))
                        (or (eqv? 'closure (1st (1st args))) (eqv? 'arbclosure (1st (1st args))) (eqv? 'pair-closure (1st (1st args))) (eqv? 'prim-proc (1st (1st args))) )
                        (if (procedure? (1st args))
                          (procedure? (1st args))
                          (eqv? (1st args) 'closure)))]
      [else (error 'apply-prim-proc 
            "Bad primitive procedure name: ~s" 
            prim-proc)])))

(define rep      ; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (parse-exp (read)))])
      ;; TODO: are there answers that should display differently?
      (eopl:pretty-print answer) (newline)
      (rep))))  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
  (lambda (x) (top-level-eval (syntax-expand (parse-exp x)) init-env)))







;(eval-one-exp '
;(((lambda (f)
;   ((lambda (x) (f (lambda (y) ((x x) y))))
;    (lambda (x) (f (lambda (y) ((x x) y))))))
;   )
;   6))

;(eval-one-exp '((lambda (g)
;    (lambda (n)
;      (if (zero? n)
;          1
;          (* n (g (- n 1)))))5) (lambda (q) q)  ))