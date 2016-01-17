(define (cadr  l) (car (cdr l)))
(define (cddr  l) (cdr (cdr l)))
(define (caadr l) (car (car (cdr l))))
(define (caddr l) (car (cdr (cdr l))))
(define (cdddr l) (cdr (cdr (cdr l))))
(define (cdadr l) (cdr (car (cdr l))))
(define (cadddr l) (car (cdddr l)))
(define false #f)
(define true  #t)
(define (not exp) (if exp #f #t))
(define (true? exp) (not (false? exp)))
(define (false? exp) (eq? exp false))
(define (boolean? exp) (or (true? exp) (false? exp)))

(define (time action)
  (let ((start (current-time-millis))
        (tmp   (eval action the-global-environment))
        (end   (current-time-millis)))
    (- end start)))


;; FUNCTIONS

;; map
(define (map proc items)
  (if (null? items)
    '()
    (cons (proc (car items))
          (map proc (cdr items)))))

;; length
(define (length items)
  (if (null? items)
    0
    (+ 1 (length (cdr items)))))

;; IO
(define (newline) (display "\n"))


;;

;; numbers and strings are self-evaluating
(define (self-evaluating? exp)
  (cond ((integer? exp) true) ;; SICP: number?
        ((string? exp) true)
        (else false)))

;; variables are defined as symbols
(define (variable? exp) (symbol? exp))

;; tagged-list identifies if a given list `exp` starts with `tag`
(define (tagged-list? exp tag)
  (if (pair? exp)
    (eq? (car exp) tag)
    false))

;; quoted? checks if a given list `exp` starts with `quote
(define (quoted? exp) (tagged-list? exp 'quote))

;; given a quoted `exp`, get its text.
;; example:
;; given  '(quote x)
;; return x
(define (text-of-quotation exp) (cadr exp))

;; OPERATION ON ENVIRONMENTS

;; the-empty-environment
(define the-empty-environment '())

;; extend-environment returns a new environment, consisting of a new frame
;; in which the symbols in the list `vars` are bound to the
;; corresponding elements in the list `vals`, where the enclosing
;; environment is the environment `base-env`
(define (extend-environment vars vals base-env)
  (if (= (length vars) (length vals))
    (cons (make-frame vars vals) base-env)
    (if (< (length vars) (length vals))
      (error "Too many arguments supplied" vars vals)
      (error "Too few arguments supplied" vars vals))))

(define (enclosing-environment env) (cdr env))

;; setup-environment creates a default environment
(define (setup-environment)
  ;; add more primitive procedures here
  (define primitive-procedures
    (list (list 'car car)
          (list 'cdr cdr)
          (list 'cons cons)
          (list 'null? null?)
          (list '+ +)
          (list 'time time)
          (list '= =)
          (list 'load load)
          ))
  (define (primitive-procedure-names)
    (map car primitive-procedures))
  (define (primitive-procedure-objects)
    (map (lambda (proc) (list 'primitive (cadr proc)))
         primitive-procedures))
  ;; end of local definitions
  ;;
  ;; setup-environment body
  (let ((initial-env (extend-environment (primitive-procedure-names)
                                         (primitive-procedure-objects)
                                         the-empty-environment)))
    (define-variable! 'true true initial-env)
    (define-variable! 'false false initial-env)
    initial-env))

;; to get the frame from an environment, use `first-frame`
(define (first-frame env) (car env))

;; a frame is simply a cons of `vars` and `vals`
(define (make-frame vars vals) (cons vars vals))
(define (frame-variables frame) (car frame))
(define (frame-values frame) (cdr frame))

;; to add a new binding to a frame, we prepend to the frame
;; variables the `var` and to the frame values the `val`
(define (add-binding-to-frame! var val frame)
  (set-car! frame (cons var (car frame)))
  (set-cdr! frame (cons val (cdr frame)))
  )

;; lookup-variable-value returns the value that is bound to the symbol `var`
;; in the environment `env`, or signals an error if the variable is unbound.
(define (lookup-variable-value var env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond
        ((null? vars) (env-loop (enclosing-environment env)))
        ((eq? var (car vars)) (car vals))
        (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
      (error "Unbound variable -- LOOKUP" var)
      (let ((frame (first-frame env)))
        (scan (frame-variables frame)
              (frame-values frame)))))
  (env-loop env))

;; set-variable-value! updates the value of `var` to `val` in a
;; given environment `env`
(define (set-variable-value! var val env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond
        ((null? vars) (env-loop (enclosing-environment env)))
        ((eq? var (car vars)) (set-car! vals val))
        (else
          (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
      (error "Unbound variable -- SET!" var)
      (let ((frame (first-frame env)))
        (scan (frame-variables frame)
              (frame-values frame)))))
  (env-loop env))

;; ASSIGNMENT FORM
;;
;; Assignments have the form
;;
;; (set! <var> <value>)
;;
(define (assignment? exp) (tagged-list? exp 'set!))
(define (assignment-variable exp) (cadr exp))
(define (assignment-value exp) (caddr exp))

(define (eval-assignment exp env)
  (set-variable-value! (assignment-variable exp)
                       (eval (assignment-value exp) env)
                       env)
  'ok)

;; DEFINITION FORM
;;
;; Definitions have the form
;;
;; (define <var> <value>)
;;
;; or the form
;;
;; (define (<var> <parameter1> ... <parameterN>) <body>)
;;
;; The later form is syntactic sugar for:
;;
;; (define <var>
;;   (lambda (<parameter1> ... <parameterN>)
;;     <body>))


;; An expression is a definition if it is tagged by `define
(define (definition? exp) (tagged-list? exp 'define))

;; definition-variable returns the variable of the definition for
;; either definition form
(define (definition-variable exp)
  (if (symbol? (cadr exp))
    (cadr exp)
    (caadr exp)))

(define (definition-value exp)
  (if (symbol? (cadr exp))
    (caddr exp)
    (make-lambda (cdadr exp)    ;; formal params
                 (cddr  exp)))) ;; body

;; a variable definition adds to the first frame in the environment `env`
;; a new binding that associates tbe variable `var` witb the value `val`
(define (define-variable! var val env)
  (let ((frame (first-frame env)))
    (define (scan vars vals)
      (cond
        ;; if the variable does not exist, then add it
        ((null? vars) (add-binding-to-frame! var val frame))
        ((eq? var (car vars)) (set-car! vals val))
        (else (scan (cdr vars) (cdr vals)))))
    (scan (frame-variables frame) (frame-values frame)))
  )

(define (eval-definition exp env)
  (define-variable! (definition-variable exp)
                    (eval (definition-value exp) env)
                    env)
  'ok)


;; LAMBDA
;;
;; lambda expressions are lists that begin with the symbol 'lambda
;; followed by the formal parameters and the lambda body
;;
;; e.g '(lambda (<param1> ... <paramN>) <body>)
;;
(define (lambda? exp) (tagged-list? exp 'lambda))
(define (lambda-parameters exp) (cadr exp))
(define (lambda-body exp) (cddr exp))

(define (make-lambda parameters body)
  (cons 'lambda (cons parameters body)))

;; IF
;;
;; The IF is of the following form
;;
;; (if <pred> <consequent> <alternative>)
;;
;; The <alternative> is optional
;;
(define (if? exp) (tagged-list? exp 'if))
(define (make-if predicate consequent alternative)
  (list 'if predicate consequent alternative))

;; eval-if evaluates an if expression, by firstly evaluating the
;; predicate, and then, if the predicate is true, the consequent, else
;; the alternative
(define (eval-if exp env)
  (define (if-predicate exp) (cadr exp))
  (define (if-consequent exp) (caddr exp))
  (define (if-alternative exp)
    (if (not (null? (cdddr exp)))
      (cadddr exp)
      false))
  (if (true? (eval (if-predicate exp) env))
    (eval (if-consequent exp) env)
    (eval (if-alternative exp) env)))

;; PROCEDURES
;;
;; Compound procedures are constructed from parameters, procedure bodies and
;; environments.
;;
(define (primitive-procedure? proc) (tagged-list? proc 'primitive))
(define (primitive-implementation proc) (cadr proc))

(define (make-procedure parameters body env)
  (list 'procedure parameters body env))

(define (compound-procedure? p) (tagged-list? p 'procedure))

(define (procedure-parameters p) (cadr p))
(define (procedure-body p) (caddr p))
(define (procedure-environment p) (cadddr p))

(define apply-in-underlying-scheme apply) ;; this is the underlying's scheme apply

(define (apply-primitive-procedure proc args)
  (apply-in-underlying-scheme
    (primitive-implementation proc) args))


;; BEGIN
;;
;; begin packages a sequence of expressions into a single expression.
;;
(define (begin? exp) (tagged-list? exp 'begin))
(define (begin-actions exp) (cdr exp))
(define (make-begin seq) (cons 'begin seq))

;; SEQUENCES
;;
;;
;;
(define (last-exp? seq) (null? (cdr seq)))
(define (first-exp seq) (car seq))
(define (rest-exps seq) (cdr seq))

;; eval-sequence is used by apply & eval to evaluate the sequence of
;; expressions in a procedure body or a begin form.
(define (eval-sequence exps env)
  (cond ((last-exp? exps) (eval (first-exp exps) env))
        (else (eval (first-exp exps) env)
              (eval-sequence (rest-exps exps) env))))

(define (sequence->exp seq)
  (cond ((null? seq) seq)
        ((last-exp? seq) (first-exp seq))
        (else (make-begin seq))))

;; COND
;;
;; cond is a derived expression, which means that it can be defined in terms
;; of another form (if).
;;
(define (cond? exp) (tagged-list? exp 'cond))
(define (cond-clauses exp) (cdr exp))
(define (cond-else-clause? clause) (eq? (cond-predicate clause) 'else))
(define (cond-predicate clause) (car clause))
(define (cond-actions clause) (cdr clause))
(define (cond->if exp)
  (expand-clauses (cond-clauses exp)))

(define (expand-clauses clauses)
  (if (null? clauses)
    'false
    (let ((first (car clauses))
          (rest  (cdr clauses)))
      (if (cond-else-clause? first)
        (if (null? rest)
          (sequence->exp (cond-actions first))
          (error "ELSE clause isn't last -- COND->IF" clauses))
        (make-if (cond-predicate first)
                 (sequence->exp (cond-actions first))
                 (expand-clauses rest))))))

;; APPLY
;;
;; apply takes two arguments, a procedure and a list of arguments. For primitive
;; procedures, it calls apply-primitive-procedure. For compound procedures
;; it evaluates sequentially the expressions that make up the body of the procedure.
;; The environment for the evaluation of the body of a compound procedure is
;; constructed by extending the base environment carried by the procedure to include
;; a frame that binds the parameters of the procedure to the arguments to which
;; the procedure is to be applied.
;;
(define (apply procedure arguments)
  (cond ((primitive-procedure? procedure)
         (apply-primitive-procedure procedure arguments))
        ((compound-procedure? procedure)
         (eval-sequence
           (procedure-body procedure)
           (extend-environment
             (procedure-parameters procedure)
             arguments
             (procedure-environment procedure))))
        (else
          (error "Unknown procedure type -- APPLY" procedure))))

(define (application? exp) (pair? exp))
(define (operator exp) (car exp))
(define (operands exp) (cdr exp))
(define (no-operands? ops) (null? ops))
(define (first-operand ops) (car ops))
(define (rest-operands ops) (cdr ops))


(define (list-of-values exps env)
  (if (no-operands? exps)
    '()
    (cons (eval (first-operand exps) env)
          (list-of-values (rest-operands exps) env))))

;; EVAL

;; Eval takes as input an expression and an environment. It classifies the
;; expression directs its evaluation. Each type of expression has a
;; predicate that tests for it, and an abstract means for selecting its
;; parts.
(define (eval exp env)
  (cond
    ;; for self-evaluating expressions, such as numbers, `eval`
    ;; returns the expression itself.
    ((self-evaluating? exp) exp)
    ;; variables must be looked up in the environment to find their values
    ((variable? exp) (lookup-variable-value exp env))
    ;; for quoted expressions, `eval` returns the expression that was quoted
    ((quoted? exp) (text-of-quotation exp))
    ;; an assignment to a variable must recursively call `eval` to evaluate
    ;; the new value and change the binding accordingly.
    ((assignment? exp) (eval-assignment exp env))
    ;; the definition of a variable must recursively call `eval` to evaluate
    ;; the value of the variable. The environment `env` must also be
    ;; modified since a new variable will be created
    ((definition? exp) (eval-definition exp env))
    ;; an IF expression requires special preocessing of its parts, so as
    ;; to evaluate the consequent if the predicate is true, and otherwise,
    ;; to evaluate the alternative
    ((if? exp) (eval-if exp env))
    ;; a lambda expression must be transformed into an applicable procedure
    ;; by packaging together the parameters and body specified by the
    ;; lambda expression with the environment of the evaluation
    ((lambda? exp) (make-procedure (lambda-parameters exp)
                                   (lambda-body exp)
                                   env))
    ;; begin requires the evaoluation of its sequence in the order that
    ;; they appear
    ((begin? exp) (eval-sequence (begin-actions exp) env))
    ;; cond performs case analysis and transforms its arguments into an if
    ;; form.
    ((cond? exp) (eval (cond->if exp) env))
    ;; for a procedure application, eval must recursively evaluate the operator
    ;; and the operands. The resulting procedure and operand values are passed
    ;; to apply, which performs the actual evaluation.
    ((application? exp)
     (apply (eval (operator exp) env)
            (list-of-values (operands exp) env)))
    (else
      (error "Unknown expression type -- EVAL" exp)))
  )

;; REPL
;;
;; run the evaluator as a program
;;

;; the-global-environment
(define the-global-environment (setup-environment))

(define input-prompt "kat$ ")
(define output-prompt "> ")

;; driver-loop
;;
;; The metacircular evaluator is kickstarted by this procedure.
;;
(define (driver-loop)
  (define (prompt-for-input string)
    (newline) (display string))
  (define (announce-output string)
    (display string))
  ;; user-print avoids printing the environment part of a compound proc
  (define (user-print object)
    (if (compound-procedure? object)
      (display (list 'compound-procedure
                     (procedure-parameters object)
                     (procedure-body object)
                     '<procedure-env>))
      (display object)))
  ;; driver-loop body
  (prompt-for-input input-prompt)
  (let ((input (read)))
    (let ((output (eval input the-global-environment)))
      (announce-output output-prompt)
      (user-print output)))
  (driver-loop))


(define logo
"
  ____  __.  ________________               .__
  |    |/ _| /  _  \\__    ___/   ______ ____ |  |__   ____   _____   ____
  |      <  /  /_\\  \\|    |     /  ___// ___\\|  |  \\_/ __ \\ /     \\_/ __ \\
  |    |  \\/    |    \\    |     \\___ \\\\  \\___|   Y  \\  ___/|  Y Y  \\  ___/
  |____|__ \\____|__  /____|    /____  >\\___  >___|  /\\___  >__|_|  /\\___  >
          \\/       \\/               \\/     \\/     \\/     \\/      \\/     \\/

Welcome to Kat Scheme v0.1 (10-01-2016) <https://bitbucket.org/jfourkiotis/kat>
")


(display logo)
(driver-loop)

'metacircular-loaded
