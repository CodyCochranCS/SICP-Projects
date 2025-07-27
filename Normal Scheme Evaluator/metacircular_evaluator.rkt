#lang racket


;; underlying tag structure used throughout
(define (tagged-list? exp tag)
  (if (pair? exp)
      (eq? (car exp) tag)
      #f))

(define (true? x)
  (not (eq? x #f)))
(define (false? x)
  (eq? x #f))

;; used in eval
(define (self-evaluating? exp)
  (cond ((number? exp) #t)
        ((string? exp) #t)
        (else #f)))

(define (variable? exp) (symbol? exp))

(define (quoted? exp)
  (tagged-list? exp 'quote))
(define (text-of-quotation exp) (cadr exp))

(define (assignment? exp)
  (tagged-list? exp 'set!))
(define (assignment-variable exp) (cadr exp))
(define (assignment-value exp) (caddr exp))

(define (definition? exp)
  (tagged-list? exp 'define))

(define (make-lambda parameters body)
  (cons 'lambda (cons parameters body)))
(define (definition-variable exp)
  (if (symbol? (cadr exp))
      (cadr exp)
      (caadr exp)))
(define (definition-value exp)
  (if (symbol? (cadr exp))
      (caddr exp)
      (make-lambda (cdadr exp)   ; formal parameters
                   (cddr exp)))) ; body

(define (lambda? exp) (tagged-list? exp 'lambda))
(define (lambda-parameters exp) (cadr exp))
(define (lambda-body exp) (cddr exp))


(define (let? exp) (tagged-list? exp 'let))
(define (let-bindings exp) (cadr exp))
(define (let-body exp) (cddr exp))
(define (let->combination exp)
  (let loop ((params '())
             (vals '())
             (bindings (let-bindings exp)))
    (if (null? bindings)
        (cons (make-lambda params (let-body exp))
              vals)
        (let ((first (car bindings))
              (rest  (cdr bindings)))
          (loop (cons (car first) params)
                (cons (cadr first) vals)
                rest)))))

(define (let*? exp) (tagged-list? exp 'let*))
(define (let*-bindings exp) (cadr exp))
(define (let*-body exp) (cddr exp))
(define (let*->nested-lets exp)
  (let ((bindings (let*-bindings exp)))
    (if (null? bindings)
        (cons 'let (cons '() (let*-body exp)))
        (let recurse ((first-binding (car bindings))
                      (rest-bindings (cdr bindings)))
          (if (null? rest-bindings)
              (cons 'let (cons (list first-binding) (let*-body exp)))
              (list 'let
                    (list first-binding)
                    (recurse (car rest-bindings) (cdr rest-bindings))))))))


(define (if? exp) (tagged-list? exp 'if))
(define (if-predicate exp) (cadr exp))
(define (if-consequent exp) (caddr exp))
(define (if-alternative exp)
  (if (not (null? (cdddr exp)))
      (cadddr exp)
      'false))

(define (make-if predicate consequent alternative)
  (list 'if predicate consequent alternative))

(define (begin? exp) (tagged-list? exp 'begin))
(define (begin-actions exp) (cdr exp))
(define (last-exp? seq) (null? (cdr seq)))
(define (first-exp seq) (car seq))
(define (rest-exps seq) (cdr seq))

(define (make-begin seq) (cons 'begin seq))
(define (sequence->exp seq)
  (cond ((null? seq) seq)
        ((last-exp? seq) (first-exp seq))
        (else (make-begin seq))))


(define (application? exp) (pair? exp))
(define (operator exp) (car exp))
(define (operands exp) (cdr exp))

; Modified for exercise 4.2
; (define (application? exp) (tagged-list? exp 'call))
; (define (operator exp) (cadr exp))
; (define (operands exp) (cddr exp))




(define (no-operands? ops) (null? ops))
(define (first-operand ops) (car ops))
(define (rest-operands ops) (cdr ops))


(define (cond? exp) (tagged-list? exp 'cond))
(define (cond-clauses exp) (cdr exp))
(define (cond-arrow-clause? clause)
  (tagged-list? (cond-actions clause) '=>))
(define (cond-else-clause? clause)
  (eq? (cond-predicate clause) 'else))
(define (cond-predicate clause) (car clause))
(define (cond-actions clause) (cdr clause))

(define (expand-clauses clauses)
  (if (null? clauses)
      'false                          ; no else clause
      (let ((first (car clauses))
            (rest (cdr clauses)))
        (cond ((cond-else-clause? first)
               (if (null? rest)
                   (sequence->exp (cond-actions first))
                   (error "ELSE clause isn't last -- COND->IF"
                          clauses)))
              ((cond-arrow-clause? first)
               (list 'let
                     (list (list 'temp (cond-predicate first)))
                     (make-if 'temp
                              (list (cadr (cond-actions first)) 'temp)
                              (expand-clauses rest))))
              (else (make-if (cond-predicate first)
                             (sequence->exp (cond-actions first))
                             (expand-clauses rest)))))))

(define (cond->if exp)
  (expand-clauses (cond-clauses exp)))


(define (make-procedure parameters body env)
  (list 'procedure parameters body env))

(define (compound-procedure? p)
  (tagged-list? p 'procedure))
(define (procedure-parameters p) (cadr p))
(define (procedure-body p) (caddr p))
(define (procedure-environment p) (cadddr p))


(define (primitive-procedure? proc)
  (tagged-list? proc 'primitive))
(define (primitive-implementation proc) (cadr proc))

;; environment
;; frame uses mutable pairs due to set-mcar! and set-mcdr! used in add-binding-to-frame!

(define (enclosing-environment env) (cdr env))
(define (first-frame env) (car env))
(define the-empty-environment '())

;(define (make-frame variables values)
  ;(mcons variables values))
;(define (frame-variables frame) (mcar frame))
;(define (frame-values frame) (mcdr frame))

(define (make-frame variables values)
  (make-hash (map cons variables values)))

;(define (add-binding-to-frame! var val frame)
  ;(set-mcar! frame (cons var (mcar frame)))
  ;(set-mcdr! frame (cons val (mcdr frame))))

(define (add-binding-to-frame! var val frame)
  (hash-set! frame var val))

;;;;;;;;;;;;;;;;;;

(define (extend-environment vars vals base-env)
  (if (= (length vars) (length vals))
      (cons (make-frame vars vals) base-env)
      (if (< (length vars) (length vals))
          (error "Too many arguments supplied" vars vals)
          (error "Too few arguments supplied" vars vals))))

#|
(define (lookup-variable-value var env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? var (car vars))
             (car vals))
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
        (error "Unbound variable" var)
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
  (env-loop env))
|#
(define (lookup-variable-value var env)
  (define (env-loop env)
    (if (eq? env the-empty-environment)
        (error "Unbound variable" var)
        (let ((frame (first-frame env)))
          (if (hash-has-key? frame var)
              (hash-ref frame var)
              (env-loop (enclosing-environment env))))))
  (env-loop env))

#|
(define (set-variable-value! var val env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? var (car vars))
             (set-car! vals val))
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
        (error "Unbound variable -- SET!" var)
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
  (env-loop env))
|#
(define (set-variable-value! var val env)
  (define (env-loop env)
    (if (eq? env the-empty-environment)
        (error "Unbound variable -- SET!" var)
        (let ((frame (first-frame env)))
          (if (hash-has-key? frame var)
              (hash-set! frame var val)
              (env-loop (enclosing-environment env))))))
  (env-loop env))

#|
(define (define-variable! var val env)
  (let ((frame (first-frame env)))
    (define (scan vars vals)
      (cond ((null? vars)
             (add-binding-to-frame! var val frame))
            ((eq? var (car vars))
             (set-car! vals val))
            (else (scan (cdr vars) (cdr vals)))))
    (scan (frame-variables frame)
          (frame-values frame))))
|#

(define (define-variable! var val env)
  (let ((frame (first-frame env)))
    (if (hash-has-key? frame var)
        (hash-set! frame var val)
        (add-binding-to-frame! var val frame))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define primitive-procedures
  (list (list 'car car)
        (list 'cdr cdr)
        (list 'cons cons)
        (list 'null? null?)
        (list '+ +)
        (list '* *)
        (list '- -)
        (list '= =)
        ; ....
        (list 'assoc assoc)
        (list 'cadr cadr)
        ; <more primitives>
        ))

(define (primitive-procedure-names)
  (map car primitive-procedures))
(define (primitive-procedure-objects)
  (map (lambda (proc) (list 'primitive (cadr proc)))
       primitive-procedures))

(define (setup-environment)
  (let ((initial-env
         (extend-environment (primitive-procedure-names)
                             (primitive-procedure-objects)
                             the-empty-environment)))
    (define-variable! 'true #t initial-env)
    (define-variable! 'false #f initial-env)
    initial-env))
(define the-global-environment (setup-environment))

;; ----------------------------------------------- apply must be original scheme "apply"
(define (apply-primitive-procedure proc args)
  (apply ;; apply in underlying scheme
   (primitive-implementation proc) args))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; mutual requirements
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (apply2 procedure arguments) ;; new version of "apply" that's distinct from scheme's
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
         (error
          "Unknown procedure type -- APPLY" procedure))))


(define eval-table
  (make-hash `((set!   . ,(λ (exp env) (eval-assignment exp env)))
               (define . ,(λ (exp env) (eval-definition exp env)))
               (if     . ,(λ (exp env) (eval-if exp env)))
               (and    . ,(λ (exp env) (eval-and exp env)))
               (or     . ,(λ (exp env) (eval-or exp env)))
               (lambda . ,(λ (exp env) (make-procedure (lambda-parameters exp)
                                                       (lambda-body exp)
                                                       env)))
               (let    . ,(λ (exp env) (eval (let->combination exp) env)))
               (let*   . ,(λ (exp env) (eval (let*->nested-lets exp) env)))
               (begin  . ,(λ (exp env) (eval-sequence (begin-actions exp) env)))
               (cond   . ,(λ (exp env) (eval (cond->if exp) env))))))

(define (eval exp env)
  (cond ((self-evaluating? exp) exp)
        ((variable? exp) (lookup-variable-value exp env))
        ((quoted? exp) (text-of-quotation exp))
        (else ((hash-ref eval-table
                         (car exp)
                         (λ () (λ (exp env) (apply2 (eval (operator exp) env)
                                               (list-of-values (operands exp) env)))))
               exp env))))


; Previous eval function:
#|
(define (eval exp env)
  (cond ((self-evaluating? exp) exp)
        ((variable? exp) (lookup-variable-value exp env))
        ((quoted? exp) (text-of-quotation exp))
        ((assignment? exp) (eval-assignment exp env)) ;set!
        ((definition? exp) (eval-definition exp env)) ;define
        ((if? exp) (eval-if exp env))                 ;if
        ((and? exp) (eval-and exp env)) ; added       ;and
        ((or? exp) (eval-or exp env))   ; added       ;or
        ((lambda? exp)                                ;lambda
         (make-procedure (lambda-parameters exp)
                         (lambda-body exp)
                         env))
        ((begin? exp)                                ;begin
         (eval-sequence (begin-actions exp) env))
        ((cond? exp) (eval (cond->if exp) env))      ;cond
        ((application? exp)                          ;call
         (apply2 (eval (operator exp) env)  ;;;;;;;;;;;;;;;; uses new version of "apply"
                 (list-of-values (operands exp) env)))
        (else
         (error "Unknown expression type -- EVAL" exp))))
|#
(define (eval-sequence exps env)
  (cond ((last-exp? exps) (eval (first-exp exps) env))
        (else (eval (first-exp exps) env)
              (eval-sequence (rest-exps exps) env))))

(define (eval-assignment exp env)
  (set-variable-value! (assignment-variable exp)
                       (eval (assignment-value exp) env)
                       env)
  'ok)

(define (eval-definition exp env)
  (define-variable! (definition-variable exp)
                    (eval (definition-value exp) env)
                    env)
  'ok)

#|
(define (list-of-values exps env)
  (if (no-operands? exps)
      '()
      (cons (eval (first-operand exps) env)
            (list-of-values (rest-operands exps) env))))
|#
; version that enforces left-to-right:
(define (list-of-values exps env)
  (if (no-operands? exps)
      '()
      (let* ((first-val (eval (first-operand exps) env))
             (rest-vals (list-of-values (rest-operands exps) env)))
        (cons first-val rest-vals))))



(define (eval-if exp env)
  (if (true? (eval (if-predicate exp) env))
      (eval (if-consequent exp) env)
      (eval (if-alternative exp) env)))


(define input-prompt ";;; M-Eval input:")
(define output-prompt ";;; M-Eval value:")
(define (driver-loop)
  (prompt-for-input input-prompt)
  (let ((input (read)))
    (let ((output (eval input the-global-environment)))
      (announce-output output-prompt)
      (user-print output)))
  (driver-loop))
(define (prompt-for-input string)
  (newline) (newline) (display string) (newline))
(define (announce-output string)
  (newline) (display string) (newline))


(define (user-print object)
  (if (compound-procedure? object)
      (display (list 'compound-procedure
                     (procedure-parameters object)
                     (procedure-body object)
                     '<procedure-env>))
      (display object)))



(define (and? exp) (tagged-list? exp 'and))
(define (or? exp) (tagged-list? exp 'or))

(define (eval-and exp env)
  (let loop ((args (cdr exp)))
    (cond ((null? args) 'true)
          ((true? (eval (car args) env))
           (loop (cdr args)))
          (else 'false))))

(define (eval-or exp env)
  (let loop ((args (cdr exp)))
    (cond ((null? args) 'false)
          ((true? (eval (car args) env)) 'true)
          (else (loop (cdr args))))))




(driver-loop)

