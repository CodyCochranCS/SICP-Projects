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
(define (named-let? exp)
  (and (let? exp) (symbol? (cadr exp))))
(define (let-name exp)
  (if (named-let? exp)
      (cadr exp)
      (error "Attempt to get name of non-name let -- " exp)))
(define (let-bindings exp)
  (if (named-let? exp)
      (caddr exp)
      (cadr exp)))
(define (let-body exp)
  (if (named-let? exp)
      (cdddr exp)
      (cddr exp)))
(define (let->combination exp)
  (let loop ((params '())
             (vals '())
             (bindings (let-bindings exp)))
    (if (null? bindings)
        (let ((lambda-proc (make-lambda (reverse params) (let-body exp)))
              (vals (reverse vals)))
          (if (named-let? exp)
              (let ((name (let-name exp)))
                (list (list 'lambda '()
                            (list 'define name lambda-proc)
                            (cons name vals))))
              (cons lambda-proc vals)))
        (let ((first (car bindings))
              (rest  (cdr bindings)))
          (loop (cons (car first) params)
                (cons (cadr first) vals)
                rest)))))

(define (make-let bindings body)
  (cons 'let (cons bindings body))) ; can't use list since last item is already list

(define (let*? exp) (tagged-list? exp 'let*))
(define (let*-bindings exp) (cadr exp))
(define (let*-body exp) (cddr exp))
(define (let*->nested-lets exp)
  (let ((bindings (let*-bindings exp)))
    (if (null? bindings)
        ;(cons 'let (cons '() (let*-body exp)))
        (make-let '() (let*-body exp))
        (let recurse ((first-binding (list (car bindings)))
                      (rest-bindings (cdr bindings)))
          (if (null? rest-bindings)
              ;(cons 'let (cons (list first-binding) (let*-body exp)))
              (make-let first-binding (let*-body exp))
              (make-let first-binding
                    (list (recurse (list (car rest-bindings)) (cdr rest-bindings)))))))))


(define (letrec? exp) (tagged-list? exp 'letrec))
(define (letrec-bindings exp) (cadr exp))
(define (letrec-body exp) (cddr exp))
(define (letrec->let exp)
  (let ((bindings (letrec-bindings exp))
        (body (letrec-body exp)))
    (if (null? bindings)
        (make-let '() body)
        (let recurse ((bindings bindings)
                      (unassigned-list '())
                      (set-list '()))
          (if (null? bindings)
              (make-let (reverse unassigned-list)  ; Reversing may not be necessary
                        (append (reverse set-list) ; but just in case....
                                body))
              (let ((first-binding (car bindings)))
                (recurse (cdr bindings)
                         (cons (list (car first-binding) (quote '*unassigned*))
                               unassigned-list)           ; (u <e1>) -> (u '*unassigned*)
                         (cons (cons 'set! first-binding) ; (u <e1>) -> (set! u <e1>)
                               set-list))))))))



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

(define (scan-out-defines body)
  (let loop ((definitions '())
             (body body))
    (if (tagged-list? (car body) 'define)
        (loop (cons (cdar body) definitions)
              (cdr body))
        (if (null? definitions)
            body
            (let loop ((definitions definitions)
                       (let-bindings '())
                       (body body))
              (if (null? definitions)
                  (list (cons 'let (cons let-bindings body)))
                  (let ((current-definition (car definitions)))
                    (loop (cdr definitions)
                          (cons (list (car current-definition) (list 'quote '*unassigned*)) let-bindings)
                          (cons (cons 'set! current-definition) body)))))))))


(define (make-procedure parameters body env)
  (list 'procedure parameters body env)) ; modify "body" -> "(scan-out-defines body)"
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; REIMPLEMENT THIS LATER

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
              (let ((val (hash-ref frame var)))
                (if (eq? val '*unassigned*)
                    (error "Unassigned variable - " var)
                    val))
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

#|
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
|#






#|
(define eval-table
  (make-hash `((set!   . ,(λ (exp env) (eval-assignment exp env))) ;;;;;;;;;;;
               (define . ,(λ (exp env) (eval-definition exp env))) ;;;;;;;;;;;
               (if     . ,(λ (exp env) (eval-if exp env))) ;;;;;;;;;;;;;
               (and    . ,(λ (exp env) (eval-and exp env)))
               (or     . ,(λ (exp env) (eval-or exp env)))
               (lambda . ,(λ (exp env) (make-procedure (lambda-parameters exp) ;;;;;;;;;
                                                       (lambda-body exp)
                                                       env)))
               (let    . ,(λ (exp env) (eval (let->combination exp) env)))
               (let*   . ,(λ (exp env) (eval (let*->nested-lets exp) env)))
               (letrec . ,(λ (exp env) (eval (letrec->let exp) env)))
               (begin  . ,(λ (exp env) (eval-sequence (begin-actions exp) env)));;;;;;;;;;;;
               (cond   . ,(λ (exp env) (eval (cond->if exp) env)))))) ;;;;;;;;;;;;
|#

(define analyze-table
  (make-hash `((set!   . ,(λ (exp) (analyze-assignment exp)))
               (define . ,(λ (exp) (analyze-definition exp)))
               (if     . ,(λ (exp) (analyze-if exp))) ;;;;;;;;;;;;;
               (and    . ,(λ (exp) (analyze-and exp)))
               (or     . ,(λ (exp) (analyze-or exp)))
               (lambda . ,(λ (exp) (analyze-lambda exp)))
               (let    . ,(λ (exp) (analyze (let->combination exp))))
               (let*   . ,(λ (exp) (analyze (let*->nested-lets exp))))
               (letrec . ,(λ (exp) (analyze (letrec->let exp))))
               (begin  . ,(λ (exp) (analyze-sequence (begin-actions exp))))
               (cond   . ,(λ (exp) (analyze (cond->if exp)))))))

(define (analyze exp)
  (cond ((self-evaluating? exp) (analyze-self-evaluating exp))
        ((variable? exp) (analyze-variable exp))
        ((quoted? exp) (analyze-quoted exp))
        (else ((hash-ref analyze-table
                         (car exp)
                         (λ () (λ (exp) (analyze-application exp))))
               exp))))

(define (eval exp env)
  ((analyze exp) env))

(define (analyze-self-evaluating exp)
  (λ (env) exp))

(define (analyze-quoted exp)
  (let ((qval (text-of-quotation exp)))
    (λ (env) qval)))

(define (analyze-variable exp)
  (λ (env) (lookup-variable-value exp env)))

(define (analyze-lambda exp)
  (let ((vars (lambda-parameters exp))
        (bproc (analyze-sequence (lambda-body exp))))
    (λ (env) (make-procedure vars bproc env))))

(define (analyze-application exp)
  (let ((fproc (analyze (operator exp)))
        (aprocs (map analyze (operands exp))))
    (λ (env)
      (execute-application (fproc env)
                           (map (lambda (aproc) (aproc env))
                                aprocs)))))

(define (execute-application proc args)
  (cond ((primitive-procedure? proc)
         (apply-primitive-procedure proc args))
        ((compound-procedure? proc)
         ((procedure-body proc)
          (extend-environment (procedure-parameters proc)
                              args
                              (procedure-environment proc))))
        (else (error "Unknown procedure type -- EXECUTE-APPLICATION" proc))))














#|
(define (eval-sequence exps env)
  (cond ((last-exp? exps) (eval (first-exp exps) env))
        (else (eval (first-exp exps) env)
              (eval-sequence (rest-exps exps) env))))
|#
(define (analyze-sequence exps)
  (define (sequentially proc1 proc2)
    (λ (env) (proc1 env) (proc2 env)))
  (define (loop first-proc rest-procs)
    (if (null? rest-procs)
        first-proc
        (loop (sequentially first-proc (car rest-procs))
              (cdr rest-procs))))
  (let ((procs (map analyze exps)))
    (if (null? procs)
        (error "Empty sequence -- ANALYZE")
        (loop (car procs) (cdr procs)))))




#|
(define (eval-assignment exp env)
  (set-variable-value! (assignment-variable exp)
                       (eval (assignment-value exp) env)
                       env)
  'ok)
|#
(define (analyze-assignment exp)
  (let ((var (assignment-variable exp))
        (vproc (analyze (assignment-value exp))))
    (λ (env)
      (set-variable-value! var (vproc env) env)
      'ok)))




#|
(define (eval-definition exp env)
  (define-variable! (definition-variable exp)
                    (eval (definition-value exp) env)
                    env)
  'ok)
|#
(define (analyze-definition exp)
  (let ((var (definition-variable exp))
        (vproc (analyze (definition-value exp))))
    (λ (env)
      (define-variable! var (vproc env) env)
      'ok)))




#|
(define (list-of-values exps env)
  (if (no-operands? exps)
      '()
      (let* ((first-val (eval (first-operand exps) env))
             (rest-vals (list-of-values (rest-operands exps) env)))
        (cons first-val rest-vals))))
|#



#|
(define (eval-if exp env)
  (if (true? (eval (if-predicate exp) env))
      (eval (if-consequent exp) env)
      (eval (if-alternative exp) env)))
|#

(define (analyze-if exp)
  (let ((pproc (analyze (if-predicate exp)))
        (cproc (analyze (if-consequent exp)))
        (aproc (analyze (if-alternative exp))))
    (λ (env)
      (if (true? (pproc env))
          (cproc env)
          (aproc env)))))




(define (and? exp) (tagged-list? exp 'and))
(define (or? exp) (tagged-list? exp 'or))

#|
(define (eval-and exp env)
  (let loop ((args (cdr exp)))
    (cond ((null? args) 'true)
          ((true? (eval (car args) env))
           (loop (cdr args)))
          (else 'false))))
|#
(define (analyze-and exp)
  (let ((args (cdr exp)))
    (if (null? args)
        (analyze 'true)
        (let ((first-arg (car args))
              (rest-args (cdr args)))
          (if (null? rest-args)
              (analyze first-arg) ; (and x) = x
              (analyze (make-if first-arg
                                (cons 'and rest-args)
                                'false)))))))
                                
#|
(define (eval-or exp env)
  (let loop ((args (cdr exp)))
    (cond ((null? args) 'false)
          ((true? (eval (car args) env)) 'true)
          (else (loop (cdr args))))))
|#
(define (analyze-or exp)
  (let ((args (cdr exp)))
    (if (null? args)
        (analyze 'false)
        (let ((first-arg (car args))
              (rest-args (cdr args)))
          (if (null? rest-args)
              (analyze first-arg) ; (or x) = x
              (analyze (make-if first-arg
                                first-arg
                                (cons 'or rest-args))))))))



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




; (driver-loop)

