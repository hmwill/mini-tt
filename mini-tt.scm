;;; mini-tt.scm
;;;
;;; An implementation of the Mini-TT language
;;;
;;; Coquand, T, Kimoshita, Y., Nordström, B., & Takeyama, M (2009).
;;; "A simple type-theoretic language: Mini-TT", in:
;;; "From Seamantics to Computer Sicence", eds. Bertot, Y., Huet, G., Lévy, J.-J., & Plotkin, G.,
;;; Cambridge University Press
;;;
;;; Mini-TT is given by the following abstract syntax rules:
;;;
;;; Name:
;;;    <symbol>
;;;
;;; Exp:
;;;   (exp-one)                         Unit type
;;;   (exp-unit)                        Unit value
;;;   (exp-set)                         Universe of small types
;;;   (exp-var Name)                    Variable
;;;   (exp-pi Patt Exp Exp)             Function type construction
;;;   (exp-lambda Patt Exp)             Function value introduction
;;;   (exp-apply Exp Exp)               Function elimination
;;;   (exp-sigma Patt Exp Exp)          Dependent sum
;;;   (exp-make-pair Exp Exp)           Dependent sum introducton
;;;   (exp-fst Exp)                     Dependent sum elimination
;;;   (exp-snd Exp)                     Dependent sum elimination
;;;   (exp-con Name Exp)                Variant construction
;;;   (exp-sum Branch)                  Variant introduction
;;;   (exp-fun Branch)                  Variant elimination
;;;   (exp-let Decl Exp)                Declaration
;;;
;;; Decl:
;;;   (decl-def Patt Exp Exp)           Regular let binding
;;;   (decl-rec Patt Exp Exp)           Recursive let bidning
;;;
;;; Patt:
;;;   (pat-pair Patt Patt)              Match dependent sum
;;;   (pat-blank)                       Placeholder
;;;   (pat-var Name)                    Bind a variable
;;;
;;; Branch:
;;;   ((Name . Exp) (Name . Exp) ... )

(module mini-tt *
  (import (except scheme eval))
  (import srfi-34)
  (import datatype)
  
  ;;; branches are given as association list of labels to expressions
  (define (branch? branch)
    (let ((check-pair (lambda (p) 
                        (and (symbol? (car p)) 
                             (exp? (cdr p)))))) 
      (and (map check-pair branch))))

  ;;; expression representation
  (define-datatype exp exp?
    (exp-one)
    (exp-unit)
    (exp-set)
    (exp-var        (name symbol?))
    (exp-lambda     (pattern patt?) (expr exp?))
    (exp-pi         (pattern patt?) (domain exp?) (range exp?))
    (exp-sigma      (pattern patt?) (domain exp?) (range exp?))
    (exp-make-pair  (left exp?) (right exp?))
    (exp-construct  (label symbol?) (expr exp?))
    (exp-sum        (cases branch?))
    (exp-fun        (cases branch?))
    (exp-fst        (expr exp?))
    (exp-snd        (expr exp?))
    (exp-apply      (func exp?) (arg exp?))
    (exp-let        (decl decl?) (body exp?)) )
  
  ;;; Recursive and non-recursive declarations
  (define-datatype decl decl?
    (decl-def (patt patt?) (typ exp?) (val exp?))
    (decl-rec (patt patt?) (typ exp?) (val exp?)) )
  
  ;;; Simple pattern matching
  (define-datatype patt patt?
    (pat-pair (left patt?) (right patt?))
    (pat-blank)
    (pat-var (name symbol?)) )
  
  ;;; a value
  (define-datatype val val?
    (val-unit)
    (val-one)
    (val-set)
    (val-accum (a accum?))
    (val-pi (t val?) (g closure?))
    (val-lambda (f closure?))
    (val-sigma (t val?) (g closure?))
    (val-make-pair (fst val?) (snd val?))
    (val-construct (label symbol?) (v val?))
    (val-sum (choices choice-closure?))
    (val-fun (choices choice-closure?)) )
  
  ;;; an accumulator ("neutral value")
  (define-datatype accum accum?
    (acc-var (n number?))
    (acc-fun (fun accum?) (arg val?))
    (acc-app (choice choice-closure?) (arg accum?))
    (acc-fst (acc accum?))
    (acc-snd (acc accum?)) )
  
  ;;; function closure
  (define-datatype closure closure?
    (clos-bind (pat patt?) (body exp?) (env env?))
    (clos-decon (f closure?) (c symbol?)) )
  
  ;;; choice closure
  (define (choice-closure? s . rho)
    (and (branch? s)
         (env? rho)))
    
  ;; Check if the pattern p contains the variable v
  (define (in-pattern p v)
   (cases patt p
     (pat-pair (left right) (or (in-pattern left v) (in-pattern right v)))
     (pat-blank () #f)
     (pat-var (x) (equal? x v))))
     
  ;;; Extract the first component of a value v, reduce if we have a pair value otherwise
  ;;; accumulate the result
  (define (vfst v)
    (cases val v
      (val-make-pair    (left right)  left)
      (val-accum        (acc)         (val-accum (acc-fst acc))) ))
      
  ;;; Extract the second component of a value v, reduce if we have a pair value otherwise
  ;;; accumulate the result
  (define (vsnd v)
    (cases val v
      (val-make-pair    (left right)  right)
      (val-accum        (acc)         (val-accum (acc-snd acc))) ))
      
  ;;; Project a value v associated with a pattern p to a single variable x
  (define (project-pattern p x v)
    (cases patt p
      (pat-pair   (left right) 
        (cond 
          ((in-pattern left  v) => (project-pattern left  x (vfst v))) 
          ((in-pattern right v) => (project-pattern right x (vsnd v)))))
      (pat-var    (y)          
        (cond 
          ((equal? x y) => v)
          (else (raise "Internal inconsistency"))))
      (else (raise "Internal inconsistency") ) ))

  ;;; an entry in the evaluation environment; the environment is a list of those
  (define-datatype env-entry env-entry?
    (env-val (pat patt?) (v val?))
    (env-decl (decl decl?)))
  
  (define (env? env)
    (and (map env-entry? env)))
      
  (define (lookup-with-entry x entry env)
    (cases env-entry entry
      (env-val  (p v) 
        (cond
          ((in-pattern p x) => (project-pattern p x v)) 
          (else #f)))
      (env-decl (d) 
        (cases decl d
          (decl-def (p t e) 
            (and (in-pattern p x)
                 (project-pattern p x (eval e env))))
          (decl-rec (p t e) 
            (and (in-pattern p x)
                 (project-pattern p x (eval e (cons entry env)))))))))
    
  ;;; look up a variable within the given environment
  ;;;
  ;;; Raises an exception if not found
  (define (lookup var env)
    (cond
      ((null? env) => (raise "Variable not found in environment"))
      ((lookup-with-entry var (car env) (cdr env)))
      (else (lookup var (cdr env)))))
      
  ;;; instantiate a function closure
  (define (inst cl v)
    (cases closure cl
      (clos-bind (pat body env)
        (eval body (cons (env-val pat v) env)))
      (clos-decon (f c) 
        (inst f (val-construct c v))) ) )
          
  ;;; determine the application of a function to a value; possibly with accumulators
  (define (eval-apply func arg)
    (cases val func
      (val-lambda (f)  
        (inst f arg) )
      (val-fun (choices) 
        (cases val arg
          (val-construct (label value) 
            (let* ((s         (car choices)) 
                   (env       (cdr choices)) 
                   (case-expr (assoc label s) ))
              (eval-apply (eval case-expr env) value) ) ) 
          (val-accum (acc) (val-accum (acc-app choices acc))) ) )
      (val-accum (acc) 
        (val-accum (acc-fun acc arg)) ) ) )
      
  ;;; Evalute the given expression in the provided environment
  (define (eval expr env)
    (cases exp expr
      (exp-one ()   (val-one))
      (exp-unit ()  (val-unit))
      (exp-set ()   (val-set))
        
      (exp-var (name) 
        (lookup name env))
      (exp-lambda (pattern expr) 
        (val-lambda (clos-bind pattern expr env)))
      (exp-pi (pattern domain range) 
        (val-pi (eval domain env) (clos-bind pattern range env)))
      (exp-sigma (pattern domain range) 
        (val-sigma (eval domain env) (clos-bind pattern range env)))
      (exp-make-pair (left right) 
        (val-make-pair (eval left env) (eval right env)))
      (exp-construct (label expr) 
        (val-construct label (eval expr env)))
      (exp-sum (choices) 
        (val-sum (cons choices env)))
      (exp-fun (choices) 
        (val-fun (cons choices env)))
      (exp-fst (expr) 
        (let ((evaluated (eval expr env)))
          (vfst evaluated) ) )
      (exp-snd (expr) 
        (let ((evaluated (eval expr env)))
          (vsnd evaluated) ) )
      (exp-apply (func arg) 
        (eval-apply (eval func env) (eval arg env)))
      (exp-let (decl body) 
        (eval body ((cons (env-decl decl) env))))))
          
  ;;; Normalized expression type
  (define-datatype nexp nexp?
    (nexp-one)
    (nexp-unit)
    (nexp-set)
    (nexp-accum     (acc nacc?))
    (nexp-lambda    (i integer?) (expr   nexp?))
    (nexp-pi        (i integer?) (domain nexp?) (range nexp?))
    (nexp-sigma     (i integer?) (domain nexp?) (range nexp?))
    (nexp-make-pair (left nexp?) (right nexp?))
    (nexp-construct (label symbol?) (expr nexp?))
    (nexp-sum       (cases nchoices?))
    (nexp-fun       (cases nchoices?))
    (nexp-fst       (expr nexp?)) )
  
  
  ;;; Normalized accumulator type
  (define-datatype nacc nacc?
    (nacc-var (i integer?))
    (nacc-fun (acc nacc?) (arg nexp?))
    (nacc-app (choices nchoices?) (arg nacc?))
    (nacc-fst (acc nacc?))
    (nacc-snd (acc nacc?))
  )
  
  ;;; Normalized choice closure
  (define (nchoices? s . rho)
    (and (branch? s)
         (nenv? rho)))
      
  ;;; Normalized environment entry type
  (define-datatype nenv-entry nenv-entry?
    (nenv-val (pat patt?) (e nexp?))
    (nenv-decl (decl decl?)))
  
  (define (nenv? env)
    (and (map nenv-entry? env)))
      
  ;;; Convert the given value back into a normalized expression
  (define (readback-value i v)
    (cases val v
      (val-unit       ()        (nexp-unit))
      (val-one        ()        (nexp-one))
      (val-set        ()        (nexp-set))
      (val-accum      (a)       (nexp-accum (readback-accum i a)))
      (val-construct  (l v)     (nexp-construct l (readback-value i v)))
      (val-make-pair  (fst snd) (nexp-make-pair (readback-value i fst) 
                                                (readback-value i snd)))
      (val-lambda     (f)       (nexp-lambda i (readback-value (+ i 1) 
                                                               (inst f (nexp-accum (acc-var i))))))
      (val-pi         (t g)     (nexp-pi i 
                                        (readback-value i t)
                                        (readback-value (+ i 1) 
                                                        (inst g (nexp-accum (acc-var i))))))
      (val-sigma      (t g)     (nexp-sigma i 
                                        (readback-value i t)
                                        (readback-value (+ i 1) 
                                                        (inst g (nexp-accum (acc-var i))))))
      (val-sum        (cc)      (nexp-sum (cons (car cc)
                                          (readback-env i (cdr cc)))))
      (val-fun        (cc)      (nexp-fun (cons (car cc)
                                          (readback-env i (cdr cc)))))))
      
  ;;; Convert the given accumulator into a normalized expression
  (define (readback-accum i a)
    (cases accum a
      (acc-var        (n)       (nacc-var n))
      (acc-fun        (acc arg) (nacc-fun (readback-accum i acc) 
                                          (readback-value i arg)))
      (acc-app        (cc arg)  (nacc-app (cons (car cc)
                                                (readback-env i (cdr cc))) 
                                          (readback-accum i arg)))
      (acc-fst        (acc)     (nacc-fst (readback-accum i acc)))
      (acc-snd        (acc)     (nacc-snd (readback-accum i acc)))))
  
  ;;; Convert a single environment entry into a normalized expression
  (define (readback-env-entry i e)
    (cases env-entry e
      (env-val  (p v)     (nenv-val p (readback-value i v)))
      (env-decl (d)       e)))
    
  ;;; Convert the given environment into a normalized form
  (define (readback-env i e)
    (cond
      ((null? e) => e)
      (else (cons (readback-env-entry i (car e)) 
                  (readback-env-entry i (cdr e))))))
  
  ;;; extend the the given context by binding all variable included in the pattern p to their types
  (define (extend-context context p t v)
    (cases patt p
      (pat-pair   (p1 p2)  
        (cases val t
          (val-sigma (t g)      (let ((context1 (extend-context p1 t (vfst v))))
                                  (extend-context context1 p2 (inst g (vfst v)) (vsnd v))))))
      (pat-blank  ()            context)
      (pat-var    (x)           ((cons (cons x t) context)))))
    
  ;;; check if <p:a b> qualified by pi or sigma form a valid type in the given context and environment
  (define (check-is-pi-sigma-type? env context l p a b)
    (and
      (check-is-type? env context l a)
      ((let ((context0  (extend-context context p (eval a env) (val-accum (acc-var l))))
             (env0      (cons (env-val p (val-accum (acc-var l))) env)))
          (check-is-type? (+ l 1) env0 context0 b)))))
          
  ;;; check if expr denotes a type using the given environment and context
  (define (check-is-type? env context l e)
    (cases exp e
      (exp-set    ()      #t)
      (exp-pi     (p a b) (check-is-pi-sigma-type? env context l p a b))
      (exp-sigma  (p a b) (check-is-pi-sigma-type? env context l p a b))
      (else               (check-expr-type? env context l e (val-set)))))
    
    ;;; check that decl is a valid declaration in the given environment and context.
    ;;; if this is the case, return the extended context
    (define (check-decl env context l d)
      (cases decl d
        (decl-def (p a e) 
          (if (check-is-type? env context l a) 
            (let ((t (eval a env)))
              (if (check-expr-type? env context l e t) 
                (extend-context context p t (eval e env)) 
                (raise "Invalid declaration"))) 
            (raise "Invalid declaration")))
        (decl-rec (p a e) 
          (if (check-is-type? env context l a) 
            (let* ((t         (eval a env))
                   (gen       (val-accum (acc-var l)))
                   (context1  (extend-context context p t gen)))
                (if (check-expr-type? (+ l 1) 
                                      (cons (env-val p gen) env) 
                                      context1 e t)
                  (let  ((v   (eval e (cons (env-decl d) env))))
                    (extend-context context p t v))                    
                  (raise "Invalid declaration")))
            (raise "Invalid declaration")))))
      
  ;;; calculate the normal forms of two type values and test if they are equal
  (define (equal-normal-type? i v1 v2)
    (equal? (readback-value i v1)
            (readback-value i v2)))
            
  ;;; check that a sigma or pi expr matches a type in the given environment and context
  (define (check-sigma-pi-expr-type? env context l p a b t)
    (if (check-expr-type? env context l a (val-set))
      (let* ((gen       (val-accum (acc-var l)))
             (context1  (extend-context context p (eval a env) gen)))
        (check-expr-type? (cons (env-val p gen) env) context1 b (val-set)))
      (raise "Type mismatch")))
    
  ;;; check that expr matches a type in the given environment and context
  (define (check-expr-type? env context l e t)
    (cases exp e
      (exp-lambda (p e)
        (cases val t
          (val-pi (t g)     (let* ((gen       (val-accum (acc-var l)))
                                   (context1  (extend-context context p t gen)))
                              (check-expr-type? (+ l 1) 
                                               (cons (env-val p gen) env) 
                                               context1 e (inst g gen))))))
      (exp-make-pair (e1 e2)
        (cases val t
          (val-sigma (t g)  (and (check-expr-type? env context l e1 t)
                                 (check-expr-type? env context l e2 (inst g (eval e1 env)))))))
      (exp-construct  (c e)
        (cases val t
          (val-sum (cc)     (let* ((cas     (car cc))
                                   (env1    (cdr cc))
                                   (a       (cdr (assoc c cas))))  ; TODO: This fails if the label is not found
                              (check-expr-type? env context l e (eval a env1))))))
      (exp-unit ()
        (cases val t        
          (val-one ()       #t)))
      (exp-one ()
        (cases val t        
          (val-set ()       #t)))
          
      (exp-pi (p a b) 
        (cases val t
          (val-set ()       (check-sigma-pi-expr-type? env context l p a b t))))
      (exp-sigma (p a b) 
        (cases val t
          (val-set ()       (check-sigma-pi-expr-type? env context l p a b t))))
      (exp-sum (cas) 
        (cases val t
          (val-set ()       (and (map (lambda (a) (check-expr-type? env context l a (val-set))) 
                                      cas)))))
      (exp-fun (ces) 
        (cases val t
          (val-pi (sum g)
          (cases val sum
            (val-sum (cc)   (let* ((cas     (car cc))
                                   (env1    (cdr cc)))
                                 (if (equal? (map car ces) (map car cas)) 
                                   (and (map (lambda (ce ca) 
                                               (let*  ((c   (car ce))
                                                       (e   (cdr ce))
                                                       (a   (cdr ca))
                                                       (cl  (val-pi (eval a env1) (clos-decon g c))))
                                                 (check-expr-type? env context l e cl))) 
                                             ces cas)) 
                                   (raise "Case labels do not match"))))))))
                                 
      (exp-decl (d e)       (let ((context1 (check-decl env context l d)))
                              (check-expr-type? (cons (env-decl d) env) context1 e t)))
      
    (else (equal-normal-type? l t (infer-expr-type env context l e)))))
    
  ;;; infer the type of expr in the given environment and context
  (define (infer-expr-type env context l e)
    (cases exp e
      (exp-var (x)      (cdr (assoc x context)))
      (exp-app (e1 e2)  (cases val (infer-expr-type env context l e1)
                          (val-pi (t g) 
                            (if (check-expr-type? env context l e2 t)
                              (inst g (eval e2 env))
                              (raise "Cannot infer type")))))
      (exp-fst (e)      (cases val (infer-expr-type env context l e)
                          (val-sigma (a g)
                            a)))
      (exp-snd (e)      (cases val (infer-expr-type env context l e)
                          (val-sigma (a g)
                            (inst g (vfst (eval e env))))))
      (else (raise "Cannot infer type"))))
)