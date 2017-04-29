;;
;; grassc.scm - Compiler from Grass to lambda calculus
;; http://www.blue.sky.or.jp/grass/
;;
;; Copyright (C) 2008 UENO Katsuhiro. All rights reserved.
;;
;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions
;; are met:
;; 1. Redistributions of source code must retain the above copyright
;;    notice, this list of conditions and the following disclaimer.
;; 2. Redistributions in binary form must reproduce the above copyright
;;    notice, this list of conditions and the following disclaimer in
;;    the documentation and/or other materials provided with the
;;    distribution.
;;
;; THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''
;; AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
;; THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
;; PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS
;; BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
;; CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
;; SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR
;; BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
;; WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE
;; OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN
;; IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
;;
;; History:
;;
;; 2008-06-17
;;   - First version.
;;

;;
;; == Abstract
;;
;; This program gives a simulation of Grass machine by lambda calculus.
;; In this program, we define a translation from Grass machine state to
;; lambda calculus with explicit substitutions[1] and show the correctness
;; of the translation. Translation from lambda caluculus with explicit
;; substitutions to lambda calculus is trivial, that is, just reducing
;; substitution terms. By composing the above two translations, we obtain
;; a compilation algorithm from Grass to lambda calculus.
;;
;; == Lambda calculus with explicit substitutions
;;
;;   e ::= 1 | \e | e e | e[s]
;;   s ::= id | ^ | e::s | s[s]
;;
;;   Beta         (\e1) e2     --> e1[e2::id]
;;   VarId        1[id]        --> 1
;;   VarCons      1[e::s]      --> e
;;   App          (e1 e2)[s]   --> (e1[s]) (e2[s])
;;   Abs          (\e)[s]      --> \(e[1::(s[^])])
;;   Clos         (e[s1])[s2]  --> e[s1[s2]]
;;   IdL          id[s]        --> s
;;   ShiftId      ^[id]        --> ^
;;   ShiftCons    ^[e::s]      --> s
;;   Map          (e::s1)[s2]  --> e[s1]::s1[s2]
;;   Ass          (s1[s2])[s3] --> s1[s2[s3]]
;;
;; m and n range over the set of positive integers.
;; We wrote "^n" as an abbreviation of a composition of n shift terms.
;;
;;   ^0 = id
;;   ^1 = ^
;;   ^2 = ^[^]
;;   ...
;;   ^n = ^[^[...[^]...]]
;;        <----- n ----->
;;
;; Single positive integer n denotes 1[^(n-1)].
;;
;;   2 = 1[^1] = 1[^]
;;   3 = 1[^2] = 1[^[^]]
;;   ...
;;   n = 1[^(n-1)] = 1[^[^[...[^]...]]]
;;                    <----- n-1 ----->
;;
;; Translation from lambda calculus with explicit substitutions to
;; lambda calculus is eliminating substitution terms by applying
;; reduction rules except Beta.
;;
;; In this program, we additionally use the following rules to eliminate
;; substitution terms.
;;
;; Lemma
;;   VarN         n[e::s]     -*-> (n-1)[s]
;;   VarShiftN    m[^n]       -*-> (m+n)
;;   AssN         ^m[^n]      -*-> ^(m+n)
;;
;; Lemma
;;   IdR          s[id]       -*-> s
;;   Beta'        (\e1)[s] e2 -*-> e1[e2::s]
;;
;; == Simulate Grass machine by lambda calculus with explicit substitutions
;;                      _
;; We give an algorithm X, which translates elements of Grass machine state
;; to lambda calculus with explicit substitutions.
;;
;; Machine State:
;;   _________   _ _
;;   (C,E,nil) = C[E]
;;   ________________     __  __  _______
;;   (C,E,(Cd,Ed)::D) = (\Cd)[Ed] (C,E,D)
;;
;; Code:
;;   ___________     _   _ _
;;   App(m,n)::C = (\C) (m n)
;;   _____________     __    __
;;   Abs(1,C1)::C2 = (\C2) (\C1)
;;   _____________     __    ________________
;;   Abs(n,C1)::C2 = (\C2) (\Abs(n-1,C1)::nil)   (n > 1)
;;   ___
;;   nil = 1
;;
;; Environment:
;;   __________     _  __   __
;;   (C,E1)::E2 = (\C)[E1]::E2
;;   ___
;;   nil = id
;;
;; Lemma.
;;                                   _______      __________
;;   If (C,E,D) --> (C',E',D'), then (C,E,D) -*-> (C',E',D').
;;
;; Proof (sketch)
;;   ___________________
;;   (App(m,n)::C, E, D)
;;     = D ((\C) (m n))[E]
;;     -(App)-----> D ((\C)[E] (m n)[E])
;;     -(App)-----> D ((\C)[E] (m[E] n[E]))
;;     -(VarN)*---> D ((\C)[E] ((\Cm)[Em] (\Cn)[En])
;;     -(Beta')---> D ((\C)[E] Cm[(\Cn)[En]::Em])
;;                  ___________________________
;;                = (Cm, (Cn,En)::Em, (C,E)::D)
;;   _____________________
;;   (Abs(1,C1)::C2, E, D)
;;     = D ((\C2) (\C1))[E]
;;     -(App)-----> D ((\C2)[E] (\C1)[E])
;;     -(Beta')---> D C2[(\C1)[E]::E]
;;                  __________________
;;                = (C2, (C1,E)::E, D)
;;   _____________________________
;;   (nil, (C1,E1)::E, (C2,E2)::D)
;;     = D ((\C2)[E2] 1[(\C1)[E1]::E])
;;     -(VarCons)-> D ((\C2)[E2] (\C1)[E1])
;;     -(Beta')---> D C2[(\C1)[E1]::E2]
;;                  ____________________
;;                = (C2, (C1,E1)::E2, D)
;;
;; We can obtain a compilation algorithm from Grass to lambda calculus
;; by composing this translation and the translation from lambda
;; calculus with explicit substitutions to lambda calculus.
;;
;; == Giving names to De Bruijn notation
;;
;; To execute the result of the compilation by eval, we need to represent
;; the resulting terms in LISP form by giving variable names to De Bruijn
;; indecies[2].
;;
;; The algorithm to give names is trivially constructed as an inversion
;; of the algorithm getting red of the names defined in [2].
;;
;;
;; References:
;;
;; [1] M. Abadi, L. Cardelli, P.-L. Curien, and J.-J. Levy,
;;     Explicit substitutions, Journal of Functional Programming,
;;     Vol.1, No.4, pp.375-416, 1991.
;;
;; [2] N. De Bruijn, Lmabda-calculus Notation with Nameless Dummies,
;;     a Tool for Automatic Formula Manipulation, Indagationes
;;     Mathematicae (Proceedings), Vol.75, No.5, pp.381-392, 1972.
;;

;;;; for Gauche
;(use util.match)

;;;; stub of util.match
(define-syntax match
  (syntax-rules (quote)
    ((match exp) (match-fail))
    ((match exp ((quote x) body ...) ms ...)
     (if (equal? exp 'x) (begin body ...) (match exp ms ...)))
    ((match exp (() body ...) ms ...)
     (if (null? exp) (begin body ...) (match exp ms ...)))
    ((match exp ((pat . pats) body ...) ms ...)
     (let ((fail (lambda () (match exp ms ...))))
       (if (pair? exp)
           (match (car exp) (pat (match (cdr exp) (pats body ...) (_ (fail))))
                            (_ (fail)))
           (fail))))
    ((match exp (x body ...) ms ...)
     (let ((x exp)) body ...))))

;;;; Parser

(define (parse src)
  (define (getc i)
    (if (< i (string-length src)) (string-ref src i) #f))
  (define (eof)
    (lambda (i) (and (= i (string-length src)) (cons #t i))))
  (define (read-if f)
    (lambda (i) (let ((c (getc i))) (if (and c (f c)) (cons c (+ 1 i)) #f))))
  (define (read c)
    (seq (skip) (lambda (x) (read-if (lambda (x) (eq? x c))))))
  (define (seq p1 k)
    (lambda (i) (let ((r (p1 i))) (and r ((k (car r)) (cdr r))))))
  (define (orp p1 p2)
    (lambda (i) (or (p1 i) (p2 i))))
  (define (return x)
    (lambda (i) (cons x i)))
  (define (rep p)
    (orp (seq p (lambda (x) (seq (rep p) (lambda (y) (return (cons x y))))))
         (return ())))
  (define (rep1 p)
    (seq p (lambda (x) (seq (rep p) (lambda (y) (return (cons x y)))))))

  (define (skip)
    (rep (read-if (lambda (x) (not (memq x '(#\w #\W #\v)))))))
  (define (app)
    (seq (rep1 (read #\W)) (lambda (w1)
      (seq (rep1 (read #\w)) (lambda (w2)
        (return `(app ,(length w1) ,(length w2))))))))
  (define (abs)
    (seq (rep1 (read #\w)) (lambda (w1)
      (seq (rep (app)) (lambda (c)
        (return `((abs ,(length w1) . ,c))))))))
  (define (prog)
    (seq (abs) (lambda (a)
      (seq (rep (seq (read #\v) (lambda (_) (orp (abs) (rep (app))))))
           (lambda (l)
             (return (apply append a l)))))))
  (define (top)
    (seq (rep (read-if (lambda (x) (not (eq? x #\w))))) (lambda (_)
      (seq (prog) (lambda (ret)
        (seq (skip) (lambda (_)
          (seq (eof) (lambda (_) (return ret))))))))))

  (car ((top) 0)))

;;;; Apply substitutions

(define (apply-shift subst)
  (match subst
   ((exp . sub) (cons (apply-subst exp 1) (apply-shift sub)))
   (n (+ 1 n))))

(define (apply-subst exp subst)
  (match exp
   (('lambda body)
    `(lambda ,(apply-subst body (cons 1 (apply-shift subst)))))
   ((exp1 exp2)
    `(,(apply-subst exp1 subst) ,(apply-subst exp2 subst)))
   (n
    (if (symbol? n) n
        (match subst
         ((e . s) (if (= 1 n) e (apply-subst (- n 1) s)))
         (m (+ n m)))))))

;;;; Compile Grass machine state to lambda calculus

(define (simulate-code code)
  (match code
   ((('app m n) . t)
    `((lambda ,(simulate-code t)) (,m ,n)))
   ((('abs n . c) . t)
    `((lambda ,(simulate-code t))
      (lambda ,(simulate-code (if (= n 1) c `((abs ,(- n 1) . ,c)))))))
   (() 1)))

(define (simulate-cls cls)
  (if (symbol? cls) cls
      (apply-subst `(lambda ,(simulate-code (car cls)))
                   (simulate-env (cdr cls)))))

(define (simulate-env env)
  (if (null? env) 0
      (cons (simulate-cls (car env)) (simulate-env (cdr env)))))

(define (simulate-dump head dump)
  (if (null? dump) head
      (simulate-dump `(,(simulate-cls (car dump)) ,head) (cdr dump))))

(define (simulate code env dump)
  (simulate-dump (apply-subst (simulate-code code) (simulate-env env)) dump))

;;;; Give variable names to De Bruijn indecies

(define (give-name env exp)
  (match exp
   (('lambda body)
    (let ((var (string->symbol
                (string-append "$" (number->string (length env))))))
      `(lambda (,var) ,(give-name (cons var env) body))))
   ((exp1 exp2)
    `(,(give-name env exp1) ,(give-name env exp2)))
   (x
    (if (symbol? x) x
        (list-ref env (- x 1))))))

;;;; Primitives and the initial Grass machine state

(define primitive-implementation-base
  '(begin
     (define prim-char-vector
       (begin
         (define (char-func i)
           `(lambda (x) (if (eq? x (vector-ref char-vector ,i)) true false)))
         (define char-func-list
           (do ((i 255 (- i 1))
                (funcs () (cons (char-func i) funcs)))
               ((< i 0) funcs)))
         (eval `(letrec ((true  (lambda (x) (lambda (y) x)))
                         (false (lambda (x) (lambda (y) y)))
                         (char-vector (vector ,@char-func-list)))
                  char-vector)
               (scheme-report-environment 5))))

     (define (chcode->lambda n)
       (vector-ref prim-char-vector n))

     (define (lambda->chcode x)
       (define (find i)
         (if (>= i 256) #f
             (if ((((chcode->lambda i) x) #t) #f) i (find (+ 1 i)))))
       (find 0))

     (define prim-w (chcode->lambda 119))

     (define (prim-succ x)
       (chcode->lambda (modulo (+ 1 (lambda->chcode x)) 256)))

     (define (prim-out x)
       (write-char (integer->char (lambda->chcode x)))
       x)

     (define (prim-in-io eof)
       (let ((c (read-char)))
         (if (eof-object? c) eof (chcode->lambda (char->integer c)))))

     (define (prim-in-string src)
       (let ((point 0))
         (lambda (eof)
           (if (>= point (string-length src)) eof
               (let* ((c (string-ref src point)))
                 (set! point (+ 1 point))
                 (chcode->lambda (char->integer c)))))))
     ))

(define (primitive-implementation . input)
  (append
   primitive-implementation-base
   `((define prim-in
       ,(if (null? input) 'prim-in-io `(prim-in-string . ,input))))))

(define initial-env
  '(prim-out prim-succ prim-w prim-in))

(define initial-dump
  '((((app 1 1)) . ())
    (() . ())))

;;;; Compile Grass to lambda calculus

(define (grass-compile-to-lambda src)
  (give-name ()
   (simulate (parse src) initial-env initial-dump)))

(define (grass-run src . input)
  (eval (append (apply primitive-implementation input)
                (list (grass-compile-to-lambda src)))
        (scheme-report-environment 5)))


;;;; for debug
;(define (test-run exp . input)
;  (eval (append (apply primitive-implementation input)
;               (list exp))
;       (scheme-report-environment 5)))
;(define (test-run-file filename . input)
;  (apply test-run
;        `(let ((f ,(call-with-input-file filename read))) (f f))
;        input))

;; grassc.scm ends here.
