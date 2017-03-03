#lang racket/base
(require
  "dkanren.rkt"
  )

(module+ test
  (require
    rackunit
    racket/pretty
    )

  (define-syntax test
    (syntax-rules ()
     ((_ name expr expected)
      (let ((actual expr))
        (when (not (equal? actual expected))
          (display name)
          (newline)
          (pretty-print actual)
          (newline))
        (check-equal? actual expected)))))

  (define-syntax test-time
    (syntax-rules ()
      ((_ test-name query expected)
        (begin
          (displayln test-name)
          (time (test test-name query expected))))))

  (define-syntax test-any
    (syntax-rules ()
     ((_ name expr expecteds)
      (let* ((actual expr)
             (found (member actual expecteds))
             (expected (if (null? found) (car expecteds) (car found))))
        (test name actual expected)))))
  (define-syntax test-time-any
    (syntax-rules ()
     ((_ name body ...)
      (begin
        (displayln name)
        (time (test-any name body ...)))))))


(define (defs body)
  `(letrec
     ((in-env? (lambda (x env)
                 (match env
                   ('() #f)
                   (`((,a . ,_) . ,d)
                     (or (equal? x a) (in-env? x d))))))
      (list-of-symbols?
        (lambda (l)
          (match l
            ['() #t]
            [(cons (symbol) d) (list-of-symbols? d)])))
      (lookupe
        (lambda (x env)
          (match env
            (`((,y . ,v) . ,rest)
              (if (equal? x y)
                (match v
                  (`(val ,v) v)
                  (`(rec ,lam) `(closure ,lam ,env)))
                (lookupe x rest))))))
      (eval*
        (lambda (x* env)
          (match x*
            ('() '())
            ((cons a d)
             (cons (eval a env)
                   (eval* d env))))))
      (ext-env*
        (lambda (x* v* env)
          (match (cons x* v*)
            ('(() . ())
             env)
            (`((,x . ,x*) . (,v . ,v*))
             `((,x . (val ,v)) . ,(ext-env* x* v* env)))
          )))
      (eval
        (lambda (expr env)
          (let ((free? (lambda (sym) (not (in-env? sym env)))))
            (match/lazy expr
              ; Z
              ((and 'Z (? free?))
                'Z)
              ; ref
              ((symbol) (lookupe expr env))
              ; cons
              (`(,(and 'cons (? free?)) ,e1 ,e2)
                (cons (eval e1 env)
                      (eval e2 env)))
              ; S
              (`(,(and 'S (? free?)) ,e)
                `(S ,(eval e env)))
              ; quote
              (`(,(and 'quote (? free?)) ())
                '())
              ; letrec
              (`(,(and 'letrec (? free?))
                  ((,p-name (lambda ,(and x (? list-of-symbols?)) : ,ftype ,body)))
                  ,letrec-body)
               (eval letrec-body
                     `((,p-name . (rec (lambda ,x ,body))) . ,env)))
              ; match list
              (`(,(and 'match (? free?)) ,e1
                  ('() ,e2)
                  ((cons ,s1 ,s2) ,e3))
                (let ((v1 (eval e1 env)))
                  (match v1
                    (`()
                      (eval e2 env))
                    (`(,a . ,d)
                      (eval e3 `((,s1 . (val ,a)) (,s2 . (val ,d)) . ,env))))))
              ; match number
              (`(,(and 'match (? free?)) ,e1
                  (Z ,e2)
                  ((S ,s) ,e3))
                (let ((v1 (eval e1 env)))
                  (match v1
                    (`Z (eval e2 env))
                    (`(S ,vs) (eval e3 `((,s . (val ,vs)) . ,env))))))
              ; if
              (`(,(and 'if (? free?)) (= ,e1 ,e2)
                  ,e3
                  ,e4)
                (if (equal? (eval e1 env) (eval e2 env))
                  (eval e3 env)
                  (eval e4 env)))
              ; application
              (`(,e . ,e*)
                (let ((v (eval e env))
                      (v* (eval* e* env)))
                  (match v
                    (`(closure (lambda ,x* ,body) ,env^)
                      (eval body (ext-env* x* v* env^))))))
              ))))
      (lookupt
        (lambda (x env)
          (match env
            (`((,y . ,v) . ,rest)
              (if (equal? x y)
                v
                (lookupt x rest))))))
      (check-rands
        (lambda (rands env types)
          (match `(,rands . ,types)
            (`(() . ()) #t)
            (`((,r1 . ,rr) . (,t1 . ,tr))
              (and
                (tc r1 env t1 'I)
                (check-rands rr env tr)))
            (e #f))))
      (ext-envt*
        (lambda (x* v* env)
          (match (cons x* v*)
            ('(() . ())
             env)
            (`((,x . ,x*) . (,v . ,v*))
              `((,x . ,v) . ,(ext-envt* x* v* env))))))
      (tc
        (lambda (expr env type EI)
          (let ((free? (lambda (sym) (not (in-env? sym env)))))
            (match/lazy (list expr type EI)
              ; Z
              (`(,(and 'Z (? free?)) number I)
               #t)
              ; ref
              (`(,(symbol) ,type ,EI) (equal? type (lookupt expr env)))
              ; cons
              (`((,(and 'cons (? free?)) ,e1 ,e2) list I)
                (and
                  (tc e1 env 'number 'I)
                  (tc e2 env 'list 'I)))
              ; S
              (`((,(and 'S (? free?)) ,e) number I)
                (tc e env 'number 'I))
              ; quote
              (`((,(and 'quote (? free?)) ()) list I)
                #t)
              ; letrec
              (`((,(and 'letrec (? free?))
                  ((,p-name (lambda ,x : (,a*type -> ,rtype) ,body)))
                  ,letrec-body)
                 ,type I)
                (let ((env^ `((,p-name . (,a*type -> ,rtype)) . ,env)))
                  (and
                    (tc body (ext-envt* x a*type env^) rtype 'I)
                    (tc letrec-body env^ type 'I))))
              ; match list
              (`((,(and 'match (? free?)) ,e1
                  ('() ,e2)
                  ((cons ,s1 ,s2) ,e3))
                 ,type I)
                (and
                  (tc e1 env 'list 'E)
                  (tc e2 env type 'I)
                  (tc e3 `((,s1 . number) (,s2 . list) . ,env) type 'I)))
              ; match number
              (`((,(and 'match (? free?)) ,e1
                  (Z ,e2)
                  ((S ,s) ,e3))
                 ,type I)
                (and
                  (tc e1 env 'number 'E)
                  (tc e2 env type 'I)
                  (tc e3 `((,s . number) . ,env) type 'I)))
              ; if
              (`((,(and 'if (? free?)) (= ,e1 ,e2)
                  ,e3
                  ,e4)
                 ,type I)
                (and
                  (tc e1 env 'number 'E)
                  (tc e2 env 'number 'E)
                  (tc e3 env type 'I)
                  (tc e4 env type 'I)))
              ; application
              (`((,rator . ,rands) ,type ,EI)
                (fresh (ftype)
                  (match ftype
                    (`(,at* -> ,rtype)
                      (and
                        (equal? rtype type)
                        (and
                          (tc rator env ftype 'E)
                          (check-rands rands env at*)))))))
              ))))
      (tc+eval
        (lambda (expr type)
          (match (eval expr '())
            (v (match (tc expr '() type 'I)
                 (#t v))))))
      (lookupc
        (lambda (x env)
          (match env
            (`((,y . ,v) . ,rest)
              (if (equal? x y)
                (match v
                  (`(val ,t ,v) (cons v t))
                  (`(rec ,t ,lam) (cons `(closure ,lam ,env) t)))
                (lookupc x rest))))))
      (evalc*
        (lambda (x* env at*)
          (match (list x* at*)
            ('(() ()) '())
            (`((,x . ,x*) (,at . ,at*))
              (cons (combined x env at 'I)
                    (evalc* x* env at*))))))
      (ext-envc*
        (lambda (x* v* t* env)
          (match (list x* v* t*)
            ('(() () ())
             env)
            (`((,x . ,x*) (,v . ,v*) (,t . ,t*))
             `((,x . (val ,t ,v)) . ,(ext-envc* x* v* t* env))))))
      (combined
        (lambda (expr env type EI)
          (let ((free? (lambda (sym) (not (in-env? sym env))))
                (bound? (lambda (sym) (in-env? sym env)))
                (bound-if-sym? (lambda (sym) (or (not (symbol? sym)) (in-env? sym env)))))
            (match/lazy (list expr type EI)
              ; ref
              (`(,(? bound?) ,_ ,_)
                (match (lookupc expr env)
                  ((cons val reftype)
                   (match (equal? type reftype)
                     (#t val)))))
              ; cons
              (`((,(and 'cons (? free?)) ,e1 ,e2) list I)
                (cons (combined e1 env 'number 'I)
                      (combined e2 env 'list 'I)))
              ; S
              (`((,(and 'S (? free?)) ,e) number I)
                `(S ,(combined e env 'number 'I)))
              ; Z
              (`(,(and 'Z (? free?)) number I)
                'Z)
              ; application
              (`((,(and e (? bound-if-sym?)) . ,e*) ,type ,EI)
                (fresh (ftype)
                  (match ftype
                    (`(,at* -> ,rtype)
                      (match (equal? rtype type)
                        (#t
                         (let ((v (combined e env ftype 'E))
                               (v* (evalc* e* env at*)))
                           (match v
                             (`(closure (lambda ,x* ,body) ,env^)
                               (combined body (ext-envc* x* v* at* env^) type 'I))))))))))
              ; quote
              (`((,(and 'quote (? free?)) ()) list I)
                '())
              ; letrec
              (`((,(and 'letrec (? free?))
                  ((,p-name (lambda ,x : (,a*type -> ,rtype) ,body)))
                  ,letrec-body)
                 ,type I)
               (combined letrec-body
                         `((,p-name . (rec (,a*type -> ,rtype) (lambda ,x ,body))) . ,env)
                         type 'I))
              ; match list
              (`((,(and 'match (? free?)) ,e1
                  ('() ,e2)
                  ((cons ,s1 ,s2) ,e3))
                 ,type I)
                (let ((v1 (combined e1 env 'list 'E)))
                  (match v1
                    (`()
                      (combined e2 env type 'I))
                    (`(,a . ,d)
                      (combined e3 `((,s1 . (val number ,a)) (,s2 . (val list ,d)) . ,env) type 'I)))))
              ; match number
              (`((,(and 'match (? free?)) ,e1
                  (Z ,e2)
                  ((S ,s) ,e3))
                 ,type I)
                (let ((v1 (combined e1 env 'number 'E)))
                  (match v1
                    (`Z (combined e2 env type 'I))
                    (`(S ,vs) (combined e3 `((,s . (val number ,vs)) . ,env) type 'I)))))
              ; if
              (`((,(and 'if (? free?)) (= ,e1 ,e2)
                  ,e3
                  ,e4)
                 ,type I)
                (if (equal? (combined e1 env 'number 'E) (combined e2 env 'number 'E))
                  (combined e3 env type 'I)
                  (combined e4 env type 'I)))
              ))))
      )
     ,body))


(define (tco expr type)
  (dk-evalo (defs `(tc ',expr '() ',type 'I)) #t))

(define (eval-no-tco expr result)
  (fresh (type)
    (dk-evalo (defs `(eval ',expr '())) result)))

(define (evalo expr result)
  (fresh (type)
    (dk-evalo (defs `(tc+eval ',expr ',type)) result)))

(define (eval+typeo expr result type)
  (dk-evalo (defs `(tc+eval ',expr ',type)) result))

(define (evalco expr result type)
  (dk-evalo (defs `(combined ',expr '() ',type 'I)) result))

; Basic functionality tests of dkanren interleaved evaluator and checker
(module+ test
  (test "numbers"
    (run* (v t) (eval+typeo '(S (S Z)) v t))
    '(((S (S Z)) number)))

  (test "null"
    (run* (v t) (eval+typeo ''() v t))
    '((() list)))

  (test "lists"
    (run* (v t) (eval+typeo '(cons Z (cons (S Z) (cons (S (S Z)) '()))) v t))
    '(((Z (S Z) (S (S Z))) list)))

  ; these aren't legal with the EI restrictions.

  ;(test "match Z"
    ;(run* (v t)
      ;(eval+typeo
        ;'(match Z
           ;(Z (S (S Z)))
           ;((S r) r))
        ;v t))
    ;'(((S (S Z)) number)))

  ;(test "match (S Z)"
    ;(run* (v t)
      ;(eval+typeo
        ;'(match (S (S Z))
           ;(Z Z)
           ;((S r) r))
        ;v t))
    ;'(((S Z) number)))

  ;(test "match '()"
    ;(run* (v t)
      ;(eval+typeo
        ;'(match '()
           ;('() Z)
           ;((cons a d) (S Z)))
        ;v t))
    ;'((Z number)))

  ;(test "match (cons a d) a"
    ;(run* (v t)
      ;(eval+typeo
        ;'(match (cons Z '())
           ;('() Z)
           ;((cons a d) a))
        ;v t))
    ;'((Z number)))

  ;(test "match (cons a d) d"
    ;(run* (v t)
      ;(eval+typeo
        ;'(match (cons Z '())
           ;('() (cons Z '()))
           ;((cons a d) d))
        ;v t))
    ;'((() list)))

  ;(test "if true"
    ;(run* (v t)
      ;(eval+typeo
        ;'(if (= (S Z) (S Z))
           ;(S Z)
           ;Z)
        ;v t))
    ;'(((S Z) number)))

  ;(test "if false"
    ;(run* (v t)
      ;(eval+typeo
        ;'(if (= (S (S Z)) (S Z))
           ;(S Z)
           ;Z)
        ;v t))
    ;'((Z number)))

  (test "letrec"
    (run* (v t)
      (eval+typeo
        '(letrec ((f (lambda (n1) : ((number) -> number)
                       n1)))
           f)
        v t))
    '(((closure (lambda (n1) n1)
                ((f rec (lambda (n1) n1))))
       ((number) -> number))))

  (test "call"
    (run* (v t)
      (eval+typeo
        '(letrec ((f (lambda (n1) : ((number) -> number)
                       n1)))
           (f Z))
        v t))
    '((Z number)))

  (test "call 2 args"
    (run* (v t)
      (eval+typeo
        '(letrec ((f (lambda (n1 n2) : ((number number) -> number)
                       n1)))
           (f Z (S Z)))
        v t))
    '((Z number)))

  (test "max function 1"
    (run* (v t)
      (eval+typeo
        '(letrec ((max (lambda (n1 n2) : ((number number) -> number)
                         (match n1
                           (Z n2)
                           ((S a)
                            (S (match n2
                                 (Z a)
                                 ((S b) (max b a)))))))))
           (max (S Z) (S (S Z))))
        v t))
    '(((S (S Z)) number)))

  (test "max function 2"
    (run* (v t)
      (eval+typeo
        '(letrec ((max (lambda (n1 n2) : ((number number) -> number)
                         (match n1
                           (Z n2)
                           ((S a)
                            (S (match n2
                                 (Z a)
                                 ((S b) (max b a)))))))))
           (max (S (S Z)) (S Z)))
        v t))
    '(((S (S Z)) number)))
  )

(define-syntax-rule (synthesize fn lam [call out] ...)
    (fresh ()
      (evalo
        `(letrec ((fn lam))
           call)
        `out)
      ...))

; Synthesis tests of dkanren interleaved evaluator and checker
(module+ test

  ; Checks ok
  (test "list append check"
    (run 1 (q)
         (== q '(match l
                  ('() s)
                  ((cons _.0 _.1) (cons _.0 (append _.1 s)))))
         (synthesize
           append (lambda (l s) : ((list list) -> list)
                    ,q)
           [(append '() '()) ()]
           [(append '() (cons Z '())) (Z)]
           [(append (cons Z '()) '()) (Z)]
           [(append (cons Z '()) (cons Z '())) (Z Z)]
           [(append (cons (S Z) (cons Z '())) '()) ((S Z) Z)]
           [(append (cons (S Z) (cons Z '())) (cons Z '())) ((S Z) Z Z)]

           [(append (cons (S (S Z)) (cons (S Z) (cons Z '()))) '()) ((S (S Z)) (S Z) Z)]
           ))
    '(((match l ((quote ()) s) ((cons _.0 _.1) (cons _.0 (append _.1 s)))))))

  ; But doesn't synthesize.
  #;(test "list append synth"
    (run 1 (q)
         ;(== q '(match l
                  ;('() s)
                  ;((cons _.0 _.1) (cons _.0 (append _.1 s)))))
         (synthesize
           append (lambda (l s) : ((list list) -> list)
                    ,q)
           [(append '() '()) ()]
           [(append '() (cons Z '())) (Z)]
           [(append (cons Z '()) '()) (Z)]
           [(append (cons Z '()) (cons Z '())) (Z Z)]
           [(append (cons (S Z) (cons Z '())) '()) ((S Z) Z)]
           [(append (cons (S Z) (cons Z '())) (cons Z '())) ((S Z) Z Z)]

           [(append (cons (S (S Z)) (cons (S Z) (cons Z '()))) '()) ((S (S Z)) (S Z) Z)]
           ))
    '(((match l ((quote ()) s) ((cons _.0 _.1) (cons _.0 (append _.1 s)))))))

  ; Another synthesis that doesn't work.
  #;(test "max function synth"
    (run 1 (q)
         #;(== q '(match n1
                  (Z n2)
                  ((S _.0)
                   (S (match n2
                        (Z _.0)
                        ((S _.1) (max _.1 _.0)))))))
         (synthesize
           max (lambda (n1 n2) : ((number number) -> number)
                 ,q)
           [(max Z Z) Z]
           [(max Z (S Z)) (S Z)]
           [(max Z (S (S Z))) (S (S Z))]

           [(max (S Z) Z) (S Z)]
           [(max (S Z) (S Z)) (S Z)]
           [(max (S Z) (S (S Z))) (S (S Z))]

           [(max (S (S Z)) Z) (S (S Z))]
           [(max (S (S Z)) (S Z)) (S (S Z))]
           [(max (S (S Z)) (S (S Z))) (S (S Z))]
           ))
    '(((match n1
         (Z n2)
         ((S _.0)
          (S (match n2
               (Z _.0)
               ((S _.1) (max _.1 _.0)))))))))

  )

; Basic functionality tests of hand-interleaved version
(module+ test
  (test "numbers"
    (run* (v t) (evalco '(S (S Z)) v t))
    '(((S (S Z)) number)))

  (test "null"
    (run* (v t) (evalco ''() v t))
    '((() list)))

  (test "lists"
    (run* (v t) (evalco '(cons Z (cons (S Z) (cons (S (S Z)) '()))) v t))
    '(((Z (S Z) (S (S Z))) list)))

  (test "letrec"
    (run* (v t)
      (evalco
        '(letrec ((f (lambda (n1) : ((number) -> number)
                       n1)))
           f)
        v t))
    '(((closure (lambda (n1) n1)
                ((f rec ((number) -> number) (lambda (n1) n1))))
       ((number) -> number))))

  (test "call"
    (run* (v t)
      (evalco
        '(letrec ((f (lambda (n1) : ((number) -> number)
                       n1)))
           (f Z))
        v t))
    '((Z number)))

  (test "call 2 args"
    (run* (v t)
      (evalco
        '(letrec ((f (lambda (n1 n2) : ((number number) -> number)
                       n1)))
           (f Z (S Z)))
        v t))
    '((Z number)))

  (test "max function 1"
    (run* (v t)
      (evalco
        '(letrec ((max (lambda (n1 n2) : ((number number) -> number)
                         (match n1
                           (Z n2)
                           ((S a)
                            (S (match n2
                                 (Z a)
                                 ((S b) (max b a)))))))))
           (max (S Z) (S (S Z))))
        v t))
    '(((S (S Z)) number)))

  (test "max function 2"
    (run* (v t)
      (evalco
        '(letrec ((max (lambda (n1 n2) : ((number number) -> number)
                         (match n1
                           (Z n2)
                           ((S a)
                            (S (match n2
                                 (Z a)
                                 ((S b) (max b a)))))))))
           (max (S (S Z)) (S Z)))
        v t))
    '(((S (S Z)) number)))
  )

(define-syntax-rule (synthesizec fn lam [call out] ...)
    (fresh (type)
      (evalco
        `(letrec ((fn lam))
           call)
        `out
        type)
      ...))

; Synthesis and performance tests of hand interleaved version
(module+ test

  (println "hand interleaved is fast")
  (time (length (run 12 (e v)
             (evalco e v 'number))))

  (println "interleaved by dkanren is not")
  (time (length (run 12 (e v)
             (eval+typeo e v 'number))))

  (println "hand interleaved can handle 100 pretty fast")
  (time (length (run 100 (e v)
             (evalco e v 'number))))

  (println "500 only a bit slower than minikanren: 10 sec rather than 6")
  (time (length (run 500 (e v)
             (evalco e v 'number))))


  (test "list append check"
    (run 1 (q)
         (== q '(match l
                  ('() s)
                  ((cons _.0 _.1) (cons _.0 (append _.1 s)))))
         (absento 'S q)
         (synthesizec
           append (lambda (l s) : ((list list) -> list)
                    ,q)
           [(append '() '()) ()]
           [(append '() (cons Z '())) (Z)]
           [(append (cons Z '()) '()) (Z)]
           [(append (cons Z '()) (cons Z '())) (Z Z)]
           [(append (cons (S Z) (cons Z '())) '()) ((S Z) Z)]
           [(append (cons (S Z) (cons Z '())) (cons Z '())) ((S Z) Z Z)]

           [(append '() (cons Z (cons (S Z) '()))) (Z (S Z))]
           [(append (cons Z (cons (S Z) (cons (S (S Z)) '()))) (cons (S (S (S Z))) (cons (S (S (S (S Z)))) '()))) (Z (S Z) (S (S Z)) (S (S (S Z))) (S (S (S (S Z)))))]
           ))
    '(((match l ((quote ()) s) ((cons _.0 _.1) (cons _.0 (append _.1 s)))))))

  (println "synthesis still doesn't work. :(  The miniKanren version works in 145ms.")
  (test "list append synth"
    (run 1 (q)
         ;(== q '(match l
                  ;('() s)
                  ;((cons _.0 _.1) (cons _.0 (append _.1 s)))))
         (absento 'S q)
         (synthesizec
           append (lambda (l s) : ((list list) -> list)
                    ,q)
           [(append '() '()) ()]
           [(append '() (cons Z '())) (Z)]
           [(append (cons Z '()) '()) (Z)]
           [(append (cons Z '()) (cons Z '())) (Z Z)]
           [(append (cons (S Z) (cons Z '())) '()) ((S Z) Z)]
           [(append (cons (S Z) (cons Z '())) (cons Z '())) ((S Z) Z Z)]

           [(append '() (cons Z (cons (S Z) '()))) (Z (S Z))]
           [(append (cons Z (cons (S Z) (cons (S (S Z)) '()))) (cons (S (S (S Z))) (cons (S (S (S (S Z)))) '()))) (Z (S Z) (S (S Z)) (S (S (S Z))) (S (S (S (S Z)))))]
           ))
    '(((match l ((quote ()) s) ((cons _.0 _.1) (cons _.0 (append _.1 s)))))))

  #;(test "max function synth"
    (run 1 (q)
         #;(== q '(match n1
                  (Z n2)
                  ((S _.0)
                   (S (match n2
                        (Z _.0)
                        ((S _.1) (max _.1 _.0)))))))
         (synthesizec
           max (lambda (n1 n2) : ((number number) -> number)
                 ,q)
           [(max Z Z) Z]
           [(max Z (S Z)) (S Z)]
           [(max Z (S (S Z))) (S (S Z))]

           [(max (S Z) Z) (S Z)]
           [(max (S Z) (S Z)) (S Z)]
           [(max (S Z) (S (S Z))) (S (S Z))]

           [(max (S (S Z)) Z) (S (S Z))]
           [(max (S (S Z)) (S Z)) (S (S Z))]
           [(max (S (S Z)) (S (S Z))) (S (S Z))]
           ))
    '(((match n1
         (Z n2)
         ((S _.0)
          (S (match n2
               (Z _.0)
               ((S _.1) (max _.1 _.0)))))))))
  )

