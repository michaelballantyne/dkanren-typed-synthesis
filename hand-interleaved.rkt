#lang racket/base

(require
  "dkanren/dkanren.rkt"
  racket/pretty
  "dkanren-test.rkt" 
  )

(module+ test
  (require
    rackunit
    racket/pretty
    "dkanren-test.rkt"    
    ))


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
            (match (list expr type EI) ;; was match/lazy
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

(define (evalco expr result type)
  (dk-evalo (defs `(combined ',expr '() ',type 'I)) result))

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

  (test "list_hd"
    (time (run 1 (q)
            (synthesizec list_hd (lambda (l) : ((list) -> number)
                                         ,q)
                         [(list_hd '()) Z]
                         [(list_hd (cons Z '())) Z]
                         [(list_hd (cons (S Z) '())) (S Z)])))
    '(((match l ('() Z) ((cons _.0 _.1) _.0)))))

  
  (test "list_tl"
    (time (run 1 (q)            
            (synthesizec list_tl (lambda (l) : ((list) -> list)
                                         ,q)
                         [(list_tl '()) ()]
                         [(list_tl (cons Z '())) ()]
                         [(list_tl (cons Z (cons Z '()))) (Z)])))           
    '(((match l ('() l) ((cons _.0 _.1) _.1)))))


  (test "list_length"
    (time (run 1 (q)
            (synthesizec list_length (lambda (l) : ((list) -> number)
                                         ,q)
                         [(list_length '()) Z]
                         [(list_length (cons Z '())) (S Z)]
                         [(list_length (cons Z (cons Z '()))) (S (S Z))])))    
        '(((match l ('() Z) ((cons _.0 _.1) (S (list_length _.1)))))))


  (test "nat_iseven"
    (time (run 1 (q)
            (synthesizec nat_iseven (lambda (n) : ((number) -> number)
                                             ,q)
                         [(nat_iseven Z) (S Z)]
                         [(nat_iseven (S Z)) Z]
                         [(nat_iseven (S (S Z))) (S Z)]
                         [(nat_iseven (S (S (S Z)))) Z]
                         [(nat_iseven (S (S (S (S Z))))) (S Z)])))
    '(((match n
         (Z (S n))
         ((S _.0)
          (match _.0
            (Z _.0)
            ((S _.1) (nat_iseven _.1))))))))


  

  #;(test "list append check"
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

  #;(test "list append synth"
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

#;(module+ test
  (println "hand interleaved is fast")
  (time (length (run 12 (e v)
                     (evalco e v 'number))))

  (println "hand interleaved can handle 100 pretty fast")
  (time (length (run 100 (e v)
                     (evalco e v 'number))))

  (println "500 only a bit slower than minikanren: 10 sec rather than 6")
  (time (length (run 500 (e v)
                     (evalco e v 'number)))))
