#lang racket

(require "mk/mk.rkt")
(include "mk/test-check.scm")

(define empty-env '())

(define (lookupo x env t type)
  (fresh (y b rest)
    (== `((,y . ,b) . ,rest) env)
    (conde
      ((== x y)
       (conde
         ((== `(val ,type . ,t) b))
         ((fresh (lam-expr)
            (== `(rec ,type . ,lam-expr) b)
            (== `(closure ,lam-expr ,env) t)))))
      ((=/= x y)
       (lookupo x rest t type)))))

(define (not-in-envo x env)
  (conde
    ((== empty-env env))
    ((fresh (y b rest)
       (== `((,y . ,b) . ,rest) env)
       (=/= y x)
       (not-in-envo x rest)))))

(define (list-of-symbolso los)
  (conde
    ((== '() los))
    ((fresh (a d)
       (== `(,a . ,d) los)
       (symbolo a)
       (list-of-symbolso d)))))

(define (eval-listo expr env val type)
  (conde
    ((== '() expr)
     (== '() val))
    ((fresh (a d v-a v-d t-a t-d)
       (== `(,a . ,d) expr)
       (== `(,v-a . ,v-d) val)
       (== `(,t-a . ,t-d) type)
       (eval-expo a env v-a 'I t-a)
       (eval-listo d env v-d t-d)))))

(define (ext-env*o x* a* t* env out)
  (conde
    ((== '() x*) (== '() a*) (== env out))
    ((fresh (x a dx* da* env2 t dt*)
       (== `(,x . ,dx*) x*)
       (== `(,a . ,da*) a*)
       (== `(,t . ,dt*) t*)
       (== `((,x . (val ,t . ,a)) . ,env) env2)
       (symbolo x)
       (ext-env*o dx* da* dt* env2 out)))))

(define (evalo expr val)
  (fresh (type)
    (eval-expo expr empty-env val 'I type)))

(define (eval-expo expr env val EI type)
  (conde
    ((symbolo expr) (lookupo expr env val type))

    ((== EI 'I)
     (== type 'list)
     (fresh (e1 e2 v1 v2)
       (== `(cons ,e1 ,e2) expr)
       (== `(,v1 . ,v2) val)
       (not-in-envo 'cons env)
       (eval-expo e1 env v1 'I 'number)
       (eval-expo e2 env v2 'I 'list)))

    ((== EI 'I)
     (== type 'number)
     (fresh (e v)
       (== `(S ,e) expr)
       (== `(S ,v) val)
       (not-in-envo 'S env)
       (eval-expo e env v 'I 'number)))

    ((== EI 'I)
     (== type 'number)
     (== 'Z expr)
     (== 'Z val)
     (not-in-envo 'Z env))

    ((fresh (rator x* rands body env2 a* at* res)
       (== `(,rator . ,rands) expr)
       (eval-expo rator env `(closure (lambda ,x* ,body) ,env2) 'E `(,at* -> ,type))
       (eval-listo rands env a* at*)
       (ext-env*o x* a* at* env2 res)
       (eval-expo body res val 'I type)))

    ((== EI 'I)
     (== type 'list)
     (== '(quote ()) expr)
     (== '() val)
     (not-in-envo 'quote env))

    ((== EI 'I)
     (fresh (p-name x body letrec-body ftype)
       (== `(letrec ((,p-name (lambda ,x : ,ftype ,body)))
              ,letrec-body)
           expr)
       (list-of-symbolso x)
       (not-in-envo 'letrec env)
       (eval-expo letrec-body
                  `((,p-name . (rec ,ftype . (lambda ,x ,body))) . ,env)
                  val 'I type)))

    ((== EI 'I)
     (fresh (e1 e2 e3 v1 s1 s2)
       (== `(match ,e1
              ('() ,e2)
              ((cons ,s1 ,s2) ,e3)) expr)
       (symbolo s1)
       (symbolo s2)
       (not-in-envo 'match env)
       (eval-expo e1 env v1 'E 'list)
       (conde
         [(== '() v1)
          (eval-expo e2 env val 'I type)]
         [(fresh (a d)
            (== `(,a . ,d) v1)
            (=/= a 'closure)
            (eval-expo e3 `((,s1 . (val number . ,a)) (,s2 . (val list . ,d)) . ,env) val 'I type))])))

    ((== EI 'I)
     (fresh (e1 e2 e3 v1 s)
       (== `(match ,e1
              (Z ,e2)
              ((S ,s) ,e3)) expr)
       (symbolo s)
       (not-in-envo 'match env)
       (eval-expo e1 env v1 'E 'number)
       (conde
         [(== 'Z v1)
          (eval-expo e2 env val 'I type)]
         [(fresh (d)
            (== `(S ,d) v1)
            (eval-expo e3 `((,s . (val number . ,d)) . ,env) val 'I type))])))

    ((== EI 'I)
     (fresh (e1 e2 e3 e4 v1 v2)
       (== `(if (= ,e1 ,e2)
              ,e3
              ,e4) expr)
       (not-in-envo 'if env)
       (eval-expo e1 env v1 'E 'number)
       (eval-expo e2 env v2 'E 'number)
       (conde
         [(== v1 v2)
          (eval-expo e3 env val 'I type)]
         [(=/= v1 v2)
          (eval-expo e4 env val 'I type)])
       ))))

(time
  (pretty-print
    (run 500 (e v)
         (eval-expo e '() v 'I 'number))))

