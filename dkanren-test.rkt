#lang racket

(require rackunit)
(provide (all-defined-out))

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
       (time (test-any name body ...))))))
