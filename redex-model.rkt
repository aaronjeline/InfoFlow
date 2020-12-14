#lang racket
(require redex redex/pict)

(define-language Imp
  (n ::= number)
  (v ::= ((n label) (true label) (false label)))
  (label ::= Public Secret)
  (id ::= variable-not-otherwise-mentioned)
  (aexp ::=
      n id
      (aexp + aexp)
      (aexp - aepx)
      (aexp * aexp))
  (bexp ::=
        true false
        (aexp = aexp)
        (aexp ≤ aexp)
        (not bexp)
        (bexp && bexp))
  
  (com ::=
       skip
       (id := aexp label)
       (seq ::= com : com)
       (if bexp com com)))

(define-judgment-form Imp
  #:mode (MapsTo I O I)
  [(MapsTo x 0 s)])
  

(define-judgment-form Imp
  #:mode (aevalR I I O)
  [(aevalR n State (n Public))]
  [(MapsTo id (v l) State)
   -----
   (aevalR id State (v l))]
  [(aevalR a1 State (v1 l2))
   (aevalR a2 State (v2 l2))
   ------
   (aevalR (a1 + a2) State ((v1 + v2) (merge l1 l2)))
   ]
 [(aevalR a1 State (v1 l2))
   (aevalR a2 State (v2 l2))
   ------
   (aevalR (a1 - a2) State ((v1 - v2) (merge l1 l2)))
   ]
   [(aevalR a1 State (v1 l2))
   (aevalR a2 State (v2 l2))
   ------
   (aevalR (a1 * a2) State ((v1 * v2) (merge l1 l2)))
   ])

(render-language Imp "/tmp/Imp.ps")
(render-judgment-form aevalR "/tmp/aeval.ps")
  