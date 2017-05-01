; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "ccg/ccg" :uncertified-okp nil :dir :acl2s-modes :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "base-theory" :dir :acl2s-modes)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "custom" :dir :acl2s-modes :uncertified-okp nil :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s
(local (include-book "ihs/ihs-theories" :dir :system))

(defun myhalfadder (a b)
  (declare (type bit a b))
  (mv (xor a b) (and a b)))

(in-package "ACL2")

( INCLUDE-BOOK "ihs/basic-definitions" :dir :system)

(defun myhalfadder (a b)
  (declare (type bit a b))
  (mv (xor a b) (and a b)))

(defun myhalfadder2 (a b)
  (declare (type bit a b))
  (cons (and a b) (xor a b)))

(defun myhalfadder3 (a b)
  (declare (type bit a b))
  (mv (b-xor a b) (b-and a b)))

(defthm myhalfadder3correct
  (implies (and (bitp a) (bitp b))
  (mv-let (s c)
          (myhalfadder3 a b)
          (declare (type bit s c))
          (equal (+ a b) (+ (* 2 c) s)))))

(defun myfulladder (a b c)
  (declare (type bit a b c))
  (mv (b-xor (b-xor a b) c) (b-ior (b-ior (b-and a b) (b-and b c)) (b-and a c))))

(defthm myfulladdercorrect
  (implies (and (and (bitp a) (bitp b)) (bitp cin))
           (mv-let (s cout)
                   (myfulladder a b cin)
                   (declare (type bit s cout))
                   (equal (+ a b cin) (+ (* 2 cout) s)))))#|ACL2s-ToDo-Line|#


;; the first theorem to be proved while learning to use any theorem prover
;; sum of naturals
(defun mysum (n) 
  (if (zp n) 0
      (+ n (mysum (- n 1)))))

;;a slightly more strict version of the above
;;note I am being explicit about what input to expect for the function
(defun mysum2 (n)
  (declare (type (satisfies natp) n))
  (if (zp n) 0
    (+ n (mysum2 (- n 1)))))

;; prove that for any natural number n the sum is equal to n*(n+1)/2
(defthm mybigsigma
  (implies (natp n)
           (equal (mysum n) (/ (* n (+ n 1)) 2))))

;;it is trivial to show that both defintions are equivalent
(defthm mybigsigma2
  (implies (natp n)
           (equal (mysum n) (mysum2 n))))

;; i have to get used to the syntax of book inclusion
;; it just looks arcane
;; the first five attempts at getting acl2 to recognize bitp was a failure
(local (include-book "arithmetic/top-with-meta" :dir :system))

(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

(local (include-book "std/basic/top" :dir :system))

(local (include-book "ihs/ihs-theories" :dir :system))

;; the stuff shows my evolution in the ACL2 world
;; jumping from PVS or HOL, the syntax takes a bit getting used to

;;this first attempt at defining a half-adder is incorrect
;; xor / and won't work. Proof of it not working is in the execution
(defun myhalfadder (a b)
  (declare (type bit a b))
  (mv (xor a b) (and a b)))

;;likewise for this case
(defun myhalfadder2 (a b)
  (declare (type bit a b))
  (cons (and a b) (xor a b)))

;; this won't prove because the multi-value result doesn't have the correct form
(defthm myhalfaddercorrect
  (implies (and (bitp a) (bitp b))
  (mv-let (s c)
          (myhalfadder a b)
          (declare (type bit s c))
          (equal (+ a b) (+ (* 2 c) s)))))

;;now this works since b-xor and b-and work on bits. so they will return a 1 or 0
(defun myhalfadder3 (a b)
  (declare (type bit a b))
  (mv (b-xor a b) (b-and a b)))

;;this will prove because it uses myhalfadder3 generates a 0/1 result into each s and c
;; consequently the result is in the form expected by acl2.
(defthm myhalfadder3correct
  (implies (and (bitp a) (bitp b))
  (mv-let (s c)
          (myhalfadder3 a b)
          (declare (type bit s c))
          (equal (+ a b) (+ (* 2 c) s)))))

;; my version of the full adder
(defun myfulladder (a b c)
  (declare (type bit a b c))
  (mv (b-xor (b-xor a b) c) (b-ior (b-ior (b-and a b) (b-and b c)) (b-and a c))))

;; and it's proof of correctness
(defthm myfulladdercorrect
  (implies (and (and (bitp a) (bitp b)) (bitp cin))
           (mv-let (s cout)
                   (myfulladder a b cin)
                   (declare (type bit s cout))
                   (equal (+ a b cin) (+ (* 2 cout) s)))))

;;COMING SOON - My version of the n-bit ripple-carry adder
;; I'll have to read more about acl2 bitvectors
;; Steps
;; base case 1-bit RCA - may need to show 1-wide bit-slice satisfies bitp. trivial otherwise
;; hypothesis - k-bit RCA satisfies a[k-1:0] + b[k-1:0] + c[k-1:0]
;; step-case - k+1 bit RCA satisfies a[k:0] + b[k:0] + c[k:0]