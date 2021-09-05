(in-package #:murakami-nasako)

(defvar *random*)

(defmacro with-secure-random ((&optional (path #P"/dev/urandom")) &body body)
  (with-gensyms (random)
    `(let* ((,random (open ,path :element-type '(unsigned-byte 8) :if-does-not-exist :error))
            (*random* ,random))
       (unwind-protect
            (progn ,@body)
         (close ,random)))))

(defun secure-random (limit)
  (multiple-value-bind (n-bytes n-top-bits) (ceiling (integer-length (- limit 1)) 8)
    (let ((bytes (make-array n-bytes :element-type '(unsigned-byte 8)))
          (rand-num 0))
      (loop
        :do
           (assert (= (read-sequence bytes *random*) (length bytes)))
           (setf
            (aref bytes (- (length bytes) 1))
            (ldb (byte (+ n-top-bits 8) 0) (aref bytes (- (length bytes) 1)))
            rand-num
            (reduce (lambda (b n) (+ (* 256 n) b)) bytes :from-end t :initial-value 0))
        :when (< rand-num limit)
          :return rand-num))))

(defun test-random (limit n)
  (with-secure-random ()
    (let ((arr (make-array limit :initial-element 0)))
      (loop :repeat n
            :do (incf (aref arr (secure-random limit))))
      arr)))

(defun binary-search (value array &optional (start 0) (end (length array)))
  (let ((low start)
        (high (1- end)))
    (do () ((< high low) (values low nil))
      (let ((middle (floor (+ low high) 2)))
        (cond ((> (aref array middle) value)
               (setf high (1- middle)))
 
              ((< (aref array middle) value)
               (setf low (1+ middle)))
 
              (t (return (values middle t))))))))

;;
;; Calculates the GCD of a and b based on the Extended Euclidean Algorithm. The function also returns
;; the Bézout coefficients s and t, such that gcd(a, b) = as + bt.
;;
;; The algorithm is described on page http://en.wikipedia.org/wiki/Extended_Euclidean_algorithm#Iterative_method_2
;;
(defun egcd (a b)
  (do ((r (cons b a) (cons (- (cdr r) (* (car r) q)) (car r))) ; (r+1 r) i.e. the latest is first.
       (s (cons 0 1) (cons (- (cdr s) (* (car s) q)) (car s))) ; (s+1 s)
       (u (cons 1 0) (cons (- (cdr u) (* (car u) q)) (car u))) ; (t+1 t)
       (q nil))
      ((zerop (car r)) (values (cdr r) (cdr s) (cdr u)))       ; exit when r+1 = 0 and return r s t
    (setq q (floor (/ (cdr r) (car r))))))                     ; inside loop; calculate the q

;;
;; Calculates the inverse module for a = 1 (mod m). 
;;
;; Note: The inverse is only defined when a and m are coprimes, i.e. gcd(a, m) = 1.”
;;
(defun invmod (a m)
  (multiple-value-bind (r s k) (egcd a m)
    (unless (= 1 r) (error "invmod: Values ~a and ~a are not coprimes." a m))  
    s))

(defun chinese-remainder (am)
"Calculates the Chinese Remainder for the given set of integer modulo pairs.
 Note: All the ni and the N must be coprimes."
  (loop :for (a . m) :in am
        :with mtot = (reduce #'* (mapcar #'(lambda(X) (cdr X)) am))
        :with sum  = 0
        :finally (return (mod sum mtot))
        :do
           (incf sum (* a (invmod (/ mtot m) m) (/ mtot m)))))

(defmacro auntil (condition &body body)
  `(do ((it (progn ,@body) (progn ,@body)))
       (,condition it)))

(defun nshuffle (vec)
  (loop :for i :from (length vec) :downto 2
        do (rotatef (aref vec (secure-random i))
                    (aref vec (1- i))))
  vec)

(defvar *s-p-q-random-amount* (expt 2 8)
  "The limit for the random numbers generated for s^(P) and s^(Q) in
  MAKE-KEY")

(defclass key ()
  (((key-length :initarg :key-length :accessor key-length)
    (sp :initarg :sp :accessor sp)
    (sq :initarg :sq :accessor sq)
    (h :initarg :h :accessor h)
    (l :initarg :l :accessor l)
    (p :initarg :p :accessor p)
    (q :initarg :q :accessor q)
    (permutation :initarg :permutation :accessor permutation)
    (public-key :initarg :public-key :accessor public-key))))

(defun make-key (n)
  (let ((u (floor n 2))
        (s (make-array n))
        (sp (make-array n))
        (sq (make-array n))
        (h (make-array n))
        (l (make-array n))
        (h-len 0)
        (l-len 0))
    (loop :for i :from 0 :below n
          :do (cond
                ((= (secure-random 2) 0)
                 (setf (aref h h-len) i)
                 (incf h-len))
                (t
                 (setf (aref l l-len) i)
                 (incf l-len))))
    (let ((alpha-u+1 (binary-search (+ u 1) l 0 l-len))
          (h-ind (- h-len 1))
          (l-ind (- l-len 1))
          (p 0)
          (q 0)
          (sp-sum 0)
          (sq-sum 0))
      (loop :for i :from (- n 1) :downto u
            :for i-in-h-p
              := (cond
                   ((= (aref h h-ind) i)
                    ;; Avoid setting h-ind below 0
                    (setf h-ind (max 0 (- h-ind 1)))
                    t)
                   ((= (aref l l-ind) i)
                    ;; Avoid setting l-ind below 0
                    (setf l-ind (max 0 (- l-ind 1)))
                    nil)
                   (t
                    (error (format nil "Index ~A not in h or l" i))))
            :for f-val := (- (binary-search i l 0 l-len) alpha-u+1)
            :do (setf (aref sp i)
                      (ash (logior 1 (secure-random *s-p-q-random-amount*)) alpha-u+1)
                      (aref sq i)
                      (if i-in-h-p
                          (+
                           (ash (+ 1 (secure-random *s-p-q-random-amount*)) f-val)
                           ;; Must be greater than the sum of all sq so far
                           (logand sq-sum (lognot (- (ash 1 f-val) 1))))
                          (ash (logior 1 (secure-random *s-p-q-random-amount*)) f-val)))
                (incf sp-sum (aref sp i))
                (incf sq-sum (aref sq i)))
      (loop :for i :from (- u 1) :downto 0
            :for i-in-h-p
              := (cond
                   ((= (aref h h-ind) i)
                    ;; Avoid setting h-ind below 0
                    (setf h-ind (max 0 (- h-ind 1)))
                    t)
                   ((= (aref l l-ind) i)
                    ;; Avoid setting l-ind below 0
                    (setf l-ind (max 0 (- l-ind 1)))
                    nil)
                   (t
                    (error (format nil "Index ~A not in h or l" i))))
            :for f-val := (binary-search i l 0 l-len)
            :do (setf (aref sp i)
                      (if i-in-h-p
                          ;; Must also be greater than the sum of all sp so far
                          (+
                           (ash (+ 1 (secure-random *s-p-q-random-amount*)) f-val)
                           (logand sp-sum (lognot (- (ash 1 f-val) 1))))
                          (ash (logior 1 (secure-random *s-p-q-random-amount*)) f-val))
                      (aref sq i)
                      (secure-random *s-p-q-random-amount*))
                (incf sp-sum (aref sp i))
                (incf sq-sum (aref sq i)))
      (setf
       (values p q)
       (loop :for p := (+ sp-sum
                          (secure-random (ash 1 (+ (integer-length n) 50)))
                          (ash 1 (+ (integer-length n) 20)))
             :for q := (+ sq-sum
                          (secure-random (ash 1 (+ (integer-length n) 50)))
                          (ash 1 (+ (integer-length n) 20)))
             :when (= (gcd p q) 1)
               :return (values p q)))
      (loop :for i :from 0 :below n
            :do (setf (aref s i) (chinese-remainder `((,(aref sp i) . ,p) (,(aref sq i) . ,q)))))
      (let ((perm (make-array n))
            (public-key (make-array n)))
        (loop :for i :below n
              :do (setf (aref perm i) i))
        (nshuffle perm)
        (loop :for i :below (length perm)
              :do (setf (aref public-key (aref perm i)) (aref s i)))
        (make-instance
         'key
         :key-length n
         :sp sp
         :sq sq
         :h (subseq h 0 h-len)
         :l (subseq l 0 l-len)
         :p p
         :q q
         :permutation perm
         :public-key public-key)))))

(defun encrypt (bits key)
  (assert (<= (length bits) (length key)))
  (loop :for bit :across bits
        :for elem :across key
        :summing (* bit elem)))

(defun trailing-zeroes (n)
  (if (= n 0)
      0
      (loop :for i :upfrom 0
            :when (logbitp i n)
              :return i)))

(defun decrypt (c key)
  (with-slots (h l sp sq p q permutation key-length) key
   (let ((u (floor key-length 2))
         (cp (mod c p))
         (cq (mod c q))
         (msg-hat (make-array key-length :element-type 'bit))
         (msg (make-array key-length :element-type 'bit))
         (h-ind 0)
         (l-ind 0))
     (loop
       :for i :from 0 :below u
       :for i-in-h-p
         := (cond
              ((= (aref h h-ind) i)
               ;; Avoid setting h-ind outside h
               (setf h-ind (min (- (length h) 1) (+ h-ind 1)))
               t)
              ((= (aref l l-ind) i)
               ;; Avoid setting l-ind outside l
               (setf l-ind (min (- (length l) 1) (+ l-ind 1)))
               nil)
              (t
               (error (format nil "Index ~A not in h or l" i))))
       :do
          (setf (sbit msg-hat i)
                (if i-in-h-p
                    (if (>= cp (aref sp i))
                        1
                        0)
                    (if (= (trailing-zeroes cp) (trailing-zeroes (aref sp i)))
                        1
                        0))
                cp (- cp (* (sbit msg-hat i) (aref sp i)))
                cq (- cq (* (sbit msg-hat i) (aref sq i)))))
     (loop
       :for i :from u :below key-length
       :for i-in-h-p
         := (cond
              ((= (aref h h-ind) i)
               ;; Avoid setting h-ind outside h
               (setf h-ind (min (- (length h) 1) (+ h-ind 1)))
               t)
              ((= (aref l l-ind) i)
               ;; Avoid setting l-ind outside l
               (setf l-ind (min (- (length l) 1) (+ l-ind 1)))
               nil)
              (t
               (error (format nil "Index ~A not in h or l" i))))
       :do
          (setf (sbit msg-hat i)
                (if i-in-h-p
                    (if (>= cq (aref sq i))
                        1
                        0)
                    (if (= (trailing-zeroes cq) (trailing-zeroes (aref sq i)))
                        1
                        0))
                cp (- cp (* (sbit msg-hat i) (aref sp i)))
                cq (- cq (* (sbit msg-hat i) (aref sq i)))))
     (assert (= (mod cp p) (mod cq q) 0) () "Invalid ciphertext")
     (loop :for i :below (length permutation)
           :do (setf (sbit msg (aref permutation i)) (sbit msg-hat i)))
     msg)))
