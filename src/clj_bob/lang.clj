(ns clj-bob.lang
  (:refer-clojure :exclude [atom cons + < num if])
  (:require [clojure.string :as str]))

(defn if-nil [q a e]
  (if (or (nil? q)
          (= 'nil q))
    (e)
    (a)))

(defn if
  [Q A E]
  (if-nil Q
          (fn [] A)
          (fn [] E)))

(defrecord Pair [car cdr])
(defmethod print-method Pair [p writer]
  (.write writer (format "(%s . %s)" (:car p) (:cdr p))))

(defn s-car [x]
  (if (instance? Pair x)
    (:car x)
    (first x)))

(defn s-cdr [x]
  (if (instance? Pair x)
    (:cdr x)
    (rest x)))

(def s-+ clojure.core/+)
(def s-< clojure.core/<)

(defn cons [h t]
  (if (sequential? t)
    (apply list (concat [h] t))
    (Pair. h t)))

(defn equal
  "HAHAHAHA equality in Scheme is very weak."
  [x y]
  (= (str/lower-case x)
     (str/lower-case y)))

(defn pair? [x]
  (or (instance? Pair x)
      (and (list? x)
           (seq x))))

;; this is a bit different
(defn num [x]
  (let [num-sym? #(re-find #"^\d+$" (str %))]
    (cond
      (number? x) x
      (num-sym? x) (Integer/parseInt (str x))
      :else 0)))

(defn atom [x]
  (if (pair? x)
    'nil
    't))

(defn car [x]
  (if (pair? x)
    (s-car x)
    ()))

(defn cdr [x]
  (if (pair? x)
    (s-cdr x)
    ()))

(defn equal [x y]
  (if (= x y)
    't
    'nil))

(defn < [x y]
  (if (s-< (num x) (num y))
    't
    'nil))

(defn nat? [x]
  (if (and (integer? x)
           (< 0 x))
    't
    'nil))

(def natp nat?)

(defn + [x y]
  (s-+ (num x) (num y)))

(defmacro defun
  [name args & body]
  `(defn ~name ~(vec args) ~@body))

(defmacro dethm
  [name args & body]
  `(defn ~name ~(vec args) ~@body))

(defn size [x]
  (if (atom x)
    0
    (+ 1 (+ (size (car x)) (size (cdr x))))))
