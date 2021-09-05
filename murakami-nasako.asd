;;;; murakami-nasako.asd

(asdf:defsystem #:murakami-nasako
  :description "Implementation of Murakami and Nasako's knapsack cryptosystem"
  :author "goose121 <goose121@github-users-noreply@github.com>"
  :license  "AGPLv3"
  :version "0.0.1"
  :serial t
  :depends-on ("alexandria")
  :components ((:file "package")
               (:file "murakami-nasako")))
