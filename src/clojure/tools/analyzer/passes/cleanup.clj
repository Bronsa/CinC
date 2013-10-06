;:   Copyright (c) Nicola Mometto, Rich Hickey & contributors.
;;   The use and distribution terms for this software are covered by the
;;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;;   which can be found in the file epl-v10.html at the root of this distribution.
;;   By using this software in any fashion, you are agreeing to be bound by
;;   the terms of this license.
;;   You must not remove this notice, or any other, from this software.

(ns clojure.tools.analyzer.passes.cleanup)

(defn cleanup1 [ast]
  (let [ast (-> ast
              (update-in [:env] dissoc :locals)
              (update-in [:env] dissoc :loop-locals))]
    (if (= :local (:op ast))
      (dissoc (assoc ast :children (vec (remove #{:init} (:children ast)))) :init)
      ast)))


(defn cleanup2 [ast]
  (let [ast (-> ast
              (update-in [:env] dissoc :loop-locals-casts)
              (dissoc :atom))]
    ast))
