;:   Copyright (c) Nicola Mometto, Rich Hickey & contributors.
;;   The use and distribution terms for this software are covered by the
;;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;;   which can be found in the file epl-v10.html at the root of this distribution.
;;   By using this software in any fashion, you are agreeing to be bound by
;;   the terms of this license.
;;   You must not remove this notice, or any other, from this software.

(ns cinc.analyzer.passes.source-info)

(defn get-line [x env]
  (-> x meta :line))
(defn get-col [x env]
  (-> x meta :column))

(defn -source-info [x env]
  (merge
   (when-let [file (and (not= *file* "NO_SOURCE_FILE")
                        *file*)]
     {:file file})
   (when-let [line (get-line x env)]
     {:line line})
   (when-let [column (get-col x env)]
     {:column column})))

(defn source-info
  [{:keys [form env] :as ast}]
  (update-in ast [:env] merge (-source-info form env)))
