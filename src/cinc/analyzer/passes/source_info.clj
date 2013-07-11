(ns cinc.analyzer.passes.source-info
  (:require [cinc.analyzer.utils :refer [prewalk]]))

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
  [ast]
  (prewalk ast (fn [{:keys [form env] :as ast}]
                 (update-in ast [:env] merge (-source-info form env)))))
