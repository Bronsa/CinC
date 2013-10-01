(defproject CinC "0.0.1-SNAPSHOT"
  :description "Clojure compiler in Clojure."
  :url "https://github.com/Bronsa/CinC.git"
  :license {:name "Eclipse Public License"
            :url "http://www.eclipse.org/legal/epl-v10.html"}
  :global-vars {*warn-on-reflection* true}
  :dependencies [[org.clojure/clojure "1.5.1"]
                 [org.clojure/tools.reader "0.7.8"]
                 [org.ow2.asm/asm-all "4.1"]])
