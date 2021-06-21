chapter SeCaV_Propositional

(*
  Author: Jørgen Villadsen, DTU Compute, 2021
  Contributors: Asta Halkjær From & Alexander Birch Jensen
*)

section \<open>Sequent Calculus Verifier (SeCaV)\<close>

theory SeCaV_Propositional imports SeCaV begin

section \<open>Examples\<close>

subsection \<open>Example 1\<close>

proposition \<open>p \<or> \<not> p\<close> by metis

lemma \<open>\<tturnstile>
  [
    Dis (Pre 0 []) (Neg (Pre 0 []))
  ]
  \<close>
proof -
  from AlphaDis have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [],
      Neg (Pre 0 [])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

subsection \<open>Example 2\<close>

proposition \<open>p \<longrightarrow> \<not> \<not> p\<close> by metis

lemma \<open>\<tturnstile>
  [
    Imp (Pre 0 []) (Neg (Neg (Pre 0 [])))
  ]
  \<close>
proof -
  from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 []),
      Neg (Neg (Pre 0 []))
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

subsection \<open>Example 3\<close>

proposition \<open>\<not> \<not> p \<longrightarrow> p\<close> by metis

lemma \<open>\<tturnstile>
  [
    Imp (Neg (Neg (Pre 0 []))) (Pre 0 [])
  ]
  \<close>
proof -
  from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Neg (Neg (Pre 0 []))),
      Pre 0 []
    ]
    \<close>
    using that by simp
  with NegNeg have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 []),
      Pre 0 []
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [],
      Neg (Pre 0 [])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

subsection \<open>Example 4\<close>

proposition \<open>p \<or> (p \<longrightarrow> q)\<close> by metis

lemma \<open>\<tturnstile>
  [
    Dis (Pre 0 []) (Imp (Pre 0 []) (Pre 1 []))
  ]
  \<close>
proof -
  from AlphaDis have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [],
      Imp (Pre 0 []) (Pre 1 [])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Imp (Pre 0 []) (Pre 1 []),
      Pre 0 []
    ]
    \<close>
    using that by simp
  with AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 []),
      Pre 1 [],
      Pre 0 []
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [],
      Neg (Pre 0 [])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

subsection \<open>Example 5\<close>

proposition \<open>p \<and> q \<longrightarrow> r \<longrightarrow> p \<and> r\<close> by metis

lemma \<open>\<tturnstile>
  [
    Imp (Con (Pre 0 []) (Pre 1 [])) (Imp (Pre 2 []) (Con (Pre 0 []) (Pre 2 [])))
  ]
  \<close>
proof -
  from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Con (Pre 0 []) (Pre 1 [])),
      Imp (Pre 2 []) (Con (Pre 0 []) (Pre 2 []))
    ]
    \<close>
    using that by simp
  with AlphaCon have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 []),
      Neg (Pre 1 []),
      Imp (Pre 2 []) (Con (Pre 0 []) (Pre 2 []))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Imp (Pre 2 []) (Con (Pre 0 []) (Pre 2 [])),
      Neg (Pre 0 [])
    ]
    \<close>
    using that by simp
  with AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 2 []),
      Con (Pre 0 []) (Pre 2 []),
      Neg (Pre 0 [])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Con (Pre 0 []) (Pre 2 []),
      Neg (Pre 2 []),
      Neg (Pre 0 [])
    ]
    \<close>
    using that by simp
  with BetaCon have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [],
      Neg (Pre 2 []),
      Neg (Pre 0 [])
    ]
    \<close> and \<open>\<tturnstile>
    [
      Pre 2 [],
      Neg (Pre 2 []),
      Neg (Pre 0 [])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

end
