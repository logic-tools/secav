chapter SeCaV_Propositional

(*
  Author: Jørgen Villadsen, DTU Compute, 2020
  Contributors: Asta Halkjær From & Alexander Birch Jensen
*)

section \<open>Sequent Calculus Verifier (SeCaV)\<close>

theory SeCaV_Propositional imports SeCaV begin

abbreviation \<open>P \<equiv> Pre 0 []\<close>

abbreviation \<open>Q \<equiv> Pre 1 []\<close>

abbreviation \<open>R \<equiv> Pre 2 []\<close>

section \<open>Examples\<close>

subsection \<open>Example 1\<close>

proposition \<open>p \<longrightarrow> p\<close> by metis

lemma \<open>\<tturnstile>
  [
    Imp P P
  ]
  \<close>
proof -
  from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg P,
      P
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      P,
      Neg P
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

subsection \<open>Example 2\<close>

proposition \<open>\<not> p \<longrightarrow> \<not> \<not> \<not> p\<close> by metis

lemma \<open>\<tturnstile>
  [
    Imp (Neg P) (Neg (Neg (Neg P)))
  ]
  \<close>
proof -
  from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Neg P),
      Neg (Neg (Neg P))
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
    Imp (Neg (Neg P)) P
  ]
  \<close>
proof -
  from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Neg (Neg P)),
      P
    ]
    \<close>
    using that by simp
  with Neg have ?thesis if \<open>\<tturnstile>
    [
      Neg P,
      P
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      P,
      Neg P
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
    Dis P (Imp P Q)
  ]
  \<close>
proof -
  from AlphaDis have ?thesis if \<open>\<tturnstile>
    [
      P,
      Imp P Q
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Imp P Q,
      P
    ]
    \<close>
    using that by simp
  with AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg P,
      Q,
      P
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      P,
      Neg P
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
    Imp (Con P Q) (Imp R (Con P R))
  ]
  \<close>
proof -
  from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Con P Q),
      Imp R (Con P R)
    ]
    \<close>
    using that by simp
  with AlphaCon have ?thesis if \<open>\<tturnstile>
    [
      Neg P,
      Neg Q,
      Imp R (Con P R)
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Imp R (Con P R),
      Neg P
    ]
    \<close>
    using that by simp
  with AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg R,
      Con P R,
      Neg P
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Con P R,
      Neg R,
      Neg P
    ]
    \<close>
    using that by simp
  with BetaCon have ?thesis if \<open>\<tturnstile>
    [
      P,
      Neg R,
      Neg P
    ]
    \<close> and \<open>\<tturnstile>
    [
      R,
      Neg R,
      Neg P
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

end
