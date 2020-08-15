chapter SeCaV_Examples

(*
  Author: Jørgen Villadsen, DTU Compute, 2020
  Contributors: Asta Halkjær From & Alexander Birch Jensen
*)

section \<open>Sequent Calculus Verifier (SeCaV)\<close>

theory SeCaV_Examples imports SeCaV begin

section \<open>Examples\<close>

subsection \<open>Example 1\<close>

proposition \<open>p a \<longrightarrow> p a\<close> by metis

lemma \<open>\<tturnstile>
  [
    Imp (Pre 0 [Fun 0 []]) (Pre 0 [Fun 0 []])
  ]
  \<close>
proof -
  from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 0 []]),
      Pre 0 [Fun 0 []]
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 []],
      Neg (Pre 0 [Fun 0 []])
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

proposition \<open>(\<forall>x. p x) \<longrightarrow> p a \<and> p b\<close> by metis

lemma \<open>\<tturnstile>
  [
    Imp (Uni (Pre 0 [Var 0])) (Con (Pre 0 [Fun 0 []]) (Pre 0 [Fun 1 []]))
  ]
  \<close>
proof -
  from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni (Pre 0 [Var 0])),
      Con (Pre 0 [Fun 0 []]) (Pre 0 [Fun 1 []])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Con (Pre 0 [Fun 0 []]) (Pre 0 [Fun 1 []]),
      Neg (Uni (Pre 0 [Var 0]))
    ]
    \<close>
    using that by simp
  with BetaCon have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 []],
      Neg (Uni (Pre 0 [Var 0]))
    ]
    \<close> and \<open>\<tturnstile>
    [
      Pre 0 [Fun 1 []],
      Neg (Uni (Pre 0 [Var 0]))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni (Pre 0 [Var 0])),
      Pre 0 [Fun 0 []]
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Uni (Pre 0 [Var 0])),
      Pre 0 [Fun 1 []]
    ]
    \<close>
    using that by simp
  with GammaUni have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 0 []]),
      Pre 0 [Fun 0 []]
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 1 []]),
      Pre 0 [Fun 1 []]
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 []],
      Neg (Pre 0 [Fun 0 []])
    ]
    \<close> and \<open>\<tturnstile>
    [
      Pre 0 [Fun 1 []],
      Neg (Pre 0 [Fun 1 []])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

subsection \<open>Example 4\<close>

proposition \<open>(\<forall>x. p x \<longrightarrow> q x) \<longrightarrow> (\<exists>x. p x) \<longrightarrow> (\<exists>x. q x)\<close> by metis

lemma \<open>\<tturnstile>
  [
    Imp
      (Uni (Imp (Pre 0 [Var 0]) (Pre 1 [Var 0])))
      (Imp (Exi (Pre 0 [Var 0])) (Exi (Pre 1 [Var 0])))
  ]
  \<close>
proof -
  from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni (Imp (Pre 0 [Var 0]) (Pre 1 [Var 0]))),
      Imp (Exi (Pre 0 [Var 0])) (Exi (Pre 1 [Var 0]))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Imp (Exi (Pre 0 [Var 0])) (Exi (Pre 1 [Var 0])),
      Neg (Uni (Imp (Pre 0 [Var 0]) (Pre 1 [Var 0])))
    ]
    \<close>
    using that by simp
  with AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Exi (Pre 0 [Var 0])),
      Exi (Pre 1 [Var 0]),
      Neg (Uni (Imp (Pre 0 [Var 0]) (Pre 1 [Var 0])))
    ]
    \<close>
    using that by simp
  with DeltaExi have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 0 []]),
      Exi (Pre 1 [Var 0]),
      Neg (Uni (Imp (Pre 0 [Var 0]) (Pre 1 [Var 0])))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni (Imp (Pre 0 [Var 0]) (Pre 1 [Var 0]))),
      Neg (Pre 0 [Fun 0 []]),
      Exi (Pre 1 [Var 0])
    ]
    \<close>
    using that by simp
  with GammaUni have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp (Pre 0 [Fun 0 []]) (Pre 1 [Fun 0 []])),
      Neg (Pre 0 [Fun 0 []]),
      Exi (Pre 1 [Var 0])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Exi (Pre 1 [Var 0]),
      Neg (Imp (Pre 0 [Fun 0 []]) (Pre 1 [Fun 0 []])),
      Neg (Pre 0 [Fun 0 []])
    ]
    \<close>
    using that by simp
  with GammaExi have ?thesis if \<open>\<tturnstile>
    [
      Pre 1 [Fun 0 []],
      Neg (Imp (Pre 0 [Fun 0 []]) (Pre 1 [Fun 0 []])),
      Neg (Pre 0 [Fun 0 []])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Neg (Imp (Pre 0 [Fun 0 []]) (Pre 1 [Fun 0 []])),
      Pre 1 [Fun 0 []],
      Neg (Pre 0 [Fun 0 []])
    ]
    \<close>
    using that by simp
  with BetaImp have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 []],
      Pre 1 [Fun 0 []],
      Neg (Pre 0 [Fun 0 []])
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Pre 1 [Fun 0 []]),
      Pre 1 [Fun 0 []],
      Neg (Pre 0 [Fun 0 []])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 []],
      Neg (Pre 0 [Fun 0 []])
    ]
    \<close> and \<open>\<tturnstile>
    [
      Pre 1 [Fun 0 []],
      Neg (Pre 1 [Fun 0 []])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

subsection \<open>Example 5\<close>

proposition \<open>\<exists>x. \<forall>y. p y \<or> \<not> p x\<close> by metis

lemma \<open>\<tturnstile>
  [
    Exi (Uni (Dis (Pre 0 [Var 0]) (Neg (Pre 0 [Var 1]))))
  ]
  \<close>
proof -
  from Ext have ?thesis if \<open>\<tturnstile>
    [
      Exi (Uni (Dis (Pre 0 [Var 0]) (Neg (Pre 0 [Var 1])))),
      Exi (Uni (Dis (Pre 0 [Var 0]) (Neg (Pre 0 [Var 1]))))
    ]
    \<close>
    using that by simp
  with GammaExi[where t=\<open>Fun 0 []\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Uni (Dis (Pre 0 [Var 0]) (Neg (Pre 0 [Fun 0 []]))),
      Exi (Uni (Dis (Pre 0 [Var 0]) (Neg (Pre 0 [Var 1]))))
    ]
    \<close>
    using that by simp
  with DeltaUni have ?thesis if \<open>\<tturnstile>
    [
      Dis (Pre 0 [Fun 1 []]) (Neg (Pre 0 [Fun 0 []])),
      Exi (Uni (Dis (Pre 0 [Var 0]) (Neg (Pre 0 [Var 1]))))
    ]
    \<close>
    using that by simp
  with AlphaDis have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 1 []],
      Neg (Pre 0 [Fun 0 []]),
      Exi (Uni (Dis (Pre 0 [Var 0]) (Neg (Pre 0 [Var 1]))))
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Exi (Uni (Dis (Pre 0 [Var 0]) (Neg (Pre 0 [Var 1])))),
      Pre 0 [Fun 1 []]
    ]
    \<close>
    using that by simp
  with GammaExi[where t=\<open>Fun 1 []\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Uni (Dis (Pre 0 [Var 0]) (Neg (Pre 0 [Fun 1 []]))),
      Pre 0 [Fun 1 []]
    ]
    \<close>
    using that by simp
  with DeltaUni have ?thesis if \<open>\<tturnstile>
    [
      Dis (Pre 0 [Fun 3 []]) (Neg (Pre 0 [Fun 1 []])),
      Pre 0 [Fun 1 []]
    ]
    \<close>
    using that by simp
  with AlphaDis have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 3 []],
      Neg (Pre 0 [Fun 1 []]),
      Pre 0 [Fun 1 []]
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 1 []],
      Neg (Pre 0 [Fun 1 []])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

end
