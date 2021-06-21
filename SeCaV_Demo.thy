(*
  Author: Jørgen Villadsen, DTU Compute, 2021
*)

theory SeCaV_Demo imports SeCaV begin

section \<open>Example 1\<close>

proposition \<open>p a b \<or> \<not> p a b\<close> by metis

text \<open>
  Predicate numbers
    0 = p
  Function numbers
    0 = a
    1 = b
  \<close>

lemma \<open>\<tturnstile>
  [
    Dis (Pre 0 [Fun 0 [], Fun 1 []]) (Neg (Pre 0 [Fun 0 [], Fun 1 []]))
  ]
  \<close>
proof -
  from AlphaDis have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 [], Fun 1 []],
      Neg (Pre 0 [Fun 0 [], Fun 1 []])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

section \<open>Example 2\<close>

proposition \<open>(\<forall>x y. p x y) \<longrightarrow> p a a\<close> by metis

text \<open>
  Predicate numbers
    0 = p
  Function numbers
    0 = a
  \<close>

lemma \<open>\<tturnstile>
  [
    Imp (Uni (Uni (Pre 0 [Var 1, Var 0]))) (Pre 0 [Fun 0 [], Fun 0 []])
  ]
  \<close>
proof -
  from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni (Uni (Pre 0 [Var 1, Var 0]))),
      Pre 0 [Fun 0 [], Fun 0 []]
    ]
    \<close>
    using that by simp
  with GammaUni[where t=\<open>Fun 0 []\<close>] have ?thesis if \<open>\<tturnstile>
    [
      Neg (Uni (Pre 0 [Fun 0 [], Var 0])),
      Pre 0 [Fun 0 [], Fun 0 []]
    ]
    \<close>
    using that by simp
  with GammaUni have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 [Fun 0 [], Fun 0 []]),
      Pre 0 [Fun 0 [], Fun 0 []]
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 [], Fun 0 []],
      Neg (Pre 0 [Fun 0 [], Fun 0 []])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

section \<open>Example 3\<close>

proposition \<open>(\<forall>x. p x \<longrightarrow> q x) \<longrightarrow> (\<exists>x. p x) \<longrightarrow> (\<exists>x. q x)\<close> by metis

text \<open>
  Predicate numbers
    0 = p
    1 = q
  Function numbers
    0 = a
  \<close>

lemma \<open>\<tturnstile>
  [
    Imp (Uni (Imp (Pre 0 [Var 0]) (Pre 1 [Var 0]))) (Imp (Exi (Pre 0 [Var 0])) (Exi (Pre 1 [Var 0])))
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
  with BetaImp have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [Fun 0 []],
      Neg (Pre 0 [Fun 0 []]),
      Exi (Pre 1 [Var 0])
    ]
    \<close> and \<open>\<tturnstile>
    [
      Neg (Pre 1 [Fun 0 []]),
      Neg (Pre 0 [Fun 0 []]),
      Exi (Pre 1 [Var 0])
    ]
    \<close>
    using that by simp
  with Basic have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 1 [Fun 0 []]),
      Neg (Pre 0 [Fun 0 []]),
      Exi (Pre 1 [Var 0])
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Exi (Pre 1 [Var 0]),
      Neg (Pre 1 [Fun 0 []])
    ]
    \<close>
    using that by simp
  with GammaExi have ?thesis if \<open>\<tturnstile>
    [
      Pre 1 [Fun 0 []],
      Neg (Pre 1 [Fun 0 []])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

end

(*

# "Example 1"

Dis p[a, b] (Neg p[a, b])

AlphaDis
  p[a, b]
  Neg p[a, b]
Basic

# "Example 2"

Imp (Uni (Uni (p[1, 0]))) p[a, a]

AlphaImp
  Neg (Uni (Uni p[1, 0]))
  p[a, a]
GammaUni[a]
  Neg (Uni p[a, 0])
  p[a, a]
GammaUni
  Neg p[a, a]
  p[a, a]
Ext
  p[a, a]
  Neg p[a, a]
Basic

# "Example 3"

Imp (Uni (Imp p[0] q[0])) (Imp (Exi p[0]) (Exi q[0]))

AlphaImp
  Neg (Uni (Imp p[0] q[0]))
  Imp (Exi p[0]) (Exi q[0])
Ext
  Imp (Exi p[0]) (Exi q[0])
  Neg (Uni (Imp p[0] q[0]))
AlphaImp
  Neg (Exi p[0])
  Exi q[0]
  Neg (Uni (Imp p[0] q[0]))
DeltaExi
  Neg p[a]
  Exi q[0]
  Neg (Uni (Imp p[0] q[0]))
Ext
  Neg (Uni (Imp p[0] q[0]))
  Neg p[a]
  Exi q[0]
GammaUni
  Neg (Imp p[a] q[a])
  Neg p[a]
  Exi q[0]
BetaImp
  p[a]
  Neg p[a]
  Exi q[0]
+
  Neg q[a]
  Neg p[a]
  Exi q[0]
Basic
  Neg q[a]
  Neg p[a]
  Exi q[0]
Ext
  Exi q[0]
  Neg q[a]
GammaExi
  q[a]
  Neg q[a]
Basic

*)
