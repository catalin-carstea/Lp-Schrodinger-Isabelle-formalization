theory Inverse_Schrodinger_Lp_Born_One_Sided_Residual_QRL
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Residual_Cartesian_QRL"
begin

section \<open>Quadratic decay for the one-sided branch sign pattern\<close>

definition slp_one_sided_branch_sign ::
    "(unit + ('i::finite + 'i)) \<Rightarrow> real" where
  "slp_one_sided_branch_sign k =
    (case k of
      Inl _ \<Rightarrow> 1
    | Inr side \<Rightarrow> case side of Inl _ \<Rightarrow> 1 | Inr _ \<Rightarrow> -1)"

lemma slp_one_sided_branch_sign_values:
  fixes k :: "unit + ('i::finite + 'i)"
  shows "slp_one_sided_branch_sign k = -1 \<or>
    slp_one_sided_branch_sign k = 1"
  by (cases k; simp add: slp_one_sided_branch_sign_def split: sum.splits)

lemma slp_sum_UNIV_sum_type:
  fixes f :: "('a::finite + 'b::finite) \<Rightarrow> real"
  shows "(\<Sum>x\<in>UNIV. f x) =
    (\<Sum>a\<in>UNIV. f (Inl a)) + (\<Sum>b\<in>UNIV. f (Inr b))"
proof -
  have left_reindex:
    "(\<Sum>x\<in>Inl ` (UNIV :: 'a set). f x) =
      (\<Sum>a\<in>UNIV. f (Inl a))"
    using sum.reindex[where h = Inl and A = "UNIV :: 'a set" and g = f]
    by (simp add: o_def)
  have right_reindex:
    "(\<Sum>x\<in>Inr ` (UNIV :: 'b set). f x) =
      (\<Sum>b\<in>UNIV. f (Inr b))"
    using sum.reindex[where h = Inr and A = "UNIV :: 'b set" and g = f]
    by (simp add: o_def)
  have disjoint:
    "Inl ` (UNIV :: 'a set) \<inter> Inr ` (UNIV :: 'b set) = {}"
    by auto
  have union_sum:
    "(\<Sum>x\<in>Inl ` (UNIV :: 'a set) \<union> Inr ` (UNIV :: 'b set). f x) =
      (\<Sum>x\<in>Inl ` (UNIV :: 'a set). f x) +
        (\<Sum>x\<in>Inr ` (UNIV :: 'b set). f x)"
    by (rule sum.union_disjoint) (simp_all add: disjoint)
  show ?thesis
    using union_sum left_reindex right_reindex
    by (simp only: UNIV_sum)
qed

lemma slp_one_sided_branch_signed_sum:
  "(\<Sum>k\<in>(UNIV :: (unit + ('i::finite + 'i)) set).
      slp_one_sided_branch_sign k) = 1"
proof -
  note outer = slp_sum_UNIV_sum_type[
      where f = "slp_one_sided_branch_sign ::
        (unit + ('i + 'i)) \<Rightarrow> real"]
  note inner = slp_sum_UNIV_sum_type[
      where f = "\<lambda>side :: 'i + 'i.
        slp_one_sided_branch_sign (Inr side)"]
  show ?thesis
    using outer inner
    by (simp add: slp_one_sided_branch_sign_def o_def)
qed

theorem slp_one_sided_residual_cartesian_quadratic_decay:
  fixes F :: "real^((unit + ('i::finite + 'i)) \<times> bool) \<Rightarrow>
    complex"
  assumes stationary_phase:
      "hormander_quadratic_stationary_phase_decay_claim
        TYPE(('i + 'i) \<times> bool)"
    and density:
      "evans_compact_smooth_l1_density_claim TYPE(('i + 'i) \<times> bool)"
    and F_integrable: "integrable lborel F"
  shows
    "((\<lambda>omega. integral\<^sup>L lborel
        (\<lambda>x. exp (\<i> * of_real
          (omega * slp_signed_residual slp_one_sided_branch_sign
            (slp_complex_family_unpack x))) * F x))
      \<longlongrightarrow> 0) at_top"
  by (rule slp_signed_residual_cartesian_quadratic_decay[
      where epsilon = slp_one_sided_branch_sign and F = F])
    (rule stationary_phase, rule density,
      rule slp_one_sided_branch_sign_values,
      rule slp_one_sided_branch_signed_sum, rule F_integrable)

end
