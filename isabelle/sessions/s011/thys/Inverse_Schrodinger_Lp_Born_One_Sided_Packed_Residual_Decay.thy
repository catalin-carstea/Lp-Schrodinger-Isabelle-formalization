theory Inverse_Schrodinger_Lp_Born_One_Sided_Packed_Residual_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_One_Sided_Residual_Identity"
begin

section \<open>Literal one-sided residual decay in packed coordinates\<close>

lemma slp_one_sided_branch_family_reconstruct:
  fixes y :: "unit + ('i::finite + 'i) \<Rightarrow> complex"
  shows
    "slp_one_sided_branch_family
        (\<lambda>i. y (Inr (Inl i)))
        (\<lambda>i. y (Inr (Inr i)))
        (y (Inl ())) = y"
proof (rule ext)
  fix k
  show
    "slp_one_sided_branch_family
        (\<lambda>i. y (Inr (Inl i)))
        (\<lambda>i. y (Inr (Inr i)))
        (y (Inl ())) k = y k"
    by (cases k)
      (simp_all add: slp_one_sided_branch_family_def split: sum.splits)
qed

definition slp_one_sided_packed_residual ::
    "real^((unit + ('i::finite + 'i)) \<times> bool) \<Rightarrow> real"
where
  "slp_one_sided_packed_residual x =
    (let y = slp_complex_family_unpack x
     in Re ((\<Sum>i\<in>UNIV. (y (Inr (Inl i))) ^ 2) -
          (\<Sum>i\<in>UNIV. (y (Inr (Inr i))) ^ 2) +
          (y (Inl ())) ^ 2 -
          (y (Inl ()) +
            (\<Sum>i\<in>UNIV. y (Inr (Inl i)) - y (Inr (Inr i)))) ^ 2))"

lemma slp_one_sided_packed_residual_identity:
  "slp_one_sided_packed_residual x =
    slp_signed_residual slp_one_sided_branch_sign
      (slp_complex_family_unpack x)"
proof -
  let ?y = "slp_complex_family_unpack x"
  note residual = slp_one_sided_branch_residual_identity[
      where lambda = "\<lambda>i. ?y (Inr (Inl i))"
        and eta = "\<lambda>i. ?y (Inr (Inr i))"
        and s = "?y (Inl ())"]
  have reconstruct:
    "slp_one_sided_branch_family
        (\<lambda>i. ?y (Inr (Inl i)))
        (\<lambda>i. ?y (Inr (Inr i)))
        (?y (Inl ())) = ?y"
    by (rule slp_one_sided_branch_family_reconstruct)
  show ?thesis
    unfolding slp_one_sided_packed_residual_def Let_def
    using residual reconstruct by simp
qed

theorem slp_one_sided_packed_residual_decay:
  fixes F :: "real^((unit + ('i::finite + 'i)) \<times> bool) \<Rightarrow> complex"
  assumes stationary_phase:
      "hormander_quadratic_stationary_phase_decay_claim
        TYPE(('i + 'i) \<times> bool)"
    and density:
      "evans_compact_smooth_l1_density_claim TYPE(('i + 'i) \<times> bool)"
    and F_integrable: "integrable lborel F"
  shows
    "((\<lambda>omega. integral\<^sup>L lborel
        (\<lambda>x. exp (\<i> * of_real
          (omega * slp_one_sided_packed_residual x)) * F x))
      \<longlongrightarrow> 0) at_top"
proof -
  note decay = slp_one_sided_residual_cartesian_quadratic_decay[
      where F = F, OF stationary_phase density F_integrable]
  show ?thesis
    using decay
    by (simp only: slp_one_sided_packed_residual_identity)
qed

end
