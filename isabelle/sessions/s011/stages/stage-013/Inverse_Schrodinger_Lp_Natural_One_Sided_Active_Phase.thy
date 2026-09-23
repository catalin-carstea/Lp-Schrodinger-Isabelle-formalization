theory Inverse_Schrodinger_Lp_Natural_One_Sided_Active_Phase
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Mixed_Root_Quadratic_Decay"
begin

section \<open>A first negative coordinate as the active one-sided phase variable\<close>

lemma slp_left_branch_output_Cons_mixed_center:
  "slp_left_branch_output ((lam, eta) # ps) s =
    slp_mixed_branch_center eta [] lam ps s"
  by (simp add: slp_mixed_branch_center_def
    slp_branch_increment_def slp_left_branch_output_eq_right algebra_simps)


lemma slp_left_branch_residual_Cons_mixed:
  "slp_left_branch_residual ((lam, eta) # ps) s =
    slp_mixed_branch_residual eta [] lam ps s"
proof -
  have cons_output:
    "slp_left_branch_output ((lam, eta) # ps) s =
      - eta + lam + slp_right_branch_output ps s"
    using slp_left_branch_output_Cons_mixed_center[
      where lam=lam and eta=eta and ps=ps and s=s]
    by (simp only: slp_mixed_branch_center_def slp_left_branch_output_Nil)
  show ?thesis
    by (simp add: slp_left_branch_residual_def slp_right_branch_residual_def
      slp_branch_residual_def slp_mixed_branch_residual_def slp_mixed_core_residual_def
      cons_output slp_branch_increment_def slp_left_branch_output_eq_right algebra_simps)
qed


theorem slp_left_branch_residual_first_negative_decay_measure:
  fixes M :: "'c measure"
    and pairs :: "'c \<Rightarrow> (slp_point \<times> slp_point) list"
    and lam terminal :: "'c \<Rightarrow> slp_point"
    and F :: "'c \<Rightarrow> slp_point \<Rightarrow> complex"
  assumes stationary: "hormander_quadratic_stationary_phase_decay_claim TYPE(2)"
    and density: "evans_compact_smooth_l1_density_claim TYPE(2)"
    and M_sigma: "sigma_finite_measure M"
    and lam_measurable: "lam \<in> borel_measurable M"
    and output_measurable:
      "(\<lambda>c. slp_left_branch_output (pairs c) (terminal c)) \<in> borel_measurable M"
    and residual_measurable:
      "(\<lambda>c. slp_left_branch_residual (pairs c) (terminal c)) \<in> borel_measurable M"
    and F_integrable: "integrable (M \<Otimes>\<^sub>M lborel) (case_prod F)"
  shows "((\<lambda>omega::real. integral\<^sup>L (M \<Otimes>\<^sub>M lborel)
    (\<lambda>(c,eta). exp (\<i> * of_real (omega *
      slp_left_branch_residual ((lam c, eta) # pairs c) (terminal c))) * F c eta))
      \<longlongrightarrow> 0) at_top"
proof -
  have left_output:
    "(\<lambda>c. slp_left_branch_output [] (lam c)) \<in> borel_measurable M"
    using lam_measurable by simp
  have right_output:
    "(\<lambda>c. slp_right_branch_output (pairs c) (terminal c)) \<in> borel_measurable M"
    using output_measurable by (simp only: slp_left_branch_output_eq_right)
  have left_residual:
    "(\<lambda>c. slp_left_branch_residual [] (lam c)) \<in> borel_measurable M"
    by (simp add: slp_left_branch_residual_def slp_branch_residual_def)
  have right_residual:
    "(\<lambda>c. slp_right_branch_residual (pairs c) (terminal c)) \<in> borel_measurable M"
    using residual_measurable
    by (simp only: slp_left_branch_residual_def slp_right_branch_residual_def)
  have mixed_decay:
    "((\<lambda>omega::real. integral\<^sup>L (M \<Otimes>\<^sub>M lborel)
      (\<lambda>(c,eta). exp (\<i> * of_real (omega *
        slp_mixed_branch_residual eta [] (lam c) (pairs c) (terminal c))) * F c eta))
        \<longlongrightarrow> 0) at_top"
    by (rule slp_mixed_branch_residual_root_decay_measure[
      where left_pairs="\<lambda>_. []", OF stationary density M_sigma
        left_output right_output left_residual right_residual F_integrable])
  show ?thesis
    using mixed_decay by (simp only: slp_left_branch_residual_Cons_mixed)
qed

end
