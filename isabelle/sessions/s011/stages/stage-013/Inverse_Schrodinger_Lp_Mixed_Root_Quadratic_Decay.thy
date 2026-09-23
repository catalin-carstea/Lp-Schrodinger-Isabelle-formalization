theory Inverse_Schrodinger_Lp_Mixed_Root_Quadratic_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Quadratic_RL_Passive_Measure"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Mixed_Phase"
begin

section \<open>The root as a fixed-dimensional active mixed-phase variable\<close>

definition slp_mixed_root_hessian :: "real^2^2" where
  "slp_mixed_root_hessian =
    (\<chi> i j. if i = j then (if i = 0 then -4 else 4) else 0)"

lemma slp_mixed_root_hessian_certificate:
  "hormander_real_symmetric_matrix slp_mixed_root_hessian \<and>
    hormander_real_nondegenerate_matrix slp_mixed_root_hessian"
proof
  show "hormander_real_symmetric_matrix slp_mixed_root_hessian"
    by (auto simp: hormander_real_symmetric_matrix_def
        slp_mixed_root_hessian_def)
  have universe_two: "(UNIV :: 2 set) = {0, 1}"
    using UNIV_2 by auto
  have coordinate_action:
    "(slp_mixed_root_hessian *v x) $ i =
      (if i = 0 then -4 else 4) * x $ i" for x :: slp_point and i :: 2
  proof -
    have index_cases: "i = 0 \<or> i = 1" using universe_two by blast
    show ?thesis
      using index_cases
      by (auto simp: slp_mixed_root_hessian_def matrix_vector_mult_def universe_two)
  qed
  show "hormander_real_nondegenerate_matrix slp_mixed_root_hessian"
    unfolding hormander_real_nondegenerate_matrix_def
  proof (intro allI impI)
    fix x :: slp_point
    assume zero_image: "slp_mixed_root_hessian *v x = 0"
    have zero_coordinate: "x $ i = 0" for i :: 2
    proof -
      have "(if i = 0 then -4 else 4) * x $ i = 0"
        using zero_image by (simp add: coordinate_action[symmetric])
      then show ?thesis by (auto split: if_splits)
    qed
    show "x = 0" using zero_coordinate by (simp add: vec_eq_iff)
  qed
qed

theorem slp_mixed_branch_residual_root_decay_measure:
  fixes M :: "'c measure"
    and left_pairs right_pairs :: "'c \<Rightarrow> (slp_point \<times> slp_point) list"
    and left_terminal right_terminal :: "'c \<Rightarrow> slp_point"
    and F :: "'c \<Rightarrow> slp_point \<Rightarrow> complex"
  assumes stationary: "hormander_quadratic_stationary_phase_decay_claim TYPE(2)"
    and density: "evans_compact_smooth_l1_density_claim TYPE(2)"
    and M_sigma: "sigma_finite_measure M"
    and left_output_measurable:
      "(\<lambda>c. slp_left_branch_output (left_pairs c) (left_terminal c))
        \<in> borel_measurable M"
    and right_output_measurable:
      "(\<lambda>c. slp_right_branch_output (right_pairs c) (right_terminal c))
        \<in> borel_measurable M"
    and left_residual_measurable:
      "(\<lambda>c. slp_left_branch_residual (left_pairs c) (left_terminal c))
        \<in> borel_measurable M"
    and right_residual_measurable:
      "(\<lambda>c. slp_right_branch_residual (right_pairs c) (right_terminal c))
        \<in> borel_measurable M"
    and F_integrable: "integrable (M \<Otimes>\<^sub>M lborel) (case_prod F)"
  shows "((\<lambda>omega::real. integral\<^sup>L (M \<Otimes>\<^sub>M lborel)
    (\<lambda>(c,x). exp (\<i> * of_real (omega *
      slp_mixed_branch_residual x (left_pairs c) (left_terminal c)
        (right_pairs c) (right_terminal c))) * F c x))
      \<longlongrightarrow> 0) at_top"
proof -
  interpret quadratic: hormander_quadratic_stationary_phase_decay "TYPE(2)"
    by standard (rule stationary)
  let ?u = "\<lambda>c. slp_left_branch_output (left_pairs c) (left_terminal c)"
  let ?v = "\<lambda>c. slp_right_branch_output (right_pairs c) (right_terminal c)"
  let ?b = "\<lambda>c. (\<chi> i. if i = 0 then 2 * (?u c + ?v c) $ 0
    else -2 * (?u c + ?v c) $ 1) :: slp_point"
  let ?p0 = "\<lambda>c.
    slp_left_branch_residual (left_pairs c) (left_terminal c) +
    slp_right_branch_residual (right_pairs c) (right_terminal c) -
      2 * (?u c $ 0 * ?v c $ 0 - ?u c $ 1 * ?v c $ 1)"
  have symmetric: "hormander_real_symmetric_matrix slp_mixed_root_hessian"
    by (rule conjunct1[OF slp_mixed_root_hessian_certificate])
  have nondegenerate: "hormander_real_nondegenerate_matrix slp_mixed_root_hessian"
    by (rule conjunct2[OF slp_mixed_root_hessian_certificate])
  have coefficient_continuous:
    "continuous_on UNIV (\<lambda>z::slp_point.
      (\<chi> i. if i = 0 then 2 * z $ 0 else -2 * z $ 1) :: slp_point)"
  proof (rule continuous_on_vec_lambda)
    fix i :: 2
    show "continuous_on UNIV (\<lambda>z::slp_point.
      if i = 0 then 2 * z $ 0 else -2 * z $ 1)"
      by (cases "i = 0"; simp; intro continuous_intros)
  qed
  have output_sum_measurable: "(\<lambda>c. ?u c + ?v c) \<in> borel_measurable M"
    using left_output_measurable right_output_measurable by measurable
  have b_measurable: "?b \<in> borel_measurable M"
    by (rule borel_measurable_continuous_on[
        OF coefficient_continuous output_sum_measurable])
  have left_component_measurable[measurable]:
    "(\<lambda>c. ?u c $ i) \<in> borel_measurable M" for i :: 2
    using measurable_comp[OF left_output_measurable borel_measurable_nth[of i]]
    by (simp only: comp_def)
  have right_component_measurable[measurable]:
    "(\<lambda>c. ?v c $ i) \<in> borel_measurable M" for i :: 2
    using measurable_comp[OF right_output_measurable borel_measurable_nth[of i]]
    by (simp only: comp_def)
  have p0_measurable: "?p0 \<in> borel_measurable M"
    using left_output_measurable right_output_measurable
      left_residual_measurable right_residual_measurable by measurable
  have universe_two: "(UNIV :: 2 set) = {0, 1}"
    using UNIV_2 by auto
  have phase_identity:
    "inner x (slp_mixed_root_hessian *v x) / 2 + inner (?b c) x + ?p0 c =
      slp_mixed_branch_residual x (left_pairs c) (left_terminal c)
        (right_pairs c) (right_terminal c)" for c and x :: slp_point
    unfolding slp_mixed_branch_residual_def slp_mixed_core_residual_def
      slp_point_quadratic_value_def slp_mixed_root_hessian_def
      matrix_vector_mult_def inner_vec_def
    by (simp add: universe_two power2_eq_square field_simps algebra_simps)
  have root_decay:
    "((\<lambda>omega::real. integral\<^sup>L (M \<Otimes>\<^sub>M lborel)
      (\<lambda>(c,x). exp (\<i> * of_real
        (omega * (inner x (slp_mixed_root_hessian *v x) / 2 +
          inner (?b c) x + ?p0 c))) * F c x)) \<longlongrightarrow> 0) at_top"
    by (rule quadratic.slp_passive_affine_quadratic_decay_measure[
        OF M_sigma density symmetric nondegenerate b_measurable
          p0_measurable F_integrable])
  show ?thesis using root_decay by (simp only: phase_identity)
qed

end
