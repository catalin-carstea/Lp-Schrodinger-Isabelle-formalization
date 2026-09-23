theory Inverse_Schrodinger_Lp_Common_CGO_Tested_Remainder_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_018.Inverse_Schrodinger_Lp_Common_CGO_Tested_Remainder_Package"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_018.Inverse_Schrodinger_Lp_Common_CGO_Literal_Majorant_Decay"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Decay of the tested common-CGO Neumann remainder\<close>

context slp_cgo_full_weak_solution_context
begin

theorem slp_common_cgo_born_tested_neumann_remainder_tendsto_zero:
  fixes p epsilon A R A0 B0 B1 :: real
    and Omega X :: "slp_point set"
    and phi cutoff coefficient coefficient_tilde V V_tilde :: slp_scalar_field
  assumes riesz_hls: "aim_planar_riesz_hls_claim"
    and cauchy_test_left_inverse:
      "aim_planar_cauchy_test_left_inverse_claim"
    and evans_density: "evans_compact_support_w1p_zero_density_claim"
    and exponent_lower: "1 < p"
    and exponent_upper: "p < 2"
    and loss_positive: "0 < epsilon"
    and loss_upper: "epsilon < 1 - 1 / p"
    and radius_nonnegative: "0 \<le> A"
    and radius_lower: "1 \<le> R"
    and set_radius:
      "\<And>y :: slp_point. y \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm y \<le> A"
    and center_geometry:
      "\<And>c y :: slp_point. c \<in> Omega \<Longrightarrow> y \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm (y - c) \<le> R"
    and X_open: "open X"
    and X_bounded: "bounded X"
    and Omega_subset: "Omega \<subseteq> X"
    and cutoff_test: "slp_test_function_on X cutoff"
    and cutoff_one: "\<And>z. z \<in> Omega \<Longrightarrow> cutoff z = 1"
    and cutoff_bound:
      "\<And>x. x \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm (cutoff x) \<le> A0"
    and cutoff_derivative_zero_bound:
      "\<And>x. x \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm
          (slp_complex_partial_derivative cutoff 0 x) \<le> B0"
    and cutoff_derivative_one_bound:
      "\<And>x. x \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm
          (slp_complex_partial_derivative cutoff 1 x) \<le> B1"
    and A0_nonnegative: "0 \<le> A0"
    and B0_nonnegative: "0 \<le> B0"
    and B1_nonnegative: "0 \<le> B1"
    and coefficient_lp: "aim_complex_lp_on_plane p coefficient"
    and coefficient_support: "{x. coefficient x \<noteq> 0} \<subseteq> X"
    and coefficient_tilde_lp:
      "aim_complex_lp_on_plane p coefficient_tilde"
    and coefficient_tilde_support:
      "{x. coefficient_tilde x \<noteq> 0} \<subseteq> X"
    and coefficient_normalization: "coefficient = (\<lambda>z. V z / 4)"
    and coefficient_tilde_normalization:
      "coefficient_tilde = (\<lambda>z. V_tilde z / 4)"
    and domain: "slp_bounded_smooth_domain Omega"
    and orthogonality:
      "slp_alessandrini_orthogonality Omega V V_tilde"
    and phi_test: "slp_test_function_on Omega phi"
  defines
    "N \<equiv> nat
      (slp_tail_cutoff1
        (1 - 1 / p - epsilon) (1 - 1 / p - epsilon))"
  shows
    "((\<lambda>tau :: real.
        slp_cgo_born_tested_neumann_remainder_functional
          X N N tau phi
          (slp_restrict_field Omega (\<lambda>x. V x - V_tilde x))
          cutoff coefficient coefficient_tilde)
      \<longlongrightarrow> 0) at_top"
proof -
  let ?Q = "slp_restrict_field Omega (\<lambda>x. V x - V_tilde x)"
  obtain T Z C CV C_tilde CV_tilde where
      left_data:
        "slp_left_neumann_joint_geometric_data
          p epsilon X Z cutoff coefficient C CV T"
    and right_data:
        "slp_right_neumann_joint_geometric_data
          p epsilon X Z cutoff coefficient_tilde C_tilde CV_tilde T"
    and quantitative:
        "\<forall>N M tau. T \<le> tau \<longrightarrow>
          integrable lborel (\<lambda>c. phi c * integral\<^sup>L lborel (\<lambda>z.
            ?Q z * slp_cgo_born_neumann_remainder
              X N M tau c cutoff coefficient coefficient_tilde z))
          \<and> norm (slp_cgo_born_tested_neumann_remainder_functional
            X N M tau phi ?Q cutoff coefficient coefficient_tilde) \<le>
            (tau / pi) *
            (integral\<^sup>L lborel (\<lambda>c. norm (phi c) *
              slp_common_cgo_born_geometric_majorant
                N M p epsilon C CV C_tilde CV_tilde tau
                coefficient coefficient_tilde c)) *
            (integral\<^sup>L lborel (\<lambda>z. norm (?Q z)))"
    using slp_common_cgo_born_finite_families_eq_neg_remainder_with_bound[
      OF riesz_hls cauchy_test_left_inverse evans_density
        exponent_lower exponent_upper loss_positive loss_upper
        radius_nonnegative radius_lower set_radius center_geometry X_open
        X_bounded Omega_subset cutoff_test cutoff_one cutoff_bound
        cutoff_derivative_zero_bound cutoff_derivative_one_bound
        A0_nonnegative B0_nonnegative B1_nonnegative coefficient_lp
        coefficient_support coefficient_tilde_lp coefficient_tilde_support
        coefficient_normalization coefficient_tilde_normalization domain
        orthogonality phi_test]
    by blast
  note left_parts =
    left_data[unfolded slp_left_neumann_joint_geometric_data_def]
  note CV_positive = conjunct1[OF conjunct2[OF left_parts]]
  note right_parts =
    right_data[unfolded slp_right_neumann_joint_geometric_data_def]
  note CV_tilde_positive = conjunct1[OF conjunct2[OF right_parts]]
  have phi_test_UNIV: "slp_test_function_on UNIV phi"
    using phi_test unfolding slp_test_function_on_def by blast
  let ?majorant_integral = "\<lambda>tau :: real.
    integral\<^sup>L lborel (\<lambda>c. norm (phi c) *
      slp_common_cgo_born_geometric_majorant
        N N p epsilon C CV C_tilde CV_tilde tau
        coefficient coefficient_tilde c)"
  let ?root_mass = "integral\<^sup>L lborel (\<lambda>z. norm (?Q z))"
  let ?remainder = "\<lambda>tau :: real.
    slp_cgo_born_tested_neumann_remainder_functional
      X N N tau phi ?Q cutoff coefficient coefficient_tilde"
  have majorant_limit:
      "((\<lambda>tau :: real. tau * ?majorant_integral tau)
        \<longlongrightarrow> 0) at_top"
    unfolding N_def
    by (rule slp_common_cgo_born_tested_geometric_majorant_tendsto_zero[
      OF exponent_lower exponent_upper loss_positive loss_upper
        less_imp_le[OF CV_positive] less_imp_le[OF CV_tilde_positive]
        coefficient_lp coefficient_tilde_lp phi_test_UNIV])
  have scaled_limit:
      "((\<lambda>tau :: real.
          (tau * ?majorant_integral tau) * (?root_mass / pi))
        \<longlongrightarrow> 0) at_top"
    by (rule tendsto_mult_left_zero[OF majorant_limit])
  have bound_identity:
      "(\<lambda>tau :: real.
          (tau / pi) * ?majorant_integral tau * ?root_mass) =
        (\<lambda>tau :: real.
          (tau * ?majorant_integral tau) * (?root_mass / pi))"
    by (simp add: fun_eq_iff divide_inverse algebra_simps)
  have bound_limit:
      "((\<lambda>tau :: real.
          (tau / pi) * ?majorant_integral tau * ?root_mass)
        \<longlongrightarrow> 0) at_top"
    using scaled_limit unfolding bound_identity .
  have eventual_bound:
      "\<forall>\<^sub>F tau :: real in at_top.
        norm (?remainder tau) \<le>
          (tau / pi) * ?majorant_integral tau * ?root_mass"
    using eventually_ge_at_top[of T]
  proof eventually_elim
    fix tau :: real
    assume tau_large: "T \<le> tau"
    show "norm (?remainder tau) \<le>
        (tau / pi) * ?majorant_integral tau * ?root_mass"
      using quantitative[rule_format, where N=N and M=N and tau=tau]
        tau_large by blast
  qed
  show ?thesis
    by (rule Lim_null_comparison[OF eventual_bound bound_limit])
qed

end

end
