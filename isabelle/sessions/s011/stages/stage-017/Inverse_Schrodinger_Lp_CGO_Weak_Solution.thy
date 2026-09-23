theory Inverse_Schrodinger_Lp_CGO_Weak_Solution
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_Weak_Form_Density_Extension"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Potential-weighted literal CGO fields on the PDE carrier\<close>

lemma slp_both_cgo_potential_products_lp_on:
  fixes p M_left M_right tau :: real
    and c :: slp_point
    and Omega :: "slp_point set"
    and q V W_left W_right :: slp_scalar_field
  assumes exponent_positive: "0 < p"
    and Omega_measurable:
      "Omega \<in> sets (lborel :: slp_point measure)"
    and Omega_bounded: "bounded Omega"
    and q_lp: "aim_complex_lp_on_plane p q"
    and q_normalization: "q = (\<lambda>z. V z / 4)"
    and left_admissible:
      "slp_ae_bounded_measurable lborel M_left W_left"
    and right_admissible:
      "slp_ae_bounded_measurable lborel M_right W_right"
  shows
    "aim_complex_lp_on_plane p
        (slp_restrict_field Omega
          (\<lambda>z. V z * slp_left_cgo_field tau c W_left z))
      \<and>
      aim_complex_lp_on_plane p
        (slp_restrict_field Omega
          (\<lambda>z. V z * slp_right_cgo_field tau c W_right z))"
proof -
  let ?uL = "slp_left_cgo_field tau c W_left"
  let ?uR = "slp_right_cgo_field tau c W_right"
  have q_local: "slp_complex_lp_on p Omega q"
    by (rule aim_complex_lp_on_plane_restrict[OF
          exponent_positive Omega_measurable q_lp])

  have left_M_nonnegative: "0 \<le> M_left"
    and left_measurable: "W_left \<in> borel_measurable lborel"
    and left_bound: "AE x in lborel. norm (W_left x) \<le> M_left"
    using left_admissible unfolding slp_ae_bounded_measurable_def by blast+
  have right_M_nonnegative: "0 \<le> M_right"
    and right_measurable: "W_right \<in> borel_measurable lborel"
    and right_bound: "AE x in lborel. norm (W_right x) \<le> M_right"
    using right_admissible unfolding slp_ae_bounded_measurable_def by blast+

  have left_Wq_plane:
      "aim_complex_lp_on_plane p (\<lambda>x. W_left x * q x)"
    by (rule slp_complex_lp_AE_bounded_multiplier(1)[OF
          exponent_positive left_measurable left_bound left_M_nonnegative q_lp])
  have right_Wq_plane:
      "aim_complex_lp_on_plane p (\<lambda>x. W_right x * q x)"
    by (rule slp_complex_lp_AE_bounded_multiplier(1)[OF
          exponent_positive right_measurable right_bound right_M_nonnegative q_lp])
  have left_Wq_local:
      "slp_complex_lp_on p Omega (\<lambda>x. W_left x * q x)"
    by (rule aim_complex_lp_on_plane_restrict[OF
          exponent_positive Omega_measurable left_Wq_plane])
  have right_Wq_local:
      "slp_complex_lp_on p Omega (\<lambda>x. W_right x * q x)"
    by (rule aim_complex_lp_on_plane_restrict[OF
          exponent_positive Omega_measurable right_Wq_plane])

  have left_base_local:
      "slp_complex_lp_on p Omega
        (\<lambda>x. slp_holomorphic_quadratic_phase_multiplier tau c x * q x)"
    by (rule slp_complex_lp_on_mult_smooth_bounded[OF
          exponent_positive Omega_measurable Omega_bounded q_local
          slp_holomorphic_quadratic_phase_multiplier_has_derivative(2)])
  have left_correction_local:
      "slp_complex_lp_on p Omega
        (\<lambda>x. slp_antiholomorphic_quadratic_phase_multiplier (- tau) c x *
          (W_left x * q x))"
    by (rule slp_complex_lp_on_mult_smooth_bounded[OF
          exponent_positive Omega_measurable Omega_bounded left_Wq_local
          slp_antiholomorphic_quadratic_phase_multiplier_has_derivative(2)])
  have left_sum_local:
      "slp_complex_lp_on p Omega
        (\<lambda>x.
          slp_holomorphic_quadratic_phase_multiplier tau c x * q x +
          slp_antiholomorphic_quadratic_phase_multiplier (- tau) c x *
            (W_left x * q x))"
    by (rule slp_complex_lp_on_add_fields[OF exponent_positive
          left_base_local left_correction_local])
  have left_q_field_local:
      "slp_complex_lp_on p Omega (\<lambda>x. q x * ?uL x)"
  proof -
    have presentation:
        "(\<lambda>x. q x * ?uL x) =
          (\<lambda>x.
            slp_holomorphic_quadratic_phase_multiplier tau c x * q x +
            slp_antiholomorphic_quadratic_phase_multiplier (- tau) c x *
              (W_left x * q x))"
      by (rule ext) (simp add: slp_left_cgo_field_def algebra_simps)
    show ?thesis unfolding presentation by (rule left_sum_local)
  qed

  have right_base_local:
      "slp_complex_lp_on p Omega
        (\<lambda>x. slp_antiholomorphic_quadratic_phase_multiplier tau c x * q x)"
    by (rule slp_complex_lp_on_mult_smooth_bounded[OF
          exponent_positive Omega_measurable Omega_bounded q_local
          slp_antiholomorphic_quadratic_phase_multiplier_has_derivative(2)])
  have right_correction_local:
      "slp_complex_lp_on p Omega
        (\<lambda>x. slp_holomorphic_quadratic_phase_multiplier (- tau) c x *
          (W_right x * q x))"
    by (rule slp_complex_lp_on_mult_smooth_bounded[OF
          exponent_positive Omega_measurable Omega_bounded right_Wq_local
          slp_holomorphic_quadratic_phase_multiplier_has_derivative(2)])
  have right_sum_local:
      "slp_complex_lp_on p Omega
        (\<lambda>x.
          slp_antiholomorphic_quadratic_phase_multiplier tau c x * q x +
          slp_holomorphic_quadratic_phase_multiplier (- tau) c x *
            (W_right x * q x))"
    by (rule slp_complex_lp_on_add_fields[OF exponent_positive
          right_base_local right_correction_local])
  have right_q_field_local:
      "slp_complex_lp_on p Omega (\<lambda>x. q x * ?uR x)"
  proof -
    have presentation:
        "(\<lambda>x. q x * ?uR x) =
          (\<lambda>x.
            slp_antiholomorphic_quadratic_phase_multiplier tau c x * q x +
            slp_holomorphic_quadratic_phase_multiplier (- tau) c x *
              (W_right x * q x))"
      by (rule ext) (simp add: slp_right_cgo_field_def algebra_simps)
    show ?thesis unfolding presentation by (rule right_sum_local)
  qed

  have constant_smooth: "smooth_on UNIV (\<lambda>_::slp_point. 4::complex)"
    by (rule smooth_on_const)
  have left_scaled_local:
      "slp_complex_lp_on p Omega (\<lambda>x. (4::complex) * (q x * ?uL x))"
    by (rule slp_complex_lp_on_mult_smooth_bounded[OF
          exponent_positive Omega_measurable Omega_bounded left_q_field_local
          constant_smooth])
  have right_scaled_local:
      "slp_complex_lp_on p Omega (\<lambda>x. (4::complex) * (q x * ?uR x))"
    by (rule slp_complex_lp_on_mult_smooth_bounded[OF
          exponent_positive Omega_measurable Omega_bounded right_q_field_local
          constant_smooth])
  have left_presentation:
      "(\<lambda>x. (4::complex) * (q x * ?uL x)) =
        (\<lambda>x. V x * ?uL x)"
    by (rule ext) (simp add: q_normalization)
  have right_presentation:
      "(\<lambda>x. (4::complex) * (q x * ?uR x)) =
        (\<lambda>x. V x * ?uR x)"
    by (rule ext) (simp add: q_normalization)
  have left_weighted_local:
      "slp_complex_lp_on p Omega (\<lambda>x. V x * ?uL x)"
    using left_scaled_local unfolding left_presentation .
  have right_weighted_local:
      "slp_complex_lp_on p Omega (\<lambda>x. V x * ?uR x)"
    using right_scaled_local unfolding right_presentation .
  show ?thesis
    using left_weighted_local right_weighted_local
    unfolding slp_complex_lp_on_def by blast
qed

section \<open>Literal affine-fixed-point CGO weak solutions\<close>

locale slp_cgo_full_weak_solution_context =
  slp_cauchy_outer_fixed_point + slp_qstar_centered_smooth_far_hls_context

context slp_cgo_full_weak_solution_context
begin

theorem slp_both_affine_fixed_point_cgo_fields_weak_solution:
  fixes p M_left M_right tau :: real
    and c :: slp_point
    and X Omega :: "slp_point set"
    and cutoff q V W_left W_right :: slp_scalar_field
  assumes exponent_lower: "1 < p"
    and exponent_upper: "p < 2"
    and X_open: "open X"
    and X_bounded: "bounded X"
    and Omega_measurable:
      "Omega \<in> sets (lborel :: slp_point measure)"
    and Omega_bounded: "bounded Omega"
    and Omega_subset: "Omega \<subseteq> X"
    and cutoff_test: "slp_test_function_on X cutoff"
    and cutoff_one: "\<And>z. z \<in> Omega \<Longrightarrow> cutoff z = 1"
    and q_lp: "aim_complex_lp_on_plane p q"
    and q_support: "{x. q x \<noteq> 0} \<subseteq> X"
    and q_normalization: "q = (\<lambda>z. V z / 4)"
    and left_admissible:
      "slp_ae_bounded_measurable lborel M_left W_left"
    and right_admissible:
      "slp_ae_bounded_measurable lborel M_right W_right"
    and left_fixed:
      "AE z in lborel.
        W_left z =
          slp_restrict_field X
            (slp_left_neumann_base tau c cutoff q SLP_Dbar_Inverse) z +
          slp_restrict_field X
            (slp_left_neumann_step tau c cutoff q W_left) z"
    and right_fixed:
      "AE z in lborel.
        W_right z =
          slp_restrict_field X
            (slp_right_neumann_base tau c cutoff q SLP_Partial_Inverse) z +
          slp_restrict_field X
            (slp_right_neumann_step tau c cutoff q W_right) z"
  shows
    "slp_weak_solution Omega V
        (slp_left_cgo_field tau c W_left,
          slp_left_cgo_gradient tau c W_left
            (slp_left_outer_conjugated_gradient tau c cutoff q W_left))
      \<and>
      slp_weak_solution Omega V
        (slp_right_cgo_field tau c W_right,
          slp_right_cgo_gradient tau c W_right
            (slp_right_outer_conjugated_gradient tau c cutoff q W_right))"
proof -
  let ?FL =
    "(slp_left_cgo_field tau c W_left,
      slp_left_cgo_gradient tau c W_left
        (slp_left_outer_conjugated_gradient tau c cutoff q W_left))"
  let ?FR =
    "(slp_right_cgo_field tau c W_right,
      slp_right_cgo_gradient tau c W_right
        (slp_right_outer_conjugated_gradient tau c cutoff q W_right))"
  have exponent_positive: "0 < p" using exponent_lower by linarith
  note smooth =
    slp_both_affine_fixed_point_cgo_fields_smooth_weak_solution[OF
      exponent_lower exponent_upper X_open X_bounded Omega_measurable
      Omega_bounded Omega_subset cutoff_test cutoff_one q_lp q_support
      q_normalization left_admissible right_admissible left_fixed right_fixed]
  have left_h1: "slp_h1_data_on Omega ?FL" using smooth by blast
  have right_h1: "slp_h1_data_on Omega ?FR" using smooth by blast
  have left_tests:
      "\<forall>phi. slp_test_function_on Omega phi \<longrightarrow>
        slp_weak_form_integrable Omega V ?FL
          (phi, slp_classical_gradient phi) \<and>
        slp_weak_form Omega V ?FL
          (phi, slp_classical_gradient phi) = 0"
    using smooth by blast
  have right_tests:
      "\<forall>phi. slp_test_function_on Omega phi \<longrightarrow>
        slp_weak_form_integrable Omega V ?FR
          (phi, slp_classical_gradient phi) \<and>
        slp_weak_form Omega V ?FR
          (phi, slp_classical_gradient phi) = 0"
    using smooth by blast
  note weighted = slp_both_cgo_potential_products_lp_on[OF
    exponent_positive Omega_measurable Omega_bounded q_lp q_normalization
    left_admissible right_admissible]
  have left_weighted:
      "aim_complex_lp_on_plane p
        (slp_restrict_field Omega (\<lambda>x. V x * fst ?FL x))"
    using weighted by simp
  have right_weighted:
      "aim_complex_lp_on_plane p
        (slp_restrict_field Omega (\<lambda>x. V x * fst ?FR x))"
    using weighted by simp
  have left_solution: "slp_weak_solution Omega V ?FL"
    by (rule slp_smooth_test_weak_form_dense[OF
          exponent_lower exponent_upper Omega_measurable Omega_bounded
          left_h1 left_weighted left_tests])
  have right_solution: "slp_weak_solution Omega V ?FR"
    by (rule slp_smooth_test_weak_form_dense[OF
          exponent_lower exponent_upper Omega_measurable Omega_bounded
          right_h1 right_weighted right_tests])
  show ?thesis using left_solution right_solution by blast
qed

end

end
