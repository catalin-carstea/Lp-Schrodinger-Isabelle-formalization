theory Inverse_Schrodinger_Lp_Left_Neumann_Step_Difference
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Left_Neumann_Step_AE_Contraction"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Nested_Coefficient_Difference_Pointwise"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Difference law for the literal restricted left step\<close>

context slp_cauchy_local_w1s
begin

theorem slp_left_neumann_step_restricted_difference:
  fixes p K L :: real
    and X :: "slp_point set"
    and cutoff coefficient f g :: slp_scalar_field
  assumes riesz_hls: "aim_planar_riesz_hls_claim"
    and exponent_lower: "1 < p"
    and exponent_upper: "p < 2"
    and X_bounded: "bounded X"
    and cutoff_test: "slp_test_function_on X cutoff"
    and coefficient_lp: "aim_complex_lp_on_plane p coefficient"
    and first_admissible: "slp_ae_bounded_measurable lborel K f"
    and second_admissible: "slp_ae_bounded_measurable lborel L g"
  shows
    "slp_restrict_field X
        (slp_left_neumann_step tau c cutoff coefficient
          (\<lambda>y. f y - g y)) =
      (\<lambda>z.
        slp_restrict_field X
            (slp_left_neumann_step tau c cutoff coefficient f) z -
          slp_restrict_field X
            (slp_left_neumann_step tau c cutoff coefficient g) z)"
proof -
  have p_positive: "0 < p"
    using exponent_lower by linarith
  have K_nonnegative: "0 \<le> K"
    and f_measurable: "f \<in> borel_measurable lborel"
    and f_bound: "AE x in lborel. norm (f x) \<le> K"
    using first_admissible
    unfolding slp_ae_bounded_measurable_def by blast+
  have L_nonnegative: "0 \<le> L"
    and g_measurable: "g \<in> borel_measurable lborel"
    and g_bound: "AE x in lborel. norm (g x) \<le> L"
    using second_admissible
    unfolding slp_ae_bounded_measurable_def by blast+

  have first_product_lp:
      "aim_complex_lp_on_plane p
        (\<lambda>y. coefficient y * f y)"
  proof -
    have
      "aim_complex_lp_on_plane p
        (\<lambda>y. f y * coefficient y)"
      by (rule slp_complex_lp_AE_bounded_multiplier(1)[
            OF p_positive f_measurable f_bound K_nonnegative
              coefficient_lp])
    then show ?thesis
      by (simp only: mult.commute)
  qed
  have second_product_lp:
      "aim_complex_lp_on_plane p
        (\<lambda>y. coefficient y * g y)"
  proof -
    have
      "aim_complex_lp_on_plane p
        (\<lambda>y. g y * coefficient y)"
      by (rule slp_complex_lp_AE_bounded_multiplier(1)[
            OF p_positive g_measurable g_bound L_nonnegative
              coefficient_lp])
    then show ?thesis
      by (simp only: mult.commute)
  qed

  have pointwise_context: "aim_planar_riesz_hls_cauchy"
    using riesz_hls aim_planar_hls_cauchy by unfold_locales
  have nested_difference:
      "\<forall>z\<in>X.
        slp_partial_psi_inverse tau c
            (\<lambda>x. cutoff x *
              slp_dbar_psi_inverse tau c
                (\<lambda>y. coefficient y * f y - coefficient y * g y) x) z =
          slp_partial_psi_inverse tau c
              (\<lambda>x. cutoff x *
                slp_dbar_psi_inverse tau c
                  (\<lambda>y. coefficient y * f y) x) z -
            slp_partial_psi_inverse tau c
              (\<lambda>x. cutoff x *
                slp_dbar_psi_inverse tau c
                  (\<lambda>y. coefficient y * g y) x) z
        \<and>
        slp_dbar_psi_inverse (- tau) c
            (\<lambda>x. cutoff x *
              slp_partial_psi_inverse (- tau) c
                (\<lambda>y. coefficient y * f y - coefficient y * g y) x) z =
          slp_dbar_psi_inverse (- tau) c
              (\<lambda>x. cutoff x *
                slp_partial_psi_inverse (- tau) c
                  (\<lambda>y. coefficient y * f y) x) z -
            slp_dbar_psi_inverse (- tau) c
              (\<lambda>x. cutoff x *
                slp_partial_psi_inverse (- tau) c
                  (\<lambda>y. coefficient y * g y) x) z"
    by (rule aim_planar_riesz_hls_cauchy.slp_both_nested_oscillatory_cauchy_difference_pointwise[
          OF pointwise_context exponent_lower exponent_upper X_bounded
            cutoff_test first_product_lp second_product_lp])
  have step_difference:
      "\<forall>z\<in>X.
        slp_left_neumann_step tau c cutoff coefficient
            (\<lambda>y. f y - g y) z =
          slp_left_neumann_step tau c cutoff coefficient f z -
            slp_left_neumann_step tau c cutoff coefficient g z"
    using nested_difference
    unfolding slp_left_neumann_step_def
    by (simp add: algebra_simps)

  show ?thesis
  proof (rule ext)
    fix z :: slp_point
    show
      "slp_restrict_field X
          (slp_left_neumann_step tau c cutoff coefficient
            (\<lambda>y. f y - g y)) z =
        slp_restrict_field X
            (slp_left_neumann_step tau c cutoff coefficient f) z -
          slp_restrict_field X
            (slp_left_neumann_step tau c cutoff coefficient g) z"
    proof (cases "z \<in> X")
      case True
      then show ?thesis
        using step_difference
        by (simp add: slp_restrict_field_def)
    next
      case False
      then show ?thesis
        by (simp add: slp_restrict_field_def)
    qed
  qed
qed

end

end
