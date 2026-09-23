theory Inverse_Schrodinger_Lp_Cutoff_Conjugated_Source_Lpstar
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Outer_Affine_Fixed_Point_AE"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Qstar_Exponent_Arithmetic"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Above-two integrability of the exact cutoff conjugated sources\<close>

context slp_cauchy_outer_fixed_point
begin

theorem slp_both_cutoff_conjugated_sources_lpstar_support:
  fixes p M tau :: real
    and c :: slp_point
    and X :: "slp_point set"
    and cutoff coefficient W :: slp_scalar_field
  assumes exponent_lower: "1 < p"
    and exponent_upper: "p < 2"
    and X_open: "open X"
    and X_bounded: "bounded X"
    and cutoff_test: "slp_test_function_on X cutoff"
    and coefficient_lp: "aim_complex_lp_on_plane p coefficient"
    and coefficient_support: "{x. coefficient x \<noteq> 0} \<subseteq> X"
    and W_admissible: "slp_ae_bounded_measurable lborel M W"
  shows
    "aim_complex_lp_on_plane (aim_hls_target_exponent p)
        (\<lambda>x. cutoff x *
          slp_left_conjugated_cauchy_source tau c coefficient
            (\<lambda>y. coefficient y * W y) x)
      \<and>
      bounded {x. cutoff x *
        slp_left_conjugated_cauchy_source tau c coefficient
          (\<lambda>y. coefficient y * W y) x \<noteq> 0}
      \<and>
      aim_complex_lp_on_plane (aim_hls_target_exponent p)
        (\<lambda>x. cutoff x *
          slp_right_conjugated_cauchy_source tau c coefficient
            (\<lambda>y. coefficient y * W y) x)
      \<and>
      bounded {x. cutoff x *
        slp_right_conjugated_cauchy_source tau c coefficient
          (\<lambda>y. coefficient y * W y) x \<noteq> 0}"
proof -
  let ?qstar = "aim_hls_target_exponent p"
  let ?product = "\<lambda>x. coefficient x * W x"
  let ?modulated = "slp_oscillatory_modulation (- tau) c ?product"
  let ?left =
    "slp_left_conjugated_cauchy_source tau c coefficient ?product"
  let ?right =
    "slp_right_conjugated_cauchy_source tau c coefficient ?product"

  have exponent_positive: "0 < p"
    using exponent_lower by linarith
  have target_positive: "0 < ?qstar"
    using slp_qstar_exponent_relations(1)[OF exponent_lower exponent_upper]
    by linarith
  have X_measurable: "X \<in> sets (lborel :: slp_point measure)"
    using X_open by simp
  have cutoff_smooth: "smooth_on UNIV cutoff"
    using cutoff_test unfolding slp_test_function_on_def by blast
  have cutoff_restrict: "slp_restrict_field X cutoff = cutoff"
    by (rule slp_test_function_restrict_field_eq[OF cutoff_test])

  have M_nonnegative: "0 \<le> M"
    and W_measurable: "W \<in> borel_measurable lborel"
    and W_bound:
      "AE x in lborel. Real_Vector_Spaces.norm (W x) \<le> M"
    using W_admissible unfolding slp_ae_bounded_measurable_def by blast+
  have product_lp: "aim_complex_lp_on_plane p ?product"
  proof -
    have raw:
        "aim_complex_lp_on_plane p (\<lambda>x. W x * coefficient x)"
      by (rule slp_complex_lp_AE_bounded_multiplier(1)[OF
            exponent_positive W_measurable W_bound M_nonnegative
            coefficient_lp])
    show ?thesis
      using raw by (simp only: mult.commute)
  qed
  have modulated_lp: "aim_complex_lp_on_plane p ?modulated"
    using product_lp by simp

  have coefficient_cauchy_lpstar:
      "aim_complex_lp_on_plane ?qstar (slp_dbar_inverse coefficient) \<and>
        aim_complex_lp_on_plane ?qstar (slp_partial_inverse coefficient)"
    using slp_both_cauchy_hls exponent_lower exponent_upper coefficient_lp
    by blast
  have product_cauchy_lpstar:
      "aim_complex_lp_on_plane ?qstar (slp_dbar_inverse ?modulated) \<and>
        aim_complex_lp_on_plane ?qstar (slp_partial_inverse ?modulated)"
    using slp_both_cauchy_hls exponent_lower exponent_upper modulated_lp
    by blast

  have coefficient_dbar_local:
      "slp_complex_lp_on ?qstar X (slp_dbar_inverse coefficient)"
    by (rule aim_complex_lp_on_plane_restrict[OF target_positive X_measurable])
       (use coefficient_cauchy_lpstar in blast)
  have coefficient_partial_local:
      "slp_complex_lp_on ?qstar X (slp_partial_inverse coefficient)"
    by (rule aim_complex_lp_on_plane_restrict[OF target_positive X_measurable])
       (use coefficient_cauchy_lpstar in blast)
  have product_dbar_local:
      "slp_complex_lp_on ?qstar X (slp_dbar_psi_inverse tau c ?product)"
    unfolding slp_dbar_psi_inverse_def
    by (rule aim_complex_lp_on_plane_restrict[OF target_positive X_measurable])
       (use product_cauchy_lpstar in blast)
  have product_partial_local:
      "slp_complex_lp_on ?qstar X (slp_partial_psi_inverse (- tau) c ?product)"
    unfolding slp_partial_psi_inverse_def
    by (rule aim_complex_lp_on_plane_restrict[OF target_positive X_measurable])
       (use product_cauchy_lpstar in simp)

  have dbar_constant_local:
      "slp_complex_lp_on ?qstar X
        (\<lambda>_. slp_dbar_inverse coefficient c)"
    unfolding slp_complex_lp_on_def
    by (rule slp_bounded_restriction_lp_norm(1)[
          where A="Real_Vector_Spaces.norm (slp_dbar_inverse coefficient c)",
          OF target_positive X_measurable X_bounded]; simp)
  have partial_constant_local:
      "slp_complex_lp_on ?qstar X
        (\<lambda>_. slp_partial_inverse coefficient c)"
    unfolding slp_complex_lp_on_def
    by (rule slp_bounded_restriction_lp_norm(1)[
          where A="Real_Vector_Spaces.norm (slp_partial_inverse coefficient c)",
          OF target_positive X_measurable X_bounded]; simp)
  have left_centered_local:
      "slp_complex_lp_on ?qstar X
        (\<lambda>x. slp_dbar_inverse coefficient x -
          slp_dbar_inverse coefficient c)"
    by (rule slp_complex_lp_on_diff_fields[OF target_positive
          coefficient_dbar_local dbar_constant_local])
  have right_centered_local:
      "slp_complex_lp_on ?qstar X
        (\<lambda>x. slp_partial_inverse coefficient x -
          slp_partial_inverse coefficient c)"
    by (rule slp_complex_lp_on_diff_fields[OF target_positive
          coefficient_partial_local partial_constant_local])
  have left_local: "slp_complex_lp_on ?qstar X ?left"
    unfolding slp_left_conjugated_cauchy_source_def
    by (rule slp_complex_lp_on_add_fields[OF target_positive
          left_centered_local product_dbar_local])
  have right_local: "slp_complex_lp_on ?qstar X ?right"
    unfolding slp_right_conjugated_cauchy_source_def
    by (rule slp_complex_lp_on_add_fields[OF target_positive
          right_centered_local product_partial_local])

  have left_cutoff_local:
      "slp_complex_lp_on ?qstar X (\<lambda>x. cutoff x * ?left x)"
    by (rule slp_complex_lp_on_mult_smooth_bounded[OF target_positive
          X_measurable X_bounded left_local cutoff_smooth])
  have right_cutoff_local:
      "slp_complex_lp_on ?qstar X (\<lambda>x. cutoff x * ?right x)"
    by (rule slp_complex_lp_on_mult_smooth_bounded[OF target_positive
          X_measurable X_bounded right_local cutoff_smooth])
  have left_restrict:
      "slp_restrict_field X (\<lambda>x. cutoff x * ?left x) =
        (\<lambda>x. cutoff x * ?left x)"
  proof (rule ext)
    fix x
    have cutoff_at_x: "slp_restrict_field X cutoff x = cutoff x"
      by (rule fun_cong[OF cutoff_restrict])
    show "slp_restrict_field X (\<lambda>x. cutoff x * ?left x) x =
        cutoff x * ?left x"
      using cutoff_at_x
      by (cases "x \<in> X") (simp_all add: slp_restrict_field_def)
  qed
  have right_restrict:
      "slp_restrict_field X (\<lambda>x. cutoff x * ?right x) =
        (\<lambda>x. cutoff x * ?right x)"
  proof (rule ext)
    fix x
    have cutoff_at_x: "slp_restrict_field X cutoff x = cutoff x"
      by (rule fun_cong[OF cutoff_restrict])
    show "slp_restrict_field X (\<lambda>x. cutoff x * ?right x) x =
        cutoff x * ?right x"
      using cutoff_at_x
      by (cases "x \<in> X") (simp_all add: slp_restrict_field_def)
  qed
  have left_global:
      "aim_complex_lp_on_plane ?qstar (\<lambda>x. cutoff x * ?left x)"
    using left_cutoff_local
    unfolding slp_complex_lp_on_def left_restrict .
  have right_global:
      "aim_complex_lp_on_plane ?qstar (\<lambda>x. cutoff x * ?right x)"
    using right_cutoff_local
    unfolding slp_complex_lp_on_def right_restrict .
  have left_support: "bounded {x. cutoff x * ?left x \<noteq> 0}"
    by (rule slp_mult_test_support_bounded[OF cutoff_test])
  have right_support: "bounded {x. cutoff x * ?right x \<noteq> 0}"
    by (rule slp_mult_test_support_bounded[OF cutoff_test])

  show ?thesis
    using left_global left_support right_global right_support by blast
qed

end

end
