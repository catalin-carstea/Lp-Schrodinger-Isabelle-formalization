theory Inverse_Schrodinger_Lp_Cutoff_Conjugated_Source_Lp
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Outer_Conjugated_Source_Weak_Wirtinger"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Local_W1s_Cutoff_Zero_Pair"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_AE_Neumann_Sum_Fixed_Point"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Bounded_Support_Lp_Norm"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Local_Smooth_Multiplier"
begin

section \<open>Elementary local Lp and support closures\<close>

lemma slp_complex_lp_on_add_fields:
  assumes exponent_positive: "0 < p"
    and first_lp: "slp_complex_lp_on p X f"
    and second_lp: "slp_complex_lp_on p X g"
  shows "slp_complex_lp_on p X (\<lambda>x. f x + g x)"
proof -
  have raw:
      "aim_complex_lp_on_plane p
        (\<lambda>x. slp_restrict_field X f x + slp_restrict_field X g x)"
    by (rule aim_complex_lp_on_plane_add[OF exponent_positive])
      (use first_lp second_lp in
        \<open>auto simp: slp_complex_lp_on_def\<close>)
  have presentation:
      "slp_restrict_field X (\<lambda>x. f x + g x) =
        (\<lambda>x. slp_restrict_field X f x + slp_restrict_field X g x)"
    by (rule ext) (simp add: slp_restrict_field_def)
  show ?thesis
    unfolding slp_complex_lp_on_def presentation
    by (rule raw)
qed

lemma slp_complex_lp_on_diff_fields:
  assumes exponent_positive: "0 < p"
    and first_lp: "slp_complex_lp_on p X f"
    and second_lp: "slp_complex_lp_on p X g"
  shows "slp_complex_lp_on p X (\<lambda>x. f x - g x)"
proof -
  have raw:
      "aim_complex_lp_on_plane p
        (\<lambda>x. slp_restrict_field X f x - slp_restrict_field X g x)"
    by (rule aim_complex_lp_on_plane_diff[OF exponent_positive])
      (use first_lp second_lp in
        \<open>auto simp: slp_complex_lp_on_def\<close>)
  have presentation:
      "slp_restrict_field X (\<lambda>x. f x - g x) =
        (\<lambda>x. slp_restrict_field X f x - slp_restrict_field X g x)"
    by (rule ext) (simp add: slp_restrict_field_def)
  show ?thesis
    unfolding slp_complex_lp_on_def presentation
    by (rule raw)
qed

lemma slp_mult_test_support_bounded:
  assumes cutoff_test: "slp_test_function_on X cutoff"
  shows "bounded {x. cutoff x * f x \<noteq> 0}"
proof -
  let ?K = "closure {x. cutoff x \<noteq> 0}"
  have K_compact: "compact ?K"
    using cutoff_test unfolding slp_test_function_on_def by blast
  have product_support_subset:
      "{x. cutoff x * f x \<noteq> 0} \<subseteq> ?K"
    using closure_subset by auto
  show ?thesis
    by (rule bounded_subset[OF compact_imp_bounded[OF K_compact]
          product_support_subset])
qed

section \<open>Both exact cutoff conjugated sources\<close>

context slp_cauchy_local_w1s
begin

theorem slp_both_cutoff_conjugated_sources_lp_support:
  fixes p M tau :: real
    and c :: slp_point
    and X :: "slp_point set"
    and cutoff coefficient W :: slp_scalar_field
  assumes exponent_lower: "1 < (p::real)"
    and X_open: "open X"
    and X_bounded: "bounded X"
    and cutoff_test: "slp_test_function_on X cutoff"
    and coefficient_lp: "aim_complex_lp_on_plane p coefficient"
    and coefficient_support: "{x. coefficient x \<noteq> 0} \<subseteq> X"
    and W_admissible: "slp_ae_bounded_measurable lborel M W"
  shows
    "aim_complex_lp_on_plane p
        (\<lambda>x. cutoff x *
          slp_left_conjugated_cauchy_source tau c coefficient
            (\<lambda>y. coefficient y * W y) x)
      \<and>
      bounded {x. cutoff x *
        slp_left_conjugated_cauchy_source tau c coefficient
          (\<lambda>y. coefficient y * W y) x \<noteq> 0}
      \<and>
      aim_complex_lp_on_plane p
        (\<lambda>x. cutoff x *
          slp_right_conjugated_cauchy_source tau c coefficient
            (\<lambda>y. coefficient y * W y) x)
      \<and>
      bounded {x. cutoff x *
        slp_right_conjugated_cauchy_source tau c coefficient
          (\<lambda>y. coefficient y * W y) x \<noteq> 0}"
proof -
  let ?product = "\<lambda>x. coefficient x * W x"
  let ?modulated = "slp_oscillatory_modulation (- tau) c ?product"
  let ?left =
    "slp_left_conjugated_cauchy_source tau c coefficient ?product"
  let ?right =
    "slp_right_conjugated_cauchy_source tau c coefficient ?product"

  have exponent_positive: "0 < p"
    using exponent_lower by linarith
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
  have product_support_subset:
      "{x. ?product x \<noteq> 0} \<subseteq> {x. coefficient x \<noteq> 0}"
    by auto
  have product_support_in_X: "{x. ?product x \<noteq> 0} \<subseteq> X"
    by (rule subset_trans[OF product_support_subset coefficient_support])
  have coefficient_support_bounded: "bounded {x. coefficient x \<noteq> 0}"
    by (rule bounded_subset[OF X_bounded coefficient_support])
  have product_support_bounded: "bounded {x. ?product x \<noteq> 0}"
    by (rule bounded_subset[OF coefficient_support_bounded
          product_support_subset])
  have modulated_lp: "aim_complex_lp_on_plane p ?modulated"
    using product_lp by simp
  have modulated_support_bounded: "bounded {x. ?modulated x \<noteq> 0}"
    using product_support_bounded by simp

  note coefficient_data = slp_both_cauchy_local_w1s_certificates[OF
    exponent_lower coefficient_lp coefficient_support_bounded X_measurable
    X_bounded]
  note product_data = slp_both_cauchy_local_w1s_certificates[OF
    exponent_lower modulated_lp modulated_support_bounded X_measurable
    X_bounded]
  have coefficient_dbar_lp:
      "slp_complex_lp_on p X (slp_dbar_inverse coefficient)"
    using coefficient_data unfolding slp_local_w1s_certificate_def by blast
  have coefficient_partial_lp:
      "slp_complex_lp_on p X (slp_partial_inverse coefficient)"
    using coefficient_data unfolding slp_local_w1s_certificate_def by blast
  have product_dbar_lp:
      "slp_complex_lp_on p X
        (slp_dbar_psi_inverse tau c ?product)"
    using product_data
    unfolding slp_local_w1s_certificate_def slp_dbar_psi_inverse_def by blast
  have product_partial_lp:
      "slp_complex_lp_on p X
        (slp_partial_psi_inverse (- tau) c ?product)"
    using product_data
    unfolding slp_local_w1s_certificate_def slp_partial_psi_inverse_def
    by simp

  have dbar_constant_lp:
      "slp_complex_lp_on p X
        (\<lambda>_. slp_dbar_inverse coefficient c)"
    unfolding slp_complex_lp_on_def
    by (rule slp_bounded_restriction_lp_norm(1)[
          where A="Real_Vector_Spaces.norm (slp_dbar_inverse coefficient c)", OF
          exponent_positive X_measurable X_bounded]; simp)
  have partial_constant_lp:
      "slp_complex_lp_on p X
        (\<lambda>_. slp_partial_inverse coefficient c)"
    unfolding slp_complex_lp_on_def
    by (rule slp_bounded_restriction_lp_norm(1)[
          where A="Real_Vector_Spaces.norm (slp_partial_inverse coefficient c)", OF
          exponent_positive X_measurable X_bounded]; simp)
  have left_centered_lp:
      "slp_complex_lp_on p X
        (\<lambda>x. slp_dbar_inverse coefficient x -
          slp_dbar_inverse coefficient c)"
    by (rule slp_complex_lp_on_diff_fields[OF exponent_positive
          coefficient_dbar_lp dbar_constant_lp])
  have right_centered_lp:
      "slp_complex_lp_on p X
        (\<lambda>x. slp_partial_inverse coefficient x -
          slp_partial_inverse coefficient c)"
    by (rule slp_complex_lp_on_diff_fields[OF exponent_positive
          coefficient_partial_lp partial_constant_lp])
  have left_local_lp: "slp_complex_lp_on p X ?left"
    unfolding slp_left_conjugated_cauchy_source_def
    by (rule slp_complex_lp_on_add_fields[OF exponent_positive
          left_centered_lp product_dbar_lp])
  have right_local_lp: "slp_complex_lp_on p X ?right"
    unfolding slp_right_conjugated_cauchy_source_def
    by (rule slp_complex_lp_on_add_fields[OF exponent_positive
          right_centered_lp product_partial_lp])

  have left_cutoff_local_lp:
      "slp_complex_lp_on p X (\<lambda>x. cutoff x * ?left x)"
    by (rule slp_complex_lp_on_mult_smooth_bounded[OF exponent_positive
          X_measurable X_bounded left_local_lp cutoff_smooth])
  have right_cutoff_local_lp:
      "slp_complex_lp_on p X (\<lambda>x. cutoff x * ?right x)"
    by (rule slp_complex_lp_on_mult_smooth_bounded[OF exponent_positive
          X_measurable X_bounded right_local_lp cutoff_smooth])
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
  have left_global_lp:
      "aim_complex_lp_on_plane p (\<lambda>x. cutoff x * ?left x)"
    using left_cutoff_local_lp
    unfolding slp_complex_lp_on_def left_restrict .
  have right_global_lp:
      "aim_complex_lp_on_plane p (\<lambda>x. cutoff x * ?right x)"
    using right_cutoff_local_lp
    unfolding slp_complex_lp_on_def right_restrict .
  have left_support_bounded:
      "bounded {x. cutoff x * ?left x \<noteq> 0}"
    by (rule slp_mult_test_support_bounded[OF cutoff_test])
  have right_support_bounded:
      "bounded {x. cutoff x * ?right x \<noteq> 0}"
    by (rule slp_mult_test_support_bounded[OF cutoff_test])

  show ?thesis
    using left_global_lp left_support_bounded right_global_lp
      right_support_bounded by blast
qed

end

end
