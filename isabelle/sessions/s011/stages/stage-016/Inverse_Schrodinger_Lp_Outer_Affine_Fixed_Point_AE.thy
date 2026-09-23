theory Inverse_Schrodinger_Lp_Outer_Affine_Fixed_Point_AE
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Cutoff_Conjugated_Source_Lp"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Oscillatory_Cauchy_Difference_AE"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Global Lp data for the four affine source summands\<close>

context slp_cauchy_local_w1s
begin

theorem slp_both_cutoff_neumann_source_summands_lp:
  fixes p M tau :: real
    and c :: slp_point
    and X :: "slp_point set"
    and cutoff coefficient W :: slp_scalar_field
  assumes exponent_lower: "1 < p"
    and X_open: "open X"
    and X_bounded: "bounded X"
    and cutoff_test: "slp_test_function_on X cutoff"
    and coefficient_lp: "aim_complex_lp_on_plane p coefficient"
    and coefficient_support: "{x. coefficient x \<noteq> 0} \<subseteq> X"
    and W_admissible: "slp_ae_bounded_measurable lborel M W"
  shows
    "aim_complex_lp_on_plane p
        (\<lambda>x. cutoff x *
          (slp_dbar_inverse coefficient x -
            slp_dbar_inverse coefficient c))
      \<and>
      aim_complex_lp_on_plane p
        (\<lambda>x. cutoff x *
          slp_dbar_psi_inverse tau c
            (\<lambda>y. coefficient y * W y) x)
      \<and>
      aim_complex_lp_on_plane p
        (\<lambda>x. cutoff x *
          (slp_partial_inverse coefficient x -
            slp_partial_inverse coefficient c))
      \<and>
      aim_complex_lp_on_plane p
        (\<lambda>x. cutoff x *
          slp_partial_psi_inverse (- tau) c
            (\<lambda>y. coefficient y * W y) x)"
proof -
  let ?left_total =
    "\<lambda>x. cutoff x *
      slp_left_conjugated_cauchy_source tau c coefficient
        (\<lambda>y. coefficient y * W y) x"
  let ?right_total =
    "\<lambda>x. cutoff x *
      slp_right_conjugated_cauchy_source tau c coefficient
        (\<lambda>y. coefficient y * W y) x"
  let ?left_base =
    "\<lambda>x. cutoff x *
      (slp_dbar_inverse coefficient x -
        slp_dbar_inverse coefficient c)"
  let ?right_base =
    "\<lambda>x. cutoff x *
      (slp_partial_inverse coefficient x -
        slp_partial_inverse coefficient c)"
  let ?left_step =
    "\<lambda>x. cutoff x *
      slp_dbar_psi_inverse tau c
        (\<lambda>y. coefficient y * W y) x"
  let ?right_step =
    "\<lambda>x. cutoff x *
      slp_partial_psi_inverse (- tau) c
        (\<lambda>y. coefficient y * W y) x"

  have exponent_positive: "0 < p"
    using exponent_lower by linarith
  have zero_admissible:
      "slp_ae_bounded_measurable lborel 0
        (\<lambda>_ :: slp_point. 0 :: complex)"
    by (rule slp_ae_bounded_measurable_zero)
  note actual_data = slp_both_cutoff_conjugated_sources_lp_support[OF
    exponent_lower X_open X_bounded cutoff_test coefficient_lp
    coefficient_support W_admissible]
  note zero_data = slp_both_cutoff_conjugated_sources_lp_support[OF
    exponent_lower X_open X_bounded cutoff_test coefficient_lp
    coefficient_support zero_admissible]

  have dbar_integrand_zero:
      "slp_cauchy_integrand SLP_Dbar_Inverse
        (slp_oscillatory_modulation (- tau) c
          (\<lambda>_ :: slp_point. 0)) z =
        (\<lambda>_. 0)" for z
    by (rule ext)
      (simp add: slp_cauchy_integrand_def
        slp_oscillatory_modulation_def)
  have dbar_zero:
      "slp_dbar_psi_inverse tau c (\<lambda>_ :: slp_point. 0) =
        (\<lambda>_. 0)"
    by (rule ext)
      (simp add: slp_dbar_psi_inverse_def slp_cauchy_transform_def
        dbar_integrand_zero)
  have partial_integrand_zero:
      "slp_cauchy_integrand SLP_Partial_Inverse
        (slp_oscillatory_modulation (- tau) c
          (\<lambda>_ :: slp_point. 0)) z =
        (\<lambda>_. 0)" for z
    by (rule ext)
      (simp add: slp_cauchy_integrand_def
        slp_oscillatory_modulation_def)
  have partial_zero:
      "slp_partial_psi_inverse (- tau) c (\<lambda>_ :: slp_point. 0) =
        (\<lambda>_. 0)"
    by (rule ext)
      (simp add: slp_partial_psi_inverse_def slp_cauchy_transform_def
        partial_integrand_zero)
  have left_base_lp: "aim_complex_lp_on_plane p ?left_base"
    using zero_data[where tau = tau and c = c] dbar_zero
    by (simp add: slp_left_conjugated_cauchy_source_def)
  have right_base_lp: "aim_complex_lp_on_plane p ?right_base"
    using zero_data[where tau = tau and c = c] partial_zero
    by (simp add: slp_right_conjugated_cauchy_source_def)
  have left_total_lp: "aim_complex_lp_on_plane p ?left_total"
    using actual_data by blast
  have right_total_lp: "aim_complex_lp_on_plane p ?right_total"
    using actual_data by blast

  have left_difference_lp:
      "aim_complex_lp_on_plane p (\<lambda>x. ?left_total x - ?left_base x)"
    by (rule aim_complex_lp_on_plane_diff[OF exponent_positive
          left_total_lp left_base_lp])
  have left_difference_eq:
      "(\<lambda>x. ?left_total x - ?left_base x) = ?left_step"
    by (rule ext)
      (simp add: slp_left_conjugated_cauchy_source_def algebra_simps)
  have left_step_lp: "aim_complex_lp_on_plane p ?left_step"
    using left_difference_lp by (simp only: left_difference_eq)

  have right_difference_lp:
      "aim_complex_lp_on_plane p (\<lambda>x. ?right_total x - ?right_base x)"
    by (rule aim_complex_lp_on_plane_diff[OF exponent_positive
          right_total_lp right_base_lp])
  have right_difference_eq:
      "(\<lambda>x. ?right_total x - ?right_base x) = ?right_step"
    by (rule ext)
      (simp add: slp_right_conjugated_cauchy_source_def algebra_simps)
  have right_step_lp: "aim_complex_lp_on_plane p ?right_step"
    using right_difference_lp by (simp only: right_difference_eq)

  show ?thesis
    using left_base_lp left_step_lp right_base_lp right_step_lp by blast
qed

end

section \<open>Almost-everywhere identification of the restricted outer fields\<close>

locale slp_cauchy_outer_fixed_point =
  slp_cauchy_local_w1s + aim_planar_riesz_hls

context slp_cauchy_outer_fixed_point
begin

theorem slp_both_affine_fixed_points_eq_restricted_outer_fields_AE:
  fixes p M_left M_right tau :: real
    and c :: slp_point
    and X :: "slp_point set"
    and cutoff coefficient W_left W_right :: slp_scalar_field
  assumes exponent_lower: "1 < p"
    and exponent_upper: "p < 2"
    and X_open: "open X"
    and X_bounded: "bounded X"
    and cutoff_test: "slp_test_function_on X cutoff"
    and coefficient_lp: "aim_complex_lp_on_plane p coefficient"
    and coefficient_support: "{x. coefficient x \<noteq> 0} \<subseteq> X"
    and left_admissible:
      "slp_ae_bounded_measurable lborel M_left W_left"
    and right_admissible:
      "slp_ae_bounded_measurable lborel M_right W_right"
    and left_fixed:
      "AE z in lborel.
        W_left z =
          slp_restrict_field X
            (slp_left_neumann_base tau c cutoff coefficient
              SLP_Dbar_Inverse) z +
          slp_restrict_field X
            (slp_left_neumann_step tau c cutoff coefficient W_left) z"
    and right_fixed:
      "AE z in lborel.
        W_right z =
          slp_restrict_field X
            (slp_right_neumann_base tau c cutoff coefficient
              SLP_Partial_Inverse) z +
          slp_restrict_field X
            (slp_right_neumann_step tau c cutoff coefficient W_right) z"
  shows
    "(AE z in lborel.
        W_left z =
          slp_restrict_field X
            (slp_left_outer_conjugated_field
              tau c cutoff coefficient W_left) z)
      \<and>
      (AE z in lborel.
        W_right z =
          slp_restrict_field X
            (slp_right_outer_conjugated_field
              tau c cutoff coefficient W_right) z)"
proof -
  let ?left_base =
    "\<lambda>x. cutoff x *
      (slp_dbar_inverse coefficient x -
        slp_dbar_inverse coefficient c)"
  let ?left_step =
    "\<lambda>x. cutoff x *
      slp_dbar_psi_inverse tau c
        (\<lambda>y. coefficient y * W_left y) x"
  let ?right_base =
    "\<lambda>x. cutoff x *
      (slp_partial_inverse coefficient x -
        slp_partial_inverse coefficient c)"
  let ?right_step =
    "\<lambda>x. cutoff x *
      slp_partial_psi_inverse (- tau) c
        (\<lambda>y. coefficient y * W_right y) x"

  note left_source_data = slp_both_cutoff_neumann_source_summands_lp[OF
    exponent_lower X_open X_bounded cutoff_test coefficient_lp
    coefficient_support left_admissible]
  note right_source_data = slp_both_cutoff_neumann_source_summands_lp[OF
    exponent_lower X_open X_bounded cutoff_test coefficient_lp
    coefficient_support right_admissible]
  have left_base_lp: "aim_complex_lp_on_plane p ?left_base"
    using left_source_data by blast
  have left_step_lp: "aim_complex_lp_on_plane p ?left_step"
    using left_source_data by blast
  have right_base_lp: "aim_complex_lp_on_plane p ?right_base"
    using right_source_data by blast
  have right_step_lp: "aim_complex_lp_on_plane p ?right_step"
    using right_source_data by blast

  have left_base_modulated_lp:
      "aim_complex_lp_on_plane p
        (slp_oscillatory_modulation tau c ?left_base)"
    using left_base_lp by simp
  have left_step_modulated_lp:
      "aim_complex_lp_on_plane p
        (slp_oscillatory_modulation tau c ?left_step)"
    using left_step_lp by simp
  have left_base_integrable:
      "AE z in lborel.
        slp_cauchy_integrable_at SLP_Partial_Inverse
          (slp_oscillatory_modulation tau c ?left_base) z"
    by (rule slp_cauchy_integrable_at_AE[OF exponent_lower exponent_upper
          left_base_modulated_lp])
  have left_step_integrable:
      "AE z in lborel.
        slp_cauchy_integrable_at SLP_Partial_Inverse
          (slp_oscillatory_modulation tau c ?left_step) z"
    by (rule slp_cauchy_integrable_at_AE[OF exponent_lower exponent_upper
          left_step_modulated_lp])
  have left_identification:
      "AE z in lborel.
        W_left z =
          slp_restrict_field X
            (slp_left_outer_conjugated_field
              tau c cutoff coefficient W_left) z"
    using left_fixed left_base_integrable left_step_integrable
  proof eventually_elim
    fix z :: slp_point
    assume fixed_at:
        "W_left z =
          slp_restrict_field X
            (slp_left_neumann_base tau c cutoff coefficient
              SLP_Dbar_Inverse) z +
          slp_restrict_field X
            (slp_left_neumann_step tau c cutoff coefficient W_left) z"
      and base_at:
        "slp_cauchy_integrable_at SLP_Partial_Inverse
          (slp_oscillatory_modulation tau c ?left_base) z"
      and step_at:
        "slp_cauchy_integrable_at SLP_Partial_Inverse
          (slp_oscillatory_modulation tau c ?left_step) z"
    have additive:
        "slp_partial_psi_inverse tau c ?left_base z +
            slp_partial_psi_inverse tau c ?left_step z =
          slp_partial_psi_inverse tau c
            (\<lambda>x. ?left_base x + ?left_step x) z"
      by (rule slp_partial_psi_inverse_add_at[OF base_at step_at])
    show
      "W_left z =
        slp_restrict_field X
          (slp_left_outer_conjugated_field
            tau c cutoff coefficient W_left) z"
      using fixed_at additive
      by (cases "z \<in> X")
        (simp_all add: slp_restrict_field_def slp_left_neumann_base_def
          slp_left_neumann_step_def slp_left_outer_conjugated_field_def
          slp_left_conjugated_cauchy_source_def algebra_simps)
  qed

  have right_base_modulated_lp:
      "aim_complex_lp_on_plane p
        (slp_oscillatory_modulation (- (- tau)) c ?right_base)"
    using right_base_lp by simp
  have right_step_modulated_lp:
      "aim_complex_lp_on_plane p
        (slp_oscillatory_modulation (- (- tau)) c ?right_step)"
    using right_step_lp by simp
  have right_base_integrable:
      "AE z in lborel.
        slp_cauchy_integrable_at SLP_Dbar_Inverse
          (slp_oscillatory_modulation (- (- tau)) c ?right_base) z"
    by (rule slp_cauchy_integrable_at_AE[OF exponent_lower exponent_upper
          right_base_modulated_lp])
  have right_step_integrable:
      "AE z in lborel.
        slp_cauchy_integrable_at SLP_Dbar_Inverse
          (slp_oscillatory_modulation (- (- tau)) c ?right_step) z"
    by (rule slp_cauchy_integrable_at_AE[OF exponent_lower exponent_upper
          right_step_modulated_lp])
  have right_identification:
      "AE z in lborel.
        W_right z =
          slp_restrict_field X
            (slp_right_outer_conjugated_field
              tau c cutoff coefficient W_right) z"
    using right_fixed right_base_integrable right_step_integrable
  proof eventually_elim
    fix z :: slp_point
    assume fixed_at:
        "W_right z =
          slp_restrict_field X
            (slp_right_neumann_base tau c cutoff coefficient
              SLP_Partial_Inverse) z +
          slp_restrict_field X
            (slp_right_neumann_step tau c cutoff coefficient W_right) z"
      and base_at:
        "slp_cauchy_integrable_at SLP_Dbar_Inverse
          (slp_oscillatory_modulation (- (- tau)) c ?right_base) z"
      and step_at:
        "slp_cauchy_integrable_at SLP_Dbar_Inverse
          (slp_oscillatory_modulation (- (- tau)) c ?right_step) z"
    have additive:
        "slp_dbar_psi_inverse (- tau) c ?right_base z +
            slp_dbar_psi_inverse (- tau) c ?right_step z =
          slp_dbar_psi_inverse (- tau) c
            (\<lambda>x. ?right_base x + ?right_step x) z"
      by (rule slp_dbar_psi_inverse_add_at[OF base_at step_at])
    show
      "W_right z =
        slp_restrict_field X
          (slp_right_outer_conjugated_field
            tau c cutoff coefficient W_right) z"
      using fixed_at additive
      by (cases "z \<in> X")
        (simp_all add: slp_restrict_field_def slp_right_neumann_base_def
          slp_right_neumann_step_def slp_right_outer_conjugated_field_def
          slp_right_conjugated_cauchy_source_def algebra_simps)
  qed

  show ?thesis
    using left_identification right_identification by blast
qed

end

end
