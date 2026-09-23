theory Inverse_Schrodinger_Lp_W1p_Far_Coefficient_Derivative_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Zero_Smooth_Multiplier"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Far_Amplitude_Derivative_Source"
begin

section \<open>Uniform Cartesian derivatives of the global far coefficient\<close>

theorem slp_global_far_coefficient_partial_norm_bound:
  assumes delta_positive: "0 < delta"
  shows
    "Real_Vector_Spaces.norm (slp_complex_partial_derivative
        (slp_global_far_coefficient delta c) i z) \<le>
      slp_global_cutoff_L / delta ^ 2 + 2 / delta ^ 2"
proof (cases "delta \<le> Real_Vector_Spaces.norm (z - c)")
  case True
  have away_from_center: "z \<noteq> c"
  proof
    assume z_eq: "z = c"
    show False
      using True delta_positive unfolding z_eq by simp
  qed
  have constant_derivative:
      "((\<lambda>_ :: slp_point. (1 :: complex)) has_derivative
        (\<lambda>_. 0)) (at z)"
    by (auto intro!: derivative_eq_intros)
  have far_derivative:
      "((slp_global_cutoff.slp_far_product delta c
          (\<lambda>_. (1 :: complex))) has_derivative
        slp_global_cutoff.slp_far_product_derivative delta c
          (\<lambda>_. (1 :: complex)) (\<lambda>_. 0) z) (at z)"
    by (rule slp_global_cutoff.slp_far_product_has_derivative[
          OF away_from_center constant_derivative])
  have coefficient_eq:
      "slp_global_far_coefficient delta c =
        slp_global_cutoff.slp_far_product delta c
          (\<lambda>_. (1 :: complex))"
    by (rule ext)
      (simp only: slp_global_far_coefficient_def
        slp_global_cutoff.slp_far_product_def mult.right_neutral)
  have coefficient_derivative:
      "((slp_global_far_coefficient delta c) has_derivative
        slp_global_cutoff.slp_far_product_derivative delta c
          (\<lambda>_. (1 :: complex)) (\<lambda>_. 0) z) (at z)"
    unfolding coefficient_eq by (rule far_derivative)
  have coefficient_frechet:
      "frechet_derivative (slp_global_far_coefficient delta c) (at z) =
        slp_global_cutoff.slp_far_product_derivative delta c
          (\<lambda>_. (1 :: complex)) (\<lambda>_. 0) z"
    by (rule sym, rule frechet_derivative_at[OF coefficient_derivative])

  let ?h = "axis i (1 :: real)"
  let ?q = "slp_point_as_complex (z - c)"
  let ?D = "slp_global_cutoff.slp_scaled_cutoff_derivative delta c z ?h"
  let ?A =
    "(of_real (1 - slp_global_cutoff.slp_scaled_cutoff delta c z) *
      inverse ?q) * (\<lambda>_. (0 :: complex)) ?h"
  let ?B = "(inverse ?q * (1 :: complex)) * of_real ?D"
  let ?C =
    "(of_real (1 - slp_global_cutoff.slp_scaled_cutoff delta c z) *
      inverse ?q ^ 2 * (1 :: complex)) * slp_point_as_complex ?h"
  have partial_eq:
      "slp_complex_partial_derivative
          (slp_global_far_coefficient delta c) i z = ?A - ?B - ?C"
    unfolding slp_complex_partial_derivative_def coefficient_frechet
      slp_global_cutoff.slp_far_product_derivative_def
    by (rule refl)
  have cutoff_axis:
      "Real_Vector_Spaces.norm ?D \<le> slp_global_cutoff_L / delta"
    using slp_global_cutoff.slp_scaled_cutoff_derivative_bound[
        OF delta_positive, of c z ?h]
    by simp
  have reciprocal:
      "Real_Vector_Spaces.norm (inverse ?q) \<le> 1 / delta"
    by (rule slp_center_reciprocal_bound[OF delta_positive True])
  have reciprocal_nonnegative: "0 \<le> 1 / delta"
    using delta_positive by simp
  have cutoff_product:
      "Real_Vector_Spaces.norm (inverse ?q) *
        Real_Vector_Spaces.norm ?D \<le>
        (1 / delta) * (slp_global_cutoff_L / delta)"
    apply (rule mult_mono[OF reciprocal cutoff_axis])
     apply (rule reciprocal_nonnegative)
    apply (rule norm_ge_zero)
    done
  have cutoff_term_norm:
      "Real_Vector_Spaces.norm ?B =
        Real_Vector_Spaces.norm (inverse ?q) *
          Real_Vector_Spaces.norm ?D"
    by (simp only: norm_mult mult.right_neutral norm_of_real real_norm_def)
  have cutoff_scalar_normalize:
      "(1 / delta) * (slp_global_cutoff_L / delta) =
        slp_global_cutoff_L / delta ^ 2"
    by (simp only: divide_inverse power2_eq_square mult.left_neutral
          inverse_mult_distrib mult.left_commute)
  have cutoff_term:
      "Real_Vector_Spaces.norm ?B \<le>
        slp_global_cutoff_L / delta ^ 2"
    using cutoff_product cutoff_term_norm cutoff_scalar_normalize by linarith
  have squared_coefficient:
      "Real_Vector_Spaces.norm (of_real
          (1 - slp_global_cutoff.slp_scaled_cutoff delta c z) *
        inverse ?q ^ 2) \<le> 2 / delta ^ 2"
    by (rule slp_global_cutoff.slp_far_squared_coefficient_bound[
          OF delta_positive True])
  have squared_term:
      "Real_Vector_Spaces.norm ?C \<le> 2 / delta ^ 2"
    using squared_coefficient
    by (simp only: mult.right_neutral norm_mult
          slp_point_as_complex_norm norm_axis_1)
  have triangle:
      "Real_Vector_Spaces.norm (?A - ?B - ?C) \<le>
        Real_Vector_Spaces.norm ?A + Real_Vector_Spaces.norm ?B +
          Real_Vector_Spaces.norm ?C"
    by (rule slp_norm_sub_sub_le)
  have A_zero: "?A = 0"
    by (simp only: mult_zero_right)
  have triangle_zero:
      "Real_Vector_Spaces.norm (?A - ?B - ?C) \<le>
        Real_Vector_Spaces.norm ?B + Real_Vector_Spaces.norm ?C"
    using triangle by (simp only: A_zero norm_zero add.left_neutral)
  have outside_bound:
      "Real_Vector_Spaces.norm (?A - ?B - ?C) \<le>
        slp_global_cutoff_L / delta ^ 2 + 2 / delta ^ 2"
    using triangle_zero cutoff_term squared_term by linarith
  show ?thesis
    apply (subst partial_eq)
    apply (rule outside_bound)
    done
next
  case False
  have inside_strict: "Real_Vector_Spaces.norm (z - c) < delta"
    using False by simp
  have z_ball: "z \<in> ball c delta"
    using inside_strict by (simp only: mem_ball dist_norm norm_minus_commute)
  have coefficient_differentiable:
      "slp_global_far_coefficient delta c differentiable at z"
    using smooth_on_imp_differentiable_on[
        OF slp_global_far_coefficient_smooth[OF delta_positive]]
    by (simp add: differentiable_on_def)
  have local_zero:
      "slp_global_far_coefficient delta c y =
        (\<lambda>_ :: slp_point. (0 :: complex)) y"
    if y_ball: "y \<in> ball c delta" for y
  proof -
    have y_inside_strict: "Real_Vector_Spaces.norm (y - c) < delta"
      using y_ball by (simp only: mem_ball dist_norm norm_minus_commute)
    have y_inside: "Real_Vector_Spaces.norm (y - c) \<le> delta"
      by (rule less_imp_le[OF y_inside_strict])
    have cutoff_one:
        "slp_global_cutoff.slp_scaled_cutoff delta c y = 1"
      by (rule slp_global_cutoff.slp_scaled_cutoff_inner[
            OF delta_positive y_inside])
    show ?thesis
      unfolding slp_global_far_coefficient_def
      by (simp only: cutoff_one diff_self of_real_0 mult_zero_left)
  qed
  have derivative_zero:
      "frechet_derivative (slp_global_far_coefficient delta c) (at z) =
        frechet_derivative (\<lambda>_ :: slp_point. (0 :: complex)) (at z)"
    by (rule frechet_derivative_transform_within_open[
          OF coefficient_differentiable open_ball z_ball local_zero])
  have partial_zero:
      "slp_complex_partial_derivative
          (slp_global_far_coefficient delta c) i z = 0"
    unfolding slp_complex_partial_derivative_def derivative_zero by simp
  have cutoff_nonnegative: "0 \<le> slp_global_cutoff_L"
    by (rule slp_global_cutoff_profile_spec[THEN conjunct2,
          THEN conjunct2, THEN conjunct1])
  have cutoff_term_nonnegative:
      "0 \<le> slp_global_cutoff_L / delta ^ 2"
    by (rule divide_nonneg_nonneg[OF cutoff_nonnegative]) simp
  have square_term_nonnegative: "0 \<le> 2 / delta ^ 2"
    by simp
  show ?thesis
    unfolding partial_zero norm_zero
    by (rule add_nonneg_nonneg[OF cutoff_term_nonnegative
          square_term_nonnegative])
qed

end
