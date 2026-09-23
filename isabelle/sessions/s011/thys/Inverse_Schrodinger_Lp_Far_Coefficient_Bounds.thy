theory Inverse_Schrodinger_Lp_Far_Coefficient_Bounds
  imports Inverse_Schrodinger_Lp_Far_Product_Rule
begin

section \<open>Pointwise bounds for the far-product coefficients\<close>

lemma slp_center_reciprocal_bound:
  assumes delta_positive: "0 < delta"
    and distance: "delta \<le> norm (z - c)"
  shows "norm (inverse (slp_point_as_complex (z - c))) \<le> 1 / delta"
proof -
  have distance_positive: "0 < norm (z - c)"
    using delta_positive distance by linarith
  have reciprocal:
    "inverse (norm (z - c)) \<le> inverse delta"
    by (rule le_imp_inverse_le[OF distance delta_positive])
  show ?thesis
    using reciprocal
    by (simp only: norm_inverse slp_point_as_complex_norm
        divide_inverse)
qed

lemma slp_center_reciprocal_square_bound:
  assumes delta_positive: "0 < delta"
    and distance: "delta \<le> norm (z - c)"
  shows "norm (inverse (slp_point_as_complex (z - c)) ^ 2) \<le>
    1 / delta ^ 2"
proof -
  have reciprocal:
    "norm (inverse (slp_point_as_complex (z - c))) \<le> 1 / delta"
    by (rule slp_center_reciprocal_bound[OF delta_positive distance])
  have reciprocal_nonnegative:
    "0 \<le> norm (inverse (slp_point_as_complex (z - c)))"
    by simp
  have target_nonnegative: "0 \<le> 1 / delta"
    using delta_positive by simp
  have square:
    "norm (inverse (slp_point_as_complex (z - c))) ^ 2 \<le>
      (1 / delta) ^ 2"
    by (rule power_mono[OF reciprocal reciprocal_nonnegative])
  have normalize: "(1 / delta) ^ 2 = 1 / delta ^ 2"
    by (simp add: power2_eq_square)
  have norm_power_eq:
    "norm (inverse (slp_point_as_complex (z - c)) ^ 2) =
      norm (inverse (slp_point_as_complex (z - c))) ^ 2"
    by (rule norm_power)
  have step:
    "norm (inverse (slp_point_as_complex (z - c)) ^ 2) \<le>
      (1 / delta) ^ 2"
    using norm_power_eq square by linarith
  show ?thesis
    using step normalize by linarith
qed

context slp_cutoff_profile
begin

lemma slp_cutoff_complement_norm:
  "norm (of_real (1 - slp_scaled_cutoff delta c z) :: complex) \<le> 2"
proof -
  have triangle:
    "norm ((1 :: complex) - of_real (slp_scaled_cutoff delta c z)) \<le>
      norm (1 :: complex) +
        norm (of_real (slp_scaled_cutoff delta c z) :: complex)"
    by (rule norm_triangle_ineq4)
  have cutoff: "norm (slp_scaled_cutoff delta c z) \<le> 1"
    by (rule slp_scaled_cutoff_norm)
  have cutoff_complex:
    "norm (of_real (slp_scaled_cutoff delta c z) :: complex) \<le> 1"
    using cutoff by simp
  have target:
    "norm ((1 :: complex) - of_real (slp_scaled_cutoff delta c z)) \<le> 2"
    using triangle cutoff_complex by simp
  show ?thesis
    using target by simp
qed

lemma slp_scaled_cutoff_partial_bound:
  assumes delta_positive: "0 < delta"
  shows "norm (slp_real_wirtinger_partial
      (slp_scaled_cutoff_derivative delta c z)) \<le> L / delta"
proof -
  have first:
    "norm (slp_scaled_cutoff_derivative delta c z
      (axis (0 :: 2) 1)) \<le> L / delta"
    using slp_scaled_cutoff_derivative_bound[OF delta_positive,
        of c z "axis (0 :: 2) 1"]
    by simp
  have second:
    "norm (slp_scaled_cutoff_derivative delta c z
      (axis (1 :: 2) 1)) \<le> L / delta"
    using slp_scaled_cutoff_derivative_bound[OF delta_positive,
        of c z "axis (1 :: 2) 1"]
    by simp
  have target_nonnegative: "0 \<le> L / delta"
    using order_trans[OF norm_ge_zero first] .
  have triangle:
    "norm (of_real (slp_scaled_cutoff_derivative delta c z
        (axis (0 :: 2) 1)) / 2 -
      \<i> * of_real (slp_scaled_cutoff_derivative delta c z
        (axis (1 :: 2) 1)) / 2) \<le>
      norm ((of_real (slp_scaled_cutoff_derivative delta c z
        (axis (0 :: 2) 1)) :: complex) / 2) +
      norm (\<i> * of_real (slp_scaled_cutoff_derivative delta c z
        (axis (1 :: 2) 1)) / 2)"
    by (rule norm_triangle_ineq4)
  have first_half:
    "norm ((of_real (slp_scaled_cutoff_derivative delta c z
      (axis (0 :: 2) 1)) :: complex) / 2) \<le> (L / delta) / 2"
  proof -
    have divide:
      "norm ((of_real (slp_scaled_cutoff_derivative delta c z
        (axis (0 :: 2) 1)) :: complex) / 2) =
        norm (slp_scaled_cutoff_derivative delta c z
          (axis (0 :: 2) 1)) / 2"
      by simp
    have half:
      "norm (slp_scaled_cutoff_derivative delta c z
        (axis (0 :: 2) 1)) / 2 \<le> (L / delta) / 2"
      by (rule divide_right_mono[OF first]) simp
    show ?thesis
      using divide half by linarith
  qed
  have second_half:
    "norm (\<i> * of_real (slp_scaled_cutoff_derivative delta c z
      (axis (1 :: 2) 1)) / 2) \<le> (L / delta) / 2"
  proof -
    have divide:
      "norm (\<i> * of_real (slp_scaled_cutoff_derivative delta c z
        (axis (1 :: 2) 1)) / (2 :: complex)) =
        norm (slp_scaled_cutoff_derivative delta c z
          (axis (1 :: 2) 1)) / 2"
      by (simp only: divide_inverse norm_mult norm_inverse norm_ii
            norm_of_real;
          simp)
    have half:
      "norm (slp_scaled_cutoff_derivative delta c z
        (axis (1 :: 2) 1)) / 2 \<le> (L / delta) / 2"
      by (rule divide_right_mono[OF second]) simp
    show ?thesis
      using divide half by linarith
  qed
  show ?thesis
    unfolding slp_real_wirtinger_partial_def
    using triangle first_half second_half target_nonnegative by linarith
qed

lemma slp_far_amplitude_coefficient_bound:
  assumes delta_positive: "0 < delta"
    and distance: "delta \<le> norm (z - c)"
  shows "norm (of_real (1 - slp_scaled_cutoff delta c z) *
      inverse (slp_point_as_complex (z - c))) \<le> 2 / delta"
proof -
  have complement: "norm (of_real
      (1 - slp_scaled_cutoff delta c z) :: complex) \<le> 2"
    by (rule slp_cutoff_complement_norm)
  have reciprocal:
    "norm (inverse (slp_point_as_complex (z - c))) \<le> 1 / delta"
    by (rule slp_center_reciprocal_bound[OF delta_positive distance])
  have target_nonnegative: "0 \<le> 1 / delta"
    using delta_positive by simp
  have product:
    "norm (of_real (1 - slp_scaled_cutoff delta c z) :: complex) *
      norm (inverse (slp_point_as_complex (z - c))) \<le>
      2 * (1 / delta)"
    by (rule mult_mono[OF complement reciprocal]) simp_all
  show ?thesis
    using product by (simp only: norm_mult divide_inverse; simp add: mult_ac)
qed

lemma slp_far_cutoff_derivative_coefficient_bound:
  assumes delta_positive: "0 < delta"
    and distance: "delta \<le> norm (z - c)"
  shows "norm (slp_real_wirtinger_partial
      (slp_scaled_cutoff_derivative delta c z) *
      inverse (slp_point_as_complex (z - c))) \<le>
    L / delta ^ 2"
proof -
  have partial:
    "norm (slp_real_wirtinger_partial
      (slp_scaled_cutoff_derivative delta c z)) \<le> L / delta"
    by (rule slp_scaled_cutoff_partial_bound[OF delta_positive])
  have reciprocal:
    "norm (inverse (slp_point_as_complex (z - c))) \<le> 1 / delta"
    by (rule slp_center_reciprocal_bound[OF delta_positive distance])
  have partial_nonnegative: "0 \<le> L / delta"
    using order_trans[OF norm_ge_zero partial] .
  have reciprocal_nonnegative: "0 \<le> 1 / delta"
    using delta_positive by simp
  have product:
    "norm (slp_real_wirtinger_partial
        (slp_scaled_cutoff_derivative delta c z)) *
      norm (inverse (slp_point_as_complex (z - c))) \<le>
      (L / delta) * (1 / delta)"
    by (rule mult_mono[OF partial reciprocal partial_nonnegative]) simp
  show ?thesis
    using product
    by (simp only: norm_mult divide_inverse power2_eq_square;
        simp add: ac_simps)
qed

lemma slp_far_squared_coefficient_bound:
  assumes delta_positive: "0 < delta"
    and distance: "delta \<le> norm (z - c)"
  shows "norm (of_real (1 - slp_scaled_cutoff delta c z) *
      inverse (slp_point_as_complex (z - c)) ^ 2) \<le>
    2 / delta ^ 2"
proof -
  have complement: "norm (of_real
      (1 - slp_scaled_cutoff delta c z) :: complex) \<le> 2"
    by (rule slp_cutoff_complement_norm)
  have reciprocal_square:
    "norm (inverse (slp_point_as_complex (z - c)) ^ 2) \<le>
      1 / delta ^ 2"
    by (rule slp_center_reciprocal_square_bound[OF
          delta_positive distance])
  have target_nonnegative: "0 \<le> 1 / delta ^ 2"
    using delta_positive by simp
  have product:
    "norm (of_real (1 - slp_scaled_cutoff delta c z) :: complex) *
      norm (inverse (slp_point_as_complex (z - c)) ^ 2) \<le>
      2 * (1 / delta ^ 2)"
    by (rule mult_mono[OF complement reciprocal_square]) simp_all
  show ?thesis
    using product by (simp only: norm_mult; simp add: divide_inverse)
qed

end

end
