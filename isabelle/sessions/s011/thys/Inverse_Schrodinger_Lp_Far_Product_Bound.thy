theory Inverse_Schrodinger_Lp_Far_Product_Bound
  imports Inverse_Schrodinger_Lp_Far_Coefficient_Bounds
begin

section \<open>Pointwise majorant for the differentiated far product\<close>

lemma slp_norm_sub_sub_le:
  fixes a b d :: complex
  shows "norm (a - b - d) \<le> norm a + norm b + norm d"
proof -
  have inner: "norm (a - b) \<le> norm a + norm b"
    by (rule norm_triangle_ineq4)
  have outer: "norm (a - b - d) \<le> norm (a - b) + norm d"
    by (rule norm_triangle_ineq4)
  show ?thesis
    using inner outer by linarith
qed

context slp_cutoff_profile
begin

lemma slp_far_product_partial_norm_bound:
  assumes delta_positive: "0 < delta"
    and distance: "delta \<le> norm (z - c)"
  shows "norm (slp_complex_wirtinger_partial
      (slp_far_product_derivative delta c f Df z)) \<le>
    (2 / delta) * norm (slp_complex_wirtinger_partial Df) +
    (L / delta ^ 2) * norm (f z) +
    (2 / delta ^ 2) * norm (f z)"
proof -
  have amplitude_coefficient:
    "norm (of_real (1 - slp_scaled_cutoff delta c z) *
      inverse (slp_point_as_complex (z - c))) \<le> 2 / delta"
    by (rule slp_far_amplitude_coefficient_bound[OF
          delta_positive distance])
  have amplitude_derivative_bound:
    "norm ((of_real (1 - slp_scaled_cutoff delta c z) *
        inverse (slp_point_as_complex (z - c))) *
      slp_complex_wirtinger_partial Df) \<le>
      (2 / delta) * norm (slp_complex_wirtinger_partial Df)"
  proof -
    have multiplied:
      "norm (of_real (1 - slp_scaled_cutoff delta c z) *
          inverse (slp_point_as_complex (z - c))) *
        norm (slp_complex_wirtinger_partial Df) \<le>
        (2 / delta) * norm (slp_complex_wirtinger_partial Df)"
      by (rule mult_right_mono[OF amplitude_coefficient]) simp
    show ?thesis
      using multiplied by (simp only: norm_mult)
  qed
  have cutoff_coefficient:
    "norm (slp_real_wirtinger_partial
        (slp_scaled_cutoff_derivative delta c z) *
      inverse (slp_point_as_complex (z - c))) \<le> L / delta ^ 2"
    by (rule slp_far_cutoff_derivative_coefficient_bound[OF
          delta_positive distance])
  have cutoff_term_bound:
    "norm ((slp_real_wirtinger_partial
        (slp_scaled_cutoff_derivative delta c z) *
      inverse (slp_point_as_complex (z - c))) * f z) \<le>
      (L / delta ^ 2) * norm (f z)"
  proof -
    have multiplied:
      "norm (slp_real_wirtinger_partial
          (slp_scaled_cutoff_derivative delta c z) *
        inverse (slp_point_as_complex (z - c))) * norm (f z) \<le>
        (L / delta ^ 2) * norm (f z)"
      by (rule mult_right_mono[OF cutoff_coefficient]) simp
    show ?thesis
      using multiplied by (simp only: norm_mult)
  qed
  have squared_coefficient:
    "norm (of_real (1 - slp_scaled_cutoff delta c z) *
      inverse (slp_point_as_complex (z - c)) ^ 2) \<le>
      2 / delta ^ 2"
    by (rule slp_far_squared_coefficient_bound[OF
          delta_positive distance])
  have squared_term_bound:
    "norm ((of_real (1 - slp_scaled_cutoff delta c z) *
        inverse (slp_point_as_complex (z - c)) ^ 2) * f z) \<le>
      (2 / delta ^ 2) * norm (f z)"
  proof -
    have multiplied:
      "norm (of_real (1 - slp_scaled_cutoff delta c z) *
          inverse (slp_point_as_complex (z - c)) ^ 2) * norm (f z) \<le>
        (2 / delta ^ 2) * norm (f z)"
      by (rule mult_right_mono[OF squared_coefficient]) simp
    show ?thesis
      using multiplied by (simp only: norm_mult)
  qed
  have triangle:
    "norm (
      of_real (1 - slp_scaled_cutoff delta c z) *
        inverse (slp_point_as_complex (z - c)) *
          slp_complex_wirtinger_partial Df -
      slp_real_wirtinger_partial
          (slp_scaled_cutoff_derivative delta c z) *
        inverse (slp_point_as_complex (z - c)) * f z -
      of_real (1 - slp_scaled_cutoff delta c z) *
        inverse (slp_point_as_complex (z - c)) ^ 2 * f z) \<le>
      norm (of_real (1 - slp_scaled_cutoff delta c z) *
        inverse (slp_point_as_complex (z - c)) *
          slp_complex_wirtinger_partial Df) +
      norm (slp_real_wirtinger_partial
          (slp_scaled_cutoff_derivative delta c z) *
        inverse (slp_point_as_complex (z - c)) * f z) +
      norm (of_real (1 - slp_scaled_cutoff delta c z) *
        inverse (slp_point_as_complex (z - c)) ^ 2 * f z)"
    by (rule slp_norm_sub_sub_le)
  show ?thesis
    unfolding slp_far_product_partial
    using triangle amplitude_derivative_bound cutoff_term_bound
      squared_term_bound
    by linarith
qed

end

end
