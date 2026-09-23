theory Inverse_Schrodinger_Lp_Far_Modulated_Product_Derivative
  imports Inverse_Schrodinger_Lp_Near_Far_Operator_Splitting
begin

section \<open>Pointwise calculus for the far modulated product\<close>

lemma slp_complex_wirtinger_partial_right_multiplier:
  "slp_complex_wirtinger_partial (\<lambda>h. F h * k) =
    slp_complex_wirtinger_partial F * k"
  unfolding slp_complex_wirtinger_partial_def
  by (simp add: algebra_simps)

context slp_cutoff_profile
begin

definition slp_far_modulated_product ::
  "real \<Rightarrow> real \<Rightarrow> slp_point \<Rightarrow>
    slp_scalar_field \<Rightarrow> slp_scalar_field"
where
  "slp_far_modulated_product tau delta c f z =
    slp_center_kernel tau c z * slp_far_product delta c f z"

definition slp_far_modulated_product_derivative ::
  "real \<Rightarrow> real \<Rightarrow> slp_point \<Rightarrow>
    slp_scalar_field \<Rightarrow> (slp_point \<Rightarrow> complex) \<Rightarrow>
    slp_point \<Rightarrow> slp_point \<Rightarrow> complex"
where
  "slp_far_modulated_product_derivative tau delta c f Df z h =
    slp_center_kernel tau c z *
      slp_far_product_derivative delta c f Df z h +
    slp_center_kernel_derivative tau c z h *
      slp_far_product delta c f z"

lemma slp_far_modulated_product_has_derivative:
  assumes away_from_center: "z \<noteq> c"
    and f_derivative: "(f has_derivative Df) (at z)"
  shows "((slp_far_modulated_product tau delta c f) has_derivative
      slp_far_modulated_product_derivative tau delta c f Df z) (at z)"
proof -
  have product_derivative:
    "((\<lambda>w. slp_center_kernel tau c w *
        slp_far_product delta c f w) has_derivative
      (\<lambda>h. slp_center_kernel tau c z *
          slp_far_product_derivative delta c f Df z h +
        slp_center_kernel_derivative tau c z h *
          slp_far_product delta c f z)) (at z)"
    by (rule has_derivative_mult[OF slp_center_kernel_has_derivative
          slp_far_product_has_derivative[OF away_from_center f_derivative]])
  show ?thesis
    unfolding slp_far_modulated_product_def
      slp_far_modulated_product_derivative_def
    by (rule product_derivative)
qed

lemma slp_far_modulated_product_partial_expansion:
  "slp_complex_wirtinger_partial
      (slp_far_modulated_product_derivative tau delta c f Df z) =
    slp_center_kernel tau c z *
      slp_complex_wirtinger_partial
        (slp_far_product_derivative delta c f Df z) +
    slp_center_kernel_partial tau c z *
      slp_far_product delta c f z"
  unfolding slp_far_modulated_product_derivative_def
  unfolding slp_complex_wirtinger_partial_add
  unfolding slp_complex_wirtinger_partial_left_multiplier
  unfolding slp_complex_wirtinger_partial_right_multiplier
  unfolding slp_center_kernel_partial_def
  by (rule refl)

lemma slp_far_modulated_product_partial:
  assumes away_from_center: "z \<noteq> c"
  shows "slp_complex_wirtinger_partial
      (slp_far_modulated_product_derivative tau delta c f Df z) =
    slp_center_kernel tau c z *
      slp_complex_wirtinger_partial
        (slp_far_product_derivative delta c f Df z) +
    (\<i> * of_real tau) *
      slp_oscillatory_modulation tau c
        (slp_far_cutoff_amplitude delta c f) z"
proof -
  have difference_nonzero:
    "slp_point_as_complex (z - c) \<noteq> 0"
  proof
    assume "slp_point_as_complex (z - c) = 0"
    then have "z - c = 0"
      by (simp only: slp_point_as_complex_eq_zero_iff)
    with away_from_center show False by simp
  qed
  have inverse_cancel:
    "slp_point_as_complex (z - c) *
        inverse (slp_point_as_complex (z - c)) = 1"
    using difference_nonzero by simp
  have regroup:
    "(\<i> * of_real tau * slp_point_as_complex (z - c) *
          slp_center_kernel tau c z) *
        (of_real (1 - slp_scaled_cutoff delta c z) *
          inverse (slp_point_as_complex (z - c)) * f z) =
        ((\<i> * of_real tau) * slp_center_kernel tau c z *
          of_real (1 - slp_scaled_cutoff delta c z) * f z) *
          (slp_point_as_complex (z - c) *
            inverse (slp_point_as_complex (z - c)))"
    by (simp only: ac_simps)
  have cancel:
    "((\<i> * of_real tau) * slp_center_kernel tau c z *
        of_real (1 - slp_scaled_cutoff delta c z) * f z) *
        (slp_point_as_complex (z - c) *
          inverse (slp_point_as_complex (z - c))) =
      (\<i> * of_real tau) * slp_center_kernel tau c z *
          of_real (1 - slp_scaled_cutoff delta c z) * f z"
    by (simp only: inverse_cancel mult_1_right)
  have associate:
    "(\<i> * of_real tau) * slp_center_kernel tau c z *
        of_real (1 - slp_scaled_cutoff delta c z) * f z =
      (\<i> * of_real tau) *
          (slp_center_kernel tau c z *
            (of_real (1 - slp_scaled_cutoff delta c z) * f z))"
    by (simp only: ac_simps)
  have center_term:
    "slp_center_kernel_partial tau c z *
        slp_far_product delta c f z =
      (\<i> * of_real tau) *
        slp_oscillatory_modulation tau c
          (slp_far_cutoff_amplitude delta c f) z"
    unfolding slp_center_kernel_partial_eq
      slp_far_product_def slp_oscillatory_modulation_def
      slp_far_cutoff_amplitude_def
    by (rule trans[OF regroup trans[OF cancel associate]])
  show ?thesis
    using slp_far_modulated_product_partial_expansion[of tau delta c f Df z]
      center_term
    by simp
qed

lemma slp_far_modulated_product_pointwise_ibp:
  assumes away_from_center: "z \<noteq> c"
  shows "(\<i> * of_real tau) *
      slp_oscillatory_modulation tau c
        (slp_far_cutoff_amplitude delta c f) z =
    slp_complex_wirtinger_partial
      (slp_far_modulated_product_derivative tau delta c f Df z) -
    slp_center_kernel tau c z *
      slp_complex_wirtinger_partial
        (slp_far_product_derivative delta c f Df z)"
  using slp_far_modulated_product_partial[OF away_from_center,
      of tau delta f Df]
  by (simp add: algebra_simps)

end

end
