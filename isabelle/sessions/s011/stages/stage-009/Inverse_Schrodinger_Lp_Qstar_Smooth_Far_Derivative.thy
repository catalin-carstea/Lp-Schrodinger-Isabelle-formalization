theory Inverse_Schrodinger_Lp_Qstar_Smooth_Far_Derivative
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Qstar_Smooth_Far_IBP"
begin

section \<open>The exact three-term derivative of the smooth far product\<close>

lemma slp_classical_wirtinger_partial_frechet:
  "slp_classical_wirtinger_partial f z =
    slp_complex_wirtinger_partial (frechet_derivative f (at z))"
  unfolding slp_classical_wirtinger_partial_def
    slp_complex_partial_derivative_def
    slp_complex_wirtinger_partial_def
  by (rule diff_divide_distrib)

theorem slp_global_far_product_partial_three_term:
  assumes delta_positive: "0 < delta"
    and f_test: "slp_test_function_on UNIV f"
    and away_from_center: "z \<noteq> c"
  shows
    "slp_classical_wirtinger_partial
        (slp_global_cutoff.slp_far_product delta c f) z =
      of_real (1 - slp_global_cutoff.slp_scaled_cutoff delta c z) *
        inverse (slp_point_as_complex (z - c)) *
          slp_classical_wirtinger_partial f z -
      slp_real_wirtinger_partial
          (slp_global_cutoff.slp_scaled_cutoff_derivative delta c z) *
        inverse (slp_point_as_complex (z - c)) * f z -
      of_real (1 - slp_global_cutoff.slp_scaled_cutoff delta c z) *
        inverse (slp_point_as_complex (z - c)) ^ 2 * f z"
proof -
  have f_smooth: "smooth_on UNIV f"
    using f_test unfolding slp_test_function_on_def by blast
  have f_differentiable: "f differentiable at z"
    using smooth_on_imp_differentiable_on[OF f_smooth]
    by (simp add: differentiable_on_def)
  have f_derivative:
      "(f has_derivative frechet_derivative f (at z)) (at z)"
    using f_differentiable by (simp only: frechet_derivative_works)
  have far_derivative:
      "((slp_global_cutoff.slp_far_product delta c f) has_derivative
        slp_global_cutoff.slp_far_product_derivative delta c f
          (frechet_derivative f (at z)) z) (at z)"
    by (rule slp_global_cutoff.slp_far_product_has_derivative[
          OF away_from_center f_derivative])
  have far_differentiable:
      "slp_global_cutoff.slp_far_product delta c f differentiable at z"
    by (rule differentiableI[OF far_derivative])
  have far_frechet:
      "((slp_global_cutoff.slp_far_product delta c f) has_derivative
        frechet_derivative
          (slp_global_cutoff.slp_far_product delta c f) (at z)) (at z)"
    using far_differentiable by (simp only: frechet_derivative_works)
  have derivative_unique:
      "frechet_derivative
          (slp_global_cutoff.slp_far_product delta c f) (at z) =
        slp_global_cutoff.slp_far_product_derivative delta c f
          (frechet_derivative f (at z)) z"
    by (rule has_derivative_unique[OF far_frechet far_derivative])
  show ?thesis
    unfolding slp_classical_wirtinger_partial_frechet
      derivative_unique
      slp_global_cutoff.slp_far_product_partial
    by (rule refl)
qed

end
