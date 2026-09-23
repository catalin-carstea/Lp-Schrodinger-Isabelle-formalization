theory Inverse_Schrodinger_Lp_Qstar_Smooth_Far_IBP
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Qstar_Annular_J12_Combined"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Smooth_Far_Product"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Near_Far_Operator_Splitting"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Oscillatory_Cauchy_Division"
begin

section \<open>The exact smooth far integration-by-parts identity\<close>

definition slp_global_far_cutoff_amplitude ::
  "real \<Rightarrow> slp_point \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_scalar_field"
where
  "slp_global_far_cutoff_amplitude delta c f y =
    of_real (1 - slp_global_scaled_cutoff delta c y) * f y"

context aim_planar_cauchy_test_left_inverse
begin

theorem slp_qstar_smooth_far_ibp:
  assumes tau_positive: "0 < tau"
    and delta_positive: "0 < delta"
    and f_test: "slp_test_function_on UNIV f"
  shows
    "slp_partial_psi_inverse tau c
        (slp_global_far_cutoff_amplitude delta c f) z =
      (1 / (\<i> * of_real tau)) *
        (slp_center_kernel tau c z *
            slp_global_cutoff.slp_far_product delta c f z -
          slp_partial_psi_inverse tau c
            (slp_classical_wirtinger_partial
              (slp_global_cutoff.slp_far_product delta c f)) z)"
proof -
  let ?phi = "slp_global_cutoff.slp_far_product delta c f"
  have phi_test: "slp_test_function_on UNIV ?phi"
    by (rule slp_global_far_product_test_function[OF delta_positive f_test])
  have divided:
      "slp_partial_inverse
          (\<lambda>x. (slp_point_as_complex (x - c) *
            slp_center_kernel tau c x) * ?phi x) z =
        (1 / (\<i> * of_real tau)) *
          (slp_center_kernel tau c z * ?phi z -
            slp_partial_inverse
              (\<lambda>x. slp_center_kernel tau c x *
                slp_classical_wirtinger_partial ?phi x) z)"
    by (rule slp_partial_inverse_oscillatory_divided[
          OF tau_positive phi_test])
  have input_eq:
      "(\<lambda>x. (slp_point_as_complex (x - c) *
          slp_center_kernel tau c x) * ?phi x) =
        slp_oscillatory_modulation tau c
          (slp_global_far_cutoff_amplitude delta c f)"
  proof (rule ext)
    fix x :: slp_point
    show "(slp_point_as_complex (x - c) *
          slp_center_kernel tau c x) * ?phi x =
        slp_oscillatory_modulation tau c
          (slp_global_far_cutoff_amplitude delta c f) x"
    proof (cases "x = c")
      case True
      have cutoff_one:
          "slp_global_cutoff.slp_scaled_cutoff delta c x = 1"
        unfolding True
        by (rule slp_global_cutoff.slp_scaled_cutoff_inner[
              OF delta_positive]) (use delta_positive in simp)
      have coordinate_zero: "slp_point_as_complex (x - c) = 0"
      proof (rule iffD2[OF slp_point_as_complex_eq_zero_iff])
        show "x - c = 0"
          unfolding True by (rule diff_self)
      qed
      show ?thesis
        unfolding slp_global_cutoff.slp_far_product_def
          slp_global_far_cutoff_amplitude_def
          slp_global_scaled_cutoff_def
          slp_oscillatory_modulation_def
        by (simp only: coordinate_zero cutoff_one diff_self of_real_0
              mult_zero_left mult_zero_right)
    next
      case False
      have difference_nonzero:
          "slp_point_as_complex (x - c) \<noteq> 0"
      proof
        assume zero: "slp_point_as_complex (x - c) = 0"
        then have "x - c = 0"
          by (simp only: slp_point_as_complex_eq_zero_iff)
        with False show False by simp
      qed
      have inverse_cancel:
          "slp_point_as_complex (x - c) *
              inverse (slp_point_as_complex (x - c)) = 1"
        by (rule right_inverse[OF difference_nonzero])
      have regroup:
          "(slp_point_as_complex (x - c) *
              slp_center_kernel tau c x) *
            (of_real (1 -
                slp_global_cutoff.slp_scaled_cutoff delta c x) *
              inverse (slp_point_as_complex (x - c)) * f x) =
          (slp_center_kernel tau c x *
              (of_real (1 -
                slp_global_cutoff.slp_scaled_cutoff delta c x) * f x)) *
            (slp_point_as_complex (x - c) *
              inverse (slp_point_as_complex (x - c)))"
        by (simp only: ac_simps)
      have algebra:
          "(slp_point_as_complex (x - c) *
              slp_center_kernel tau c x) *
            (of_real (1 -
                slp_global_cutoff.slp_scaled_cutoff delta c x) *
              inverse (slp_point_as_complex (x - c)) * f x) =
          slp_center_kernel tau c x *
            (of_real (1 -
              slp_global_cutoff.slp_scaled_cutoff delta c x) * f x)"
        by (rule trans[OF regroup])
          (simp only: inverse_cancel mult_1_right)
      show ?thesis
        unfolding slp_global_cutoff.slp_far_product_def
          slp_global_far_cutoff_amplitude_def
          slp_global_scaled_cutoff_def
          slp_oscillatory_modulation_def
        by (rule algebra)
    qed
  qed
  have derivative_input_eq:
      "(\<lambda>x. slp_center_kernel tau c x *
          slp_classical_wirtinger_partial ?phi x) =
        slp_oscillatory_modulation tau c
          (slp_classical_wirtinger_partial ?phi)"
    unfolding slp_oscillatory_modulation_def by (rule refl)
  have normalized:
      "slp_partial_inverse
          (slp_oscillatory_modulation tau c
            (slp_global_far_cutoff_amplitude delta c f)) z =
        (1 / (\<i> * of_real tau)) *
          (slp_center_kernel tau c z * ?phi z -
            slp_partial_inverse
              (slp_oscillatory_modulation tau c
                (slp_classical_wirtinger_partial ?phi)) z)"
    using divided unfolding input_eq derivative_input_eq .
  show ?thesis
    unfolding slp_partial_psi_inverse_def by (rule normalized)
qed

end

end
