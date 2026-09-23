theory Inverse_Schrodinger_Lp_W1p_Rough_Global_Far_IBP
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Zero_Global_Far_Coefficient"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Rough_Far_AE"
begin

section \<open>The exact rough global-far integration-by-parts identity\<close>

context aim_planar_cauchy_test_left_inverse
begin

theorem slp_w1p_zero_pair_partial_psi_inverse_rough_global_far_AE:
  fixes p :: real
  assumes tau_positive: "0 < tau"
    and exponent_above_two: "2 < p"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and delta_positive: "0 < delta"
    and zero_pair: "slp_w1p_zero_pair_on p X u Du"
  shows "AE z in lborel.
    slp_partial_psi_inverse tau c
        (slp_global_far_cutoff_amplitude delta c
          (slp_restrict_field X u)) z =
      (1 / (\<i> * of_real tau)) *
        (slp_center_kernel tau c z *
            slp_restrict_field X
              (\<lambda>x. slp_global_far_coefficient delta c x * u x) z -
          slp_partial_psi_inverse tau c
            (slp_restrict_field X
              (slp_gradient_wirtinger_partial
                (\<lambda>x. \<chi> i.
                  slp_global_far_coefficient delta c x * Du x $ i +
                  u x * slp_complex_partial_derivative
                    (slp_global_far_coefficient delta c) i x))) z)"
proof -
  let ?a = "slp_global_far_coefficient delta c"
  let ?v = "\<lambda>x. ?a x * u x"
  let ?Dv = "\<lambda>x. \<chi> i. ?a x * Du x $ i +
    u x * slp_complex_partial_derivative ?a i x"
  have exponent_one_le: "1 \<le> p"
    using exponent_above_two by linarith
  have product_zero_pair: "slp_w1p_zero_pair_on p X ?v ?Dv"
    by (rule slp_w1p_zero_pair_on_global_far_coefficient[
          OF exponent_one_le X_measurable X_bounded delta_positive zero_pair])
  have divided_AE: "AE z in lborel.
      slp_partial_inverse
          (\<lambda>x. (slp_point_as_complex (x - c) *
            slp_center_kernel tau c x) * slp_restrict_field X ?v x) z =
        (1 / (\<i> * of_real tau)) *
          (slp_center_kernel tau c z * slp_restrict_field X ?v z -
            slp_partial_inverse
              (\<lambda>x. slp_center_kernel tau c x *
                slp_restrict_field X
                  (slp_gradient_wirtinger_partial ?Dv) x) z)"
    by (rule
        slp_w1p_zero_pair_partial_inverse_oscillatory_divided_rough_far_product_AE[
          OF tau_positive exponent_above_two X_bounded product_zero_pair])
  have restrict_product_eq:
      "slp_restrict_field X ?v =
        (\<lambda>x. ?a x * slp_restrict_field X u x)"
    by (rule ext) (simp add: slp_restrict_field_def)
  have input_eq:
      "(\<lambda>x. (slp_point_as_complex (x - c) *
          slp_center_kernel tau c x) * slp_restrict_field X ?v x) =
        slp_oscillatory_modulation tau c
          (slp_global_far_cutoff_amplitude delta c
            (slp_restrict_field X u))"
  proof (rule ext)
    fix x :: slp_point
    have restricted_at:
        "slp_restrict_field X ?v x =
          ?a x * slp_restrict_field X u x"
      using fun_cong[OF restrict_product_eq, of x] .
    show "(slp_point_as_complex (x - c) *
          slp_center_kernel tau c x) * slp_restrict_field X ?v x =
        slp_oscillatory_modulation tau c
          (slp_global_far_cutoff_amplitude delta c
            (slp_restrict_field X u)) x"
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
        apply (subst restricted_at)
        unfolding slp_global_far_coefficient_def
          slp_global_far_cutoff_amplitude_def
          slp_global_scaled_cutoff_def slp_oscillatory_modulation_def
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
              inverse (slp_point_as_complex (x - c)) *
              slp_restrict_field X u x) =
          (slp_center_kernel tau c x *
              (of_real (1 -
                slp_global_cutoff.slp_scaled_cutoff delta c x) *
                slp_restrict_field X u x)) *
            (slp_point_as_complex (x - c) *
              inverse (slp_point_as_complex (x - c)))"
        by (simp only: ac_simps)
      have algebra:
          "(slp_point_as_complex (x - c) *
              slp_center_kernel tau c x) *
            (of_real (1 -
                slp_global_cutoff.slp_scaled_cutoff delta c x) *
              inverse (slp_point_as_complex (x - c)) *
              slp_restrict_field X u x) =
          slp_center_kernel tau c x *
            (of_real (1 -
              slp_global_cutoff.slp_scaled_cutoff delta c x) *
              slp_restrict_field X u x)"
        by (rule trans[OF regroup])
          (simp only: inverse_cancel mult_1_right)
      show ?thesis
        apply (subst restricted_at)
        unfolding slp_global_far_coefficient_def
          slp_global_far_cutoff_amplitude_def
          slp_global_scaled_cutoff_def slp_oscillatory_modulation_def
        by (rule algebra)
    qed
  qed
  have derivative_input_eq:
      "(\<lambda>x. slp_center_kernel tau c x *
          slp_restrict_field X
            (slp_gradient_wirtinger_partial ?Dv) x) =
        slp_oscillatory_modulation tau c
          (slp_restrict_field X
            (slp_gradient_wirtinger_partial ?Dv))"
    unfolding slp_oscillatory_modulation_def by (rule refl)
  show ?thesis
  proof (use divided_AE in eventually_elim)
    fix z
    assume divided:
        "slp_partial_inverse
            (\<lambda>x. (slp_point_as_complex (x - c) *
              slp_center_kernel tau c x) * slp_restrict_field X ?v x) z =
          (1 / (\<i> * of_real tau)) *
            (slp_center_kernel tau c z * slp_restrict_field X ?v z -
              slp_partial_inverse
                (\<lambda>x. slp_center_kernel tau c x *
                  slp_restrict_field X
                    (slp_gradient_wirtinger_partial ?Dv) x) z)"
    have normalized:
        "slp_partial_inverse
            (slp_oscillatory_modulation tau c
              (slp_global_far_cutoff_amplitude delta c
                (slp_restrict_field X u))) z =
          (1 / (\<i> * of_real tau)) *
            (slp_center_kernel tau c z * slp_restrict_field X ?v z -
              slp_partial_inverse
                (slp_oscillatory_modulation tau c
                  (slp_restrict_field X
                    (slp_gradient_wirtinger_partial ?Dv))) z)"
      using divided unfolding input_eq derivative_input_eq .
    show "slp_partial_psi_inverse tau c
        (slp_global_far_cutoff_amplitude delta c
          (slp_restrict_field X u)) z =
      (1 / (\<i> * of_real tau)) *
        (slp_center_kernel tau c z *
            slp_restrict_field X ?v z -
          slp_partial_psi_inverse tau c
            (slp_restrict_field X
              (slp_gradient_wirtinger_partial ?Dv)) z)"
      unfolding slp_partial_psi_inverse_def by (rule normalized)
  qed
qed

end

end
