theory Inverse_Schrodinger_Lp_Cauchy_Cutoff_Terminal_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Positive_Amplitude_Terminal_Weighted_Cutoff"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Near_Center_Operator_Bridge"
begin

section \<open>Cutoff-local domination of a Cauchy terminal value\<close>

theorem slp_cauchy_transform_cutoff_terminal_riesz_bound:
  fixes R :: real
    and cutoff potential :: slp_scalar_field
    and x :: slp_point
    and orientation :: slp_cauchy_orientation
  assumes support_radius:
    "\<And>x y. \<lbrakk>cutoff x \<noteq> 0; potential y \<noteq> 0\<rbrakk> \<Longrightarrow>
      Real_Vector_Spaces.norm (x - y) \<le> R"
  shows
    "ennreal (Real_Vector_Spaces.norm (cutoff x)) *
        ennreal (Real_Vector_Spaces.norm
          (slp_cauchy_transform orientation potential x)) \<le>
      ennreal (Real_Vector_Spaces.norm (cutoff x)) *
        slp_positive_terminal_riesz_weight R potential x"
proof (cases "cutoff x = 0")
  case True
  then show ?thesis by simp
next
  case False
  show ?thesis
  proof (cases "integrable lborel
      (slp_cauchy_integrand orientation potential x)")
    case True
    have integrand_norm:
        "(\<lambda>y. Real_Vector_Spaces.norm
            (slp_cauchy_integrand orientation potential x y)) =
          slp_localized_riesz_integrand R potential x"
    proof (rule ext)
      fix y :: slp_point
      show
        "Real_Vector_Spaces.norm
            (slp_cauchy_integrand orientation potential x y) =
          slp_localized_riesz_integrand R potential x y"
      proof (cases "potential y = 0")
        case True
        then show ?thesis
          by (simp add: slp_cauchy_integrand_def
              slp_localized_riesz_integrand_def)
      next
        case False_potential: False
        have distance: "Real_Vector_Spaces.norm (x - y) \<le> R"
          by (rule support_radius[OF False False_potential])
        have kernel:
            "slp_localized_cauchy_kernel R (x - y) =
              slp_radial_inverse (x - y)"
          using slp_localized_cauchy_kernel_inside[OF distance]
          by (simp only: slp_radial_inverse_def)
        show ?thesis
          unfolding slp_cauchy_integrand_def
            slp_localized_riesz_integrand_def kernel
          by (simp only: norm_mult slp_cauchy_kernel_norm mult.commute)
      qed
    qed
    have localized_integrable:
        "integrable lborel
          (slp_localized_riesz_integrand R potential x)"
      using integrable_norm[OF True]
      unfolding integrand_norm .
    have localized_nonnegative:
        "0 \<le> slp_localized_riesz_potential R potential x"
      by (rule slp_localized_riesz_potential_nonnegative)
    have coefficient_le:
        "Real_Vector_Spaces.norm (inverse (of_real pi :: complex)) \<le> 1"
    proof -
      have one_le_pi: "1 \<le> pi"
        using pi_ge_two by linarith
      show ?thesis
        unfolding norm_inverse norm_of_real
        using one_le_pi by (simp add: inverse_le_1_iff)
    qed
    have transform_le:
        "Real_Vector_Spaces.norm
            (slp_cauchy_transform orientation potential x) \<le>
          slp_localized_riesz_potential R potential x"
    proof -
      have initial:
          "Real_Vector_Spaces.norm
              (slp_cauchy_transform orientation potential x) \<le>
            Real_Vector_Spaces.norm (inverse (of_real pi :: complex)) *
              slp_localized_riesz_potential R potential x"
        using slp_cauchy_transform_norm_bound[of orientation potential x]
        unfolding integrand_norm slp_localized_riesz_potential_def .
      have coefficient:
          "Real_Vector_Spaces.norm (inverse (of_real pi :: complex)) *
              slp_localized_riesz_potential R potential x \<le>
            1 * slp_localized_riesz_potential R potential x"
        by (rule mult_right_mono[OF coefficient_le localized_nonnegative])
      show ?thesis
        using initial coefficient by simp
    qed
    have transform_ennreal:
        "ennreal (Real_Vector_Spaces.norm
            (slp_cauchy_transform orientation potential x)) \<le>
          ennreal (slp_localized_riesz_potential R potential x)"
      by (rule ennreal_leI[OF transform_le])
    have terminal_identity:
        "slp_positive_terminal_riesz_weight R potential x =
          ennreal (slp_localized_riesz_potential R potential x)"
      by (rule slp_positive_terminal_riesz_weight_eq_localized_riesz[OF
            localized_integrable])
    show ?thesis
      unfolding terminal_identity
      by (rule mult_left_mono[OF transform_ennreal]) simp
  next
    case False_integrable: False
    have transform_zero:
        "slp_cauchy_transform orientation potential x = 0"
      unfolding slp_cauchy_transform_def
      using not_integrable_integral_eq[OF False_integrable]
      by simp
    show ?thesis
      unfolding transform_zero by simp
  qed
qed

end
