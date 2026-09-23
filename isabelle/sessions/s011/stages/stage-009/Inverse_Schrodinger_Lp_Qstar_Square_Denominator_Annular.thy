theory Inverse_Schrodinger_Lp_Qstar_Square_Denominator_Annular
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Qstar_Cutoff_Partial_Annular"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Qstar_Annular_J12_Combined"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Pointwise annular domination of the square-denominator term\<close>

definition slp_qstar_square_denominator_integrand ::
  "real \<Rightarrow> slp_scalar_field \<Rightarrow> slp_point \<Rightarrow>
    slp_point \<Rightarrow> complex"
where
  "slp_qstar_square_denominator_integrand delta f z y =
    slp_cauchy_kernel SLP_Partial_Inverse z y *
      of_real (1 - slp_global_cutoff.slp_scaled_cutoff delta 0 y) *
      inverse (slp_point_as_complex y) ^ 2 * f y"

theorem slp_qstar_square_denominator_integrand_le_annular:
  assumes delta_positive: "0 < delta"
    and amplitude_radius: "f y \<noteq> 0 \<Longrightarrow> norm y \<le> R"
  shows
    "norm (slp_qstar_square_denominator_integrand delta f z y) \<le>
      slp_qstar_annular_J1_integrand delta R f z y +
      slp_qstar_annular_J2_weighted_integrand delta R f z y"
proof -
  let ?cutoff = "slp_global_cutoff.slp_scaled_cutoff delta 0 y"
  let ?base = "slp_radial_inverse (z - y) *
    slp_radial_inverse_square y * norm (f y)"
  have J1_nonnegative:
      "0 \<le> slp_qstar_annular_J1_integrand delta R f z y"
    unfolding slp_qstar_annular_J1_integrand_def by simp
  have J2_nonnegative:
      "0 \<le> slp_qstar_annular_J2_weighted_integrand delta R f z y"
    by (rule slp_qstar_annular_J2_weighted_integrand_nonnegative)
  show ?thesis
  proof (cases "f y = 0 \<or> 1 - ?cutoff = 0")
    case True
    have integrand_zero:
        "slp_qstar_square_denominator_integrand delta f z y = 0"
    proof (rule disjE[OF True])
      assume amplitude_zero: "f y = 0"
      show ?thesis
        unfolding slp_qstar_square_denominator_integrand_def amplitude_zero
        by (simp only: mult_zero_right)
    next
      assume complement_zero: "1 - ?cutoff = 0"
      show ?thesis
        unfolding slp_qstar_square_denominator_integrand_def complement_zero
        by (simp only: of_real_0 mult_zero_right mult_zero_left)
    qed
    show ?thesis
      unfolding integrand_zero norm_zero
      using J1_nonnegative J2_nonnegative by linarith
  next
    case False
    have amplitude_nonzero: "f y \<noteq> 0"
      using False by blast
    have complement_nonzero: "1 - ?cutoff \<noteq> 0"
      using False by blast
    have annular_lower: "delta \<le> norm y"
    proof -
      have strict: "delta < norm (y - (0 :: slp_point))"
        using slp_cutoff_profile.slp_scaled_cutoff_complement_support[
          OF slp_global_cutoff_profile_spec[THEN conjunct1]
            delta_positive complement_nonzero] .
      then show ?thesis by simp
    qed
    have annular_upper: "norm y \<le> R"
      by (rule amplitude_radius[OF amplitude_nonzero])
    have cutoff_nonnegative: "0 \<le> ?cutoff"
      unfolding slp_global_cutoff.slp_scaled_cutoff_def
      using slp_global_cutoff_profile_spec by blast
    have cutoff_at_most_one: "?cutoff \<le> 1"
      unfolding slp_global_cutoff.slp_scaled_cutoff_def
      using slp_global_cutoff_profile_spec by blast
    have complement_nonnegative: "0 \<le> 1 - ?cutoff"
      using cutoff_at_most_one by linarith
    have complement_at_most_one: "1 - ?cutoff \<le> 1"
      using cutoff_nonnegative by linarith
    have complement_norm_bound:
        "norm (of_real (1 - ?cutoff) :: complex) \<le> 1"
      by (simp only: norm_of_real abs_of_nonneg[OF complement_nonnegative]
          complement_at_most_one)
    have base_nonnegative: "0 \<le> ?base"
      by (intro mult_nonneg_nonneg
            slp_radial_inverse_nonnegative
            slp_radial_inverse_square_nonnegative norm_ge_zero)
    have norm_value:
        "norm (slp_qstar_square_denominator_integrand delta f z y) =
          norm (of_real (1 - ?cutoff) :: complex) * ?base"
      unfolding slp_qstar_square_denominator_integrand_def
        slp_radial_inverse_square_def slp_radial_inverse_def
      by (simp only: norm_mult slp_cauchy_kernel_norm norm_inverse
          slp_radial_inverse_def norm_power slp_point_as_complex_norm norm_of_real
          mult.assoc mult.commute mult.left_commute)
    have norm_to_base:
        "norm (slp_qstar_square_denominator_integrand delta f z y) \<le>
          ?base"
    proof -
      have
        "norm (of_real (1 - ?cutoff) :: complex) * ?base \<le> 1 * ?base"
        by (rule mult_right_mono[OF complement_norm_bound base_nonnegative])
      then show ?thesis using norm_value by simp
    qed
    have base_to_carriers:
        "?base \<le>
          slp_qstar_annular_J1_integrand delta R f z y +
          slp_qstar_annular_J2_weighted_integrand delta R f z y"
    proof (cases "norm (z - y) \<le> delta")
      case True
      have near_carrier:
          "delta \<le> norm y \<and> norm y \<le> R \<and>
            norm (z - y) \<le> delta"
        using annular_lower annular_upper True by blast
      have J1_value:
          "slp_qstar_annular_J1_integrand delta R f z y = ?base"
        unfolding slp_qstar_annular_J1_integrand_def
          slp_annular_J1_full_integrand_def if_P[OF near_carrier]
        by (rule refl)
      show ?thesis
        using J1_value J2_nonnegative by linarith
    next
      case False
      have far: "delta \<le> norm (z - y)"
        using False by simp
      have far_carrier:
          "delta \<le> norm y \<and> norm y \<le> R \<and>
            delta \<le> norm (z - y)"
        using annular_lower annular_upper far by blast
      have J2_value:
          "slp_qstar_annular_J2_weighted_integrand delta R f z y = ?base"
        unfolding slp_qstar_annular_J2_weighted_integrand_def
          slp_annular_J2_full_integrand_def if_P[OF far_carrier]
        by (rule refl)
      show ?thesis
        using J2_value J1_nonnegative by linarith
    qed
    show ?thesis
      by (rule order_trans[OF norm_to_base base_to_carriers])
  qed
qed

end
