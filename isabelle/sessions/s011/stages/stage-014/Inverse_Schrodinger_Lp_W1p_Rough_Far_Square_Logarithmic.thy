theory Inverse_Schrodinger_Lp_W1p_Rough_Far_Square_Logarithmic
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Rough_Far_Square_Annular_Cauchy"
begin

section \<open>Explicit logarithmic bound for the rough square source\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_w1p_global_far_square_denominator_cauchy_logarithmic_bound:
  fixes b A R :: real
  assumes exponent_above_two: "2 < b"
    and radius_nonnegative: "0 \<le> A"
    and set_radius: "\<And>y. y \<in> X \<Longrightarrow> norm y \<le> A"
    and relative_radius: "\<And>y. y \<in> X \<Longrightarrow> norm (y - c) \<le> R"
    and delta_positive: "0 < delta"
    and normalized_lower: "1 \<le> R / delta"
    and zero_pair: "slp_w1p_zero_pair_on b X u Du"
  defines "q \<equiv> slp_holder_conjugate b"
  shows cauchy_integrable:
      "slp_cauchy_integrable_at orientation
        (slp_oscillatory_modulation tau c
          (slp_w1p_global_far_square_denominator_source delta c X u)) z"
    and logarithmic_bound:
      "norm (slp_cauchy_transform orientation
          (slp_oscillatory_modulation tau c
            (slp_w1p_global_far_square_denominator_source delta c X u)) z)
        \<le>
        norm (inverse (of_real pi :: complex)) *
          ((norm (inverse (of_real pi :: complex)) *
            (integral\<^sup>L lborel
              (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x)
                powr q)) powr (1 / q)) *
            (192 * slp_w1p_norm_on b X u Du)) *
          ((1 / delta) *
              integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
            (1 / delta) * (1 + log 2 (R / delta)) *
              integral\<^sup>L lborel (slp_squared_radial_annulus 1 2))"
proof -
  let ?M =
    "(norm (inverse (of_real pi :: complex)) *
      (integral\<^sup>L lborel
        (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x) powr q))
          powr (1 / q)) *
      (192 * slp_w1p_norm_on b X u Du)"
  note annular =
    slp_w1p_global_far_square_denominator_cauchy_annular_bound[
      OF exponent_above_two radius_nonnegative set_radius relative_radius
        delta_positive zero_pair,
      folded q_def]
  show "slp_cauchy_integrable_at orientation
      (slp_oscillatory_modulation tau c
        (slp_w1p_global_far_square_denominator_source delta c X u)) z"
    by (rule annular(1))

  have J1_bound:
      "integral\<^sup>L lborel
          (slp_annular_J1_full_integrand delta R (z - c)) \<le>
        (1 / delta) *
          integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
    by (rule slp_annular_J1_full_integral_bound[OF delta_positive])
  have J2_bound:
      "integral\<^sup>L lborel
          (slp_annular_J2_full_integrand delta R (z - c)) \<le>
        (1 / delta) * (1 + log 2 (R / delta)) *
          integral\<^sup>L lborel (slp_squared_radial_annulus 1 2)"
    by (rule slp_annular_J2_full_logarithmic_bound[
          OF delta_positive normalized_lower])
  have carrier_bound:
      "integral\<^sup>L lborel
          (slp_annular_J1_full_integrand delta R (z - c)) +
        integral\<^sup>L lborel
          (slp_annular_J2_full_integrand delta R (z - c)) \<le>
        (1 / delta) *
            integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
          (1 / delta) * (1 + log 2 (R / delta)) *
            integral\<^sup>L lborel (slp_squared_radial_annulus 1 2)"
    by (rule add_mono[OF J1_bound J2_bound])
  have outer_nonnegative:
      "0 \<le> norm (inverse (of_real pi :: complex)) * ?M"
    unfolding slp_w1p_norm_on_def by simp
  have scaled_carrier_bound:
      "norm (inverse (of_real pi :: complex)) * ?M *
          (integral\<^sup>L lborel
              (slp_annular_J1_full_integrand delta R (z - c)) +
            integral\<^sup>L lborel
              (slp_annular_J2_full_integrand delta R (z - c))) \<le>
        norm (inverse (of_real pi :: complex)) * ?M *
          ((1 / delta) *
              integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
            (1 / delta) * (1 + log 2 (R / delta)) *
              integral\<^sup>L lborel (slp_squared_radial_annulus 1 2))"
    by (rule mult_left_mono[OF carrier_bound outer_nonnegative])
  show "norm (slp_cauchy_transform orientation
        (slp_oscillatory_modulation tau c
          (slp_w1p_global_far_square_denominator_source delta c X u)) z)
      \<le>
      norm (inverse (of_real pi :: complex)) *
        ((norm (inverse (of_real pi :: complex)) *
          (integral\<^sup>L lborel
            (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x)
              powr q)) powr (1 / q)) *
          (192 * slp_w1p_norm_on b X u Du)) *
        ((1 / delta) *
            integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
          (1 / delta) * (1 + log 2 (R / delta)) *
            integral\<^sup>L lborel (slp_squared_radial_annulus 1 2))"
    using annular(2) scaled_carrier_bound by (rule order_trans)
qed

end

end
