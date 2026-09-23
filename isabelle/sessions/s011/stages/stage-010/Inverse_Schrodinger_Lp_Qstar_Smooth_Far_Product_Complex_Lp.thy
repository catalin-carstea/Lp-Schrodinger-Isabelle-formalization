theory Inverse_Schrodinger_Lp_Qstar_Smooth_Far_Product_Complex_Lp
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Centered_Actual_Far_Derivative_HLS"
begin

section \<open>Complex Lp control of the smooth far quotient term\<close>

theorem slp_qstar_smooth_far_product_complex_Lp:
  assumes exponent_positive: "0 < p"
    and delta_positive: "0 < delta"
    and amplitude_lp: "aim_complex_lp_on_plane p f"
  shows far_product_lp:
      "aim_complex_lp_on_plane p
        (slp_global_cutoff.slp_far_product delta c f)"
    and far_product_norm:
      "aim_complex_lp_norm p
          (slp_global_cutoff.slp_far_product delta c f) \<le>
        (2 / delta) * aim_complex_lp_norm p f"
    and centered_product_lp:
      "aim_complex_lp_on_plane p
        (\<lambda>x. slp_center_kernel tau c x *
          slp_global_cutoff.slp_far_product delta c f x)"
    and centered_product_norm:
      "aim_complex_lp_norm p
          (\<lambda>x. slp_center_kernel tau c x *
            slp_global_cutoff.slp_far_product delta c f x) \<le>
        (2 / delta) * aim_complex_lp_norm p f"
proof -
  have coefficient_measurable:
      "slp_global_far_coefficient delta c \<in>
        borel_measurable lborel"
    by (rule slp_global_far_coefficient_borel_measurable[OF
          delta_positive])
  have coefficient_bound:
      "\<And>x. norm (slp_global_far_coefficient delta c x) \<le> 2 / delta"
    by (rule slp_global_far_coefficient_norm_bound[OF delta_positive])
  have bound_nonnegative: "0 \<le> 2 / delta"
    using delta_positive by simp
  note product_data = slp_complex_lp_bounded_multiplier[
      OF exponent_positive coefficient_measurable coefficient_bound
        bound_nonnegative amplitude_lp]
  have far_product_eq:
      "slp_global_cutoff.slp_far_product delta c f =
        (\<lambda>x. slp_global_far_coefficient delta c x * f x)"
    unfolding slp_global_cutoff.slp_far_product_def
      slp_global_far_coefficient_def
    by (rule refl)
  show far_product_lp:
      "aim_complex_lp_on_plane p
        (slp_global_cutoff.slp_far_product delta c f)"
    unfolding far_product_eq
    by (rule product_data(1))
  show far_product_norm:
      "aim_complex_lp_norm p
          (slp_global_cutoff.slp_far_product delta c f) \<le>
        (2 / delta) * aim_complex_lp_norm p f"
    unfolding far_product_eq
    by (rule product_data(2))
  have centered_product_eq:
      "(\<lambda>x. slp_center_kernel tau c x *
          slp_global_cutoff.slp_far_product delta c f x) =
        slp_oscillatory_modulation tau c
          (slp_global_cutoff.slp_far_product delta c f)"
    unfolding slp_oscillatory_modulation_def by (rule refl)
  show centered_product_lp:
      "aim_complex_lp_on_plane p
        (\<lambda>x. slp_center_kernel tau c x *
          slp_global_cutoff.slp_far_product delta c f x)"
    unfolding centered_product_eq
    using far_product_lp by simp
  show centered_product_norm:
      "aim_complex_lp_norm p
          (\<lambda>x. slp_center_kernel tau c x *
            slp_global_cutoff.slp_far_product delta c f x) \<le>
        (2 / delta) * aim_complex_lp_norm p f"
    unfolding centered_product_eq
    using far_product_norm by simp
qed

end
