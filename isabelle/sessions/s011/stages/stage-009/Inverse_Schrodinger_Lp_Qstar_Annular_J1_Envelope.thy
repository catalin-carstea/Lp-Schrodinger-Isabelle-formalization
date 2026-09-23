theory Inverse_Schrodinger_Lp_Qstar_Annular_J1_Envelope
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Qstar_Annular_Combined_Constant"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Annular_J1_Full_Bounds"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Affine_Transport"
begin

hide_const (open) Commutative_Ring.norm

section \<open>The square-denominator near-output convolution envelope\<close>

definition slp_qstar_annular_J1_integrand ::
  "real \<Rightarrow> real \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_point \<Rightarrow> slp_point \<Rightarrow> real"
where
  "slp_qstar_annular_J1_integrand delta R f z y =
    slp_annular_J1_full_integrand delta R z y * norm (f y)"

definition slp_qstar_annular_J1_potential ::
  "real \<Rightarrow> real \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_point \<Rightarrow> real"
where
  "slp_qstar_annular_J1_potential delta R f z =
    integral\<^sup>L lborel (slp_qstar_annular_J1_integrand delta R f z)"

lemma slp_qstar_annular_J1_integrand_borel_measurable [measurable]:
  assumes amplitude_measurable: "f \<in> borel_measurable lborel"
  shows "slp_qstar_annular_J1_integrand delta R f z
    \<in> borel_measurable lborel"
  unfolding slp_qstar_annular_J1_integrand_def
  using amplitude_measurable by measurable

lemma slp_qstar_localized_riesz_convolution:
  assumes exponent_lower: "1 < a"
    and exponent_upper: "a < 2"
    and delta_positive: "0 < delta"
    and amplitude_lp:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
  shows
    "integral\<^sup>L lborel (slp_localized_riesz_integrand delta f z) =
      slp_real_convolution (slp_localized_cauchy_kernel delta)
        (\<lambda>y. norm (f y)) z"
proof -
  let ?h = "slp_localized_riesz_integrand delta f z"
  have h_integrable: "integrable lborel ?h"
    by (rule slp_qstar_localized_riesz_holder(1)[OF exponent_lower
          exponent_upper delta_positive amplitude_lp])
  have neg_linear: "linear (uminus :: slp_point \<Rightarrow> slp_point)"
    by (rule linearI) simp_all
  have neg_injective: "inj (uminus :: slp_point \<Rightarrow> slp_point)"
    by (rule injI) simp
  have determinant_abs:
      "abs (det (matrix (uminus :: slp_point \<Rightarrow> slp_point))) = 1"
    by (simp add: det_2 matrix_def axis_def)
  have transported:
      "integral\<^sup>L lborel ?h =
        abs (det (matrix (uminus :: slp_point \<Rightarrow> slp_point)))
          *\<^sub>R integral\<^sup>L lborel (\<lambda>y. ?h (z + -y))"
    by (rule slp_lborel_affine_pullback(2)[OF neg_linear neg_injective
          h_integrable])
  have transformed:
      "(\<lambda>y. ?h (z + -y)) =
        (\<lambda>y. slp_localized_cauchy_kernel delta y *
          norm (f (z - y)))"
    unfolding slp_localized_riesz_integrand_def
    by (rule ext) simp
  show ?thesis
    unfolding slp_real_convolution_def
    using transported determinant_abs transformed by simp
qed

theorem slp_qstar_annular_J1_envelope:
  assumes exponent_lower: "1 < a"
    and exponent_upper: "a < 2"
    and delta_positive: "0 < delta"
    and amplitude_lp:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
  shows fiber_integrable:
      "integrable lborel (slp_qstar_annular_J1_integrand delta R f z)"
    and potential_nonnegative:
      "0 \<le> slp_qstar_annular_J1_potential delta R f z"
    and convolution_bound:
      "slp_qstar_annular_J1_potential delta R f z \<le>
        (1 / delta ^ 2) *
          slp_real_convolution (slp_localized_cauchy_kernel delta)
            (\<lambda>y. norm (f y)) z"
proof -
  have amplitude_measurable: "f \<in> borel_measurable lborel"
    using amplitude_lp unfolding aim_complex_lp_on_plane_def by blast
  have holder_integrable:
      "integrable lborel (slp_localized_riesz_integrand delta f z)"
    by (rule slp_qstar_localized_riesz_holder(1)[OF exponent_lower
          exponent_upper delta_positive amplitude_lp])
  let ?majorant =
    "\<lambda>y. (1 / delta ^ 2) *
      slp_localized_riesz_integrand delta f z y"
  have scale_nonnegative: "0 \<le> 1 / delta ^ 2"
    using delta_positive by simp
  have majorant_integrable: "integrable lborel ?majorant"
    using holder_integrable by (rule integrable_mult_right)
  have integrand_nonnegative:
      "0 \<le> slp_qstar_annular_J1_integrand delta R f z y" for y
    unfolding slp_qstar_annular_J1_integrand_def
    by (intro mult_nonneg_nonneg)
      (rule slp_annular_J1_full_integrand_nonnegative, rule norm_ge_zero)
  have pointwise_bound:
      "slp_qstar_annular_J1_integrand delta R f z y \<le> ?majorant y"
    for y
  proof -
    have raw:
        "slp_annular_J1_full_integrand delta R z y \<le>
          (1 / delta ^ 2) *
            slp_localized_cauchy_kernel delta (z - y)"
      by (rule slp_annular_J1_full_pointwise_majorant[OF delta_positive])
    have multiplied:
        "slp_annular_J1_full_integrand delta R z y * norm (f y) \<le>
          ((1 / delta ^ 2) *
            slp_localized_cauchy_kernel delta (z - y)) * norm (f y)"
      by (rule mult_right_mono[OF raw norm_ge_zero])
    show ?thesis
      using multiplied
      unfolding slp_qstar_annular_J1_integrand_def
        slp_localized_riesz_integrand_def
      by (simp only: mult.assoc)
  qed
  have weighted_integrable:
      "integrable lborel (slp_qstar_annular_J1_integrand delta R f z)"
  proof (rule Bochner_Integration.integrable_bound[OF majorant_integrable])
    show "slp_qstar_annular_J1_integrand delta R f z
        \<in> borel_measurable lborel"
      by (rule slp_qstar_annular_J1_integrand_borel_measurable[OF
            amplitude_measurable])
    show "AE y in lborel.
        norm (slp_qstar_annular_J1_integrand delta R f z y) \<le>
          norm (?majorant y)"
    proof (rule AE_I2)
      fix y :: slp_point
      have holder_nonnegative:
          "0 \<le> slp_localized_riesz_integrand delta f z y"
        unfolding slp_localized_riesz_integrand_def
        by (intro mult_nonneg_nonneg
              slp_localized_cauchy_kernel_nonnegative norm_ge_zero)
      show "norm (slp_qstar_annular_J1_integrand delta R f z y) \<le>
          norm (?majorant y)"
        using pointwise_bound[of y] integrand_nonnegative[of y]
          scale_nonnegative holder_nonnegative
        by (simp only: real_norm_def abs_of_nonneg mult_nonneg_nonneg)
    qed
  qed
  show "integrable lborel (slp_qstar_annular_J1_integrand delta R f z)"
    by (rule weighted_integrable)
  show "0 \<le> slp_qstar_annular_J1_potential delta R f z"
    unfolding slp_qstar_annular_J1_potential_def
    by (rule integral_nonneg_AE)
      (rule AE_I2, rule integrand_nonnegative)
  have integral_bound:
      "integral\<^sup>L lborel
          (slp_qstar_annular_J1_integrand delta R f z) \<le>
        integral\<^sup>L lborel ?majorant"
    by (rule integral_mono[OF weighted_integrable majorant_integrable])
      (use pointwise_bound in auto)
  have majorant_integral:
      "integral\<^sup>L lborel ?majorant =
        (1 / delta ^ 2) *
          integral\<^sup>L lborel (slp_localized_riesz_integrand delta f z)"
    using holder_integrable by simp
  have convolution_identity:
      "integral\<^sup>L lborel (slp_localized_riesz_integrand delta f z) =
        slp_real_convolution (slp_localized_cauchy_kernel delta)
          (\<lambda>y. norm (f y)) z"
    by (rule slp_qstar_localized_riesz_convolution[OF exponent_lower
          exponent_upper delta_positive amplitude_lp])
  show "slp_qstar_annular_J1_potential delta R f z \<le>
      (1 / delta ^ 2) *
        slp_real_convolution (slp_localized_cauchy_kernel delta)
          (\<lambda>y. norm (f y)) z"
    unfolding slp_qstar_annular_J1_potential_def
    using integral_bound majorant_integral convolution_identity by simp
qed

end
