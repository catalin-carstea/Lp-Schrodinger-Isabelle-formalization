theory Inverse_Schrodinger_Lp_Fourier_Pointwise_Inversion
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Fourier_Continuity"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Pointwise inversion of the literal L1 Fourier transform\<close>

lemma slp_fourier_transform_cong_ae:
  fixes f g :: slp_scalar_field
  assumes f_measurable: "f \<in> borel_measurable lborel"
    and g_measurable: "g \<in> borel_measurable lborel"
    and equality: "AE x in lborel. f x = g x"
  shows "slp_fourier_transform f xi = slp_fourier_transform g xi"
proof -
  have left_measurable:
      "(\<lambda>x. slp_fourier_phase xi x * f x) \<in> borel_measurable lborel"
    using f_measurable slp_fourier_phase_measurable[of xi] by measurable
  have right_measurable:
      "(\<lambda>x. slp_fourier_phase xi x * g x) \<in> borel_measurable lborel"
    using g_measurable slp_fourier_phase_measurable[of xi] by measurable
  have integrand_eq:
      "AE x in lborel. slp_fourier_phase xi x * f x =
        slp_fourier_phase xi x * g x"
    using equality by eventually_elim simp
  show ?thesis unfolding slp_fourier_transform_def
    by (rule Bochner_Integration.integral_cong_AE[OF
        left_measurable right_measurable integrand_eq])
qed

context hormander_euclidean_l2_fourier_plancherel
begin

theorem slp_fourier_l1_double_transform_ae:
  fixes f :: slp_scalar_field
  assumes f_integrable: "integrable lborel f"
    and f_l2: "aim_complex_lp_on_plane 2 f"
    and fourier_integrable: "integrable lborel (slp_fourier_transform f)"
  shows "AE x in lborel. slp_fourier_transform (slp_fourier_transform f) x =
    of_real ((2 * pi) ^ 2) * f (-x)"
proof -
  let ?T = "slp_fourier_l2_transform f"
  have selected_l2: "aim_complex_lp_on_plane 2 ?T"
    by (rule slp_fourier_l2_transform_l2[OF f_l2])
  have selected_measurable: "?T \<in> borel_measurable lborel"
    using selected_l2 unfolding aim_complex_lp_on_plane_def by blast
  have fourier_measurable: "slp_fourier_transform f \<in> borel_measurable lborel"
    using fourier_integrable by measurable
  have selected_eq: "AE x in lborel. ?T x = slp_fourier_transform f x"
    by (rule slp_fourier_l2_transform_ae_eq_l1[OF f_l2 f_integrable])
  have selected_eq_rev: "AE x in lborel. slp_fourier_transform f x = ?T x"
    using selected_eq by eventually_elim simp
  have selected_integrable: "integrable lborel ?T"
    by (rule Bochner_Integration.integrable_cong_AE_imp[OF
        fourier_integrable selected_measurable selected_eq_rev])
  have double_selected_eq:
      "AE x in lborel. slp_fourier_l2_transform ?T x = slp_fourier_transform ?T x"
    by (rule slp_fourier_l2_transform_ae_eq_l1[OF selected_l2 selected_integrable])
  have literal_eq:
      "slp_fourier_transform ?T x = slp_fourier_transform (slp_fourier_transform f) x"
    for x
    by (rule slp_fourier_transform_cong_ae[OF
        selected_measurable fourier_measurable selected_eq])
  have inversion:
      "AE x in lborel. slp_fourier_l2_transform ?T x =
        of_real ((2 * pi) ^ 2) * f (-x)"
    using slp_fourier_l2_transform_realization f_l2
    unfolding slp_fourier_l2_realization_def by blast
  show ?thesis using double_selected_eq inversion
    by eventually_elim (simp add: literal_eq)
qed

theorem slp_fourier_l1_double_transform:
  fixes f :: slp_scalar_field
  assumes f_integrable: "integrable lborel f"
    and f_l2: "aim_complex_lp_on_plane 2 f"
    and fourier_integrable: "integrable lborel (slp_fourier_transform f)"
    and f_continuous: "continuous_on UNIV f"
  shows "slp_fourier_transform (slp_fourier_transform f) x =
    of_real ((2 * pi) ^ 2) * f (-x)"
proof -
  have left_continuous:
      "continuous_on UNIV (slp_fourier_transform (slp_fourier_transform f))"
    by (rule slp_fourier_transform_continuous[OF fourier_integrable])
  have reflected_continuous: "continuous_on UNIV (\<lambda>x. f (-x))"
    by (rule continuous_on_compose2[OF f_continuous])
      (auto intro!: continuous_intros)
  have right_continuous:
      "continuous_on UNIV (\<lambda>x. of_real ((2 * pi) ^ 2) * f (-x))"
    using reflected_continuous by (intro continuous_intros)
  show ?thesis
    by (rule slp_continuous_ae_eq[OF left_continuous right_continuous
        slp_fourier_l1_double_transform_ae[OF f_integrable f_l2 fourier_integrable]])
qed

end

end
