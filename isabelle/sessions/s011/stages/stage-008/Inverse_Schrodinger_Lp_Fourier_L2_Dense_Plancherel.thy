theory Inverse_Schrodinger_Lp_Fourier_L2_Dense_Plancherel
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Fourier_L2_Selected_Realization"
begin

section \<open>Dense-class consequences of the selected planar L2 transform\<close>

context hormander_euclidean_l2_fourier_plancherel
begin

lemma slp_fourier_l2_transform_l2:
  assumes f_l2: "aim_complex_lp_on_plane 2 f"
  shows "aim_complex_lp_on_plane 2 (slp_fourier_l2_transform f)"
  using slp_fourier_l2_transform_realization f_l2
  unfolding slp_fourier_l2_realization_def
  by blast

lemma slp_fourier_l2_transform_ae_eq_l1:
  assumes f_l2: "aim_complex_lp_on_plane 2 f"
    and f_integrable: "integrable lborel f"
  shows "AE xi in lborel.
    slp_fourier_l2_transform f xi = slp_fourier_transform f xi"
  using slp_fourier_l2_transform_realization f_l2 f_integrable
  unfolding slp_fourier_l2_realization_def
  by blast

theorem slp_fourier_l1_plancherel_l1_l2:
  assumes f_l2: "aim_complex_lp_on_plane 2 f"
    and f_integrable: "integrable lborel f"
  shows
    "integral\<^sup>L lborel
        (\<lambda>xi. cmod (slp_fourier_transform f xi) ^ 2) =
      (2 * pi) ^ 2 * integral\<^sup>L lborel (\<lambda>x. cmod (f x) ^ 2)"
proof -
  have selected_l2:
      "aim_complex_lp_on_plane 2 (slp_fourier_l2_transform f)"
    by (rule slp_fourier_l2_transform_l2[OF f_l2])
  have f_measurable:
      "f \<in> borel_measurable lborel"
    using f_l2 unfolding aim_complex_lp_on_plane_def by blast
  have selected_measurable:
      "slp_fourier_l2_transform f \<in> borel_measurable lborel"
    using selected_l2 unfolding aim_complex_lp_on_plane_def by blast
  have l1_transform_measurable:
      "slp_fourier_transform f \<in> borel_measurable lborel"
    by (rule slp_fourier_transform_measurable[OF f_measurable])
  have selected_square_measurable:
      "(\<lambda>xi. cmod (slp_fourier_l2_transform f xi) ^ 2) \<in>
        borel_measurable lborel"
    using selected_measurable by measurable
  have l1_square_measurable:
      "(\<lambda>xi. cmod (slp_fourier_transform f xi) ^ 2) \<in>
        borel_measurable lborel"
    using l1_transform_measurable by measurable
  have transform_ae:
      "AE xi in lborel.
        slp_fourier_l2_transform f xi = slp_fourier_transform f xi"
    by (rule slp_fourier_l2_transform_ae_eq_l1[OF f_l2 f_integrable])
  have square_ae:
      "AE xi in lborel.
        cmod (slp_fourier_transform f xi) ^ 2 =
          cmod (slp_fourier_l2_transform f xi) ^ 2"
    using transform_ae by eventually_elim simp
  have integral_eq:
      "integral\<^sup>L lborel
          (\<lambda>xi. cmod (slp_fourier_transform f xi) ^ 2) =
        integral\<^sup>L lborel
          (\<lambda>xi. cmod (slp_fourier_l2_transform f xi) ^ 2)"
    by (rule integral_cong_AE[OF l1_square_measurable
          selected_square_measurable square_ae])
  have selected_plancherel:
      "integral\<^sup>L lborel
          (\<lambda>xi. cmod (slp_fourier_l2_transform f xi) ^ 2) =
        (2 * pi) ^ 2 * integral\<^sup>L lborel (\<lambda>x. cmod (f x) ^ 2)"
    using slp_fourier_l2_transform_realization f_l2
    unfolding slp_fourier_l2_realization_def
    by blast
  show ?thesis
    by (rule trans[OF integral_eq selected_plancherel])
qed

end

end
