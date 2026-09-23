theory Inverse_Schrodinger_Lp_Center_Error_L2
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Center_Error_Fourier_Bound"
begin

section \<open>Planar L2 membership of the undamped physical center error\<close>

context hormander_euclidean_l2_fourier_plancherel
begin

theorem slp_center_average_error_l2_l1_l2:
  fixes f :: "slp_point \<Rightarrow> complex"
  assumes tau: "0 < tau"
    and f_integrable: "integrable lborel f"
    and f_l2: "aim_complex_lp_on_plane 2 f"
  shows "aim_complex_lp_on_plane 2
    (\<lambda>c. slp_center_average tau f c - f c)"
proof -
  let ?E = "\<lambda>c. slp_center_average tau f c - f c"
  have f_measurable: "f \<in> borel_measurable lborel"
    using f_integrable by measurable
  have average_measurable:
      "slp_center_average tau f \<in> borel_measurable lborel"
    by (rule slp_center_average_measurable[OF f_integrable])
  have error_measurable: "?E \<in> borel_measurable lborel"
    using average_measurable f_measurable by measurable
  have error_bound:
      "(\<integral>\<^sup>+c. ennreal (cmod ((?E c) ^ 2)) \<partial>lborel) \<le>
        ennreal ((integral\<^sup>L lborel
          (\<lambda>xi. cmod (((slp_center_fourier_multiplier tau xi - 1) *
            slp_fourier_transform f xi) ^ 2))) / (2 * pi) ^ 2)"
    by (rule slp_center_average_error_nn_integral_le_fourier[OF
          tau f_integrable f_l2])
  have error_nn_finite:
      "(\<integral>\<^sup>+c. ennreal (cmod ((?E c) ^ 2)) \<partial>lborel) < \<infinity>"
    by (rule order_le_less_trans[OF error_bound]) simp
  have square_measurable:
      "(\<lambda>c. cmod (?E c) powr 2) \<in> borel_measurable lborel"
    using error_measurable by measurable
  have square_nn_finite:
      "(\<integral>\<^sup>+c. cmod (?E c) powr 2 \<partial>lborel) < \<infinity>"
    using error_nn_finite
    by (simp only: powr_numeral norm_ge_zero norm_power)
  have square_integrable:
      "integrable lborel (\<lambda>c. cmod (?E c) powr 2)"
  proof (rule integrableI_nn_integral_finite[OF square_measurable])
    show "AE c in lborel. 0 \<le> cmod (?E c) powr 2"
      by simp
    show "(\<integral>\<^sup>+c. cmod (?E c) powr 2 \<partial>lborel) =
        ennreal (enn2real
          (\<integral>\<^sup>+c. cmod (?E c) powr 2 \<partial>lborel))"
      using square_nn_finite by simp
  qed
  show ?thesis
    unfolding aim_complex_lp_on_plane_def
    using error_measurable square_integrable by blast
qed

end

end
