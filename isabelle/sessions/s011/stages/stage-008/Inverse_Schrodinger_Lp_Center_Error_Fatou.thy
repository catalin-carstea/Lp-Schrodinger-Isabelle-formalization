theory Inverse_Schrodinger_Lp_Center_Error_Fatou
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_NN_Integral_Fatou_Finite"
begin

section \<open>Fatou transfer for the physical center error\<close>

theorem slp_center_average_error_nn_integral_le_liminf:
  fixes f :: "slp_point \<Rightarrow> complex"
    and S :: "nat \<Rightarrow> real"
  assumes S_positive: "\<And>n. 0 < S n"
    and S_tendsto_zero: "S \<longlonglongrightarrow> 0"
    and f_integrable: "integrable lborel f"
  shows "(\<integral>\<^sup>+c. ennreal (cmod
      ((slp_center_average tau f c - f c) ^ 2)) \<partial>lborel) \<le>
    liminf (\<lambda>n. \<integral>\<^sup>+c. ennreal (cmod
      ((slp_damped_center_average (S n) tau f c - f c) ^ 2))
        \<partial>lborel)"
proof -
  have S_at_right:
      "filterlim S (at_right (0 :: real)) sequentially"
  proof (rule tendsto_imp_filterlim_at_right)
    show "S \<longlonglongrightarrow> (0 :: real)"
      by (rule S_tendsto_zero)
    show "\<forall>\<^sub>F n in sequentially. S n > 0"
      using S_positive by simp
  qed
  have average_limit:
      "(\<lambda>n. slp_damped_center_average (S n) tau f c)
        \<longlonglongrightarrow> slp_center_average tau f c" for c
    using slp_damped_center_average_tendsto[OF f_integrable, of tau c]
      S_at_right
    by (rule filterlim_compose)
  have mass_limit:
      "(\<lambda>n. ennreal (cmod
          ((slp_damped_center_average (S n) tau f c - f c) ^ 2)))
        \<longlonglongrightarrow>
      ennreal (cmod ((slp_center_average tau f c - f c) ^ 2))" for c
  proof (rule tendsto_ennrealI)
    show "(\<lambda>n. cmod
          ((slp_damped_center_average (S n) tau f c - f c) ^ 2))
        \<longlonglongrightarrow>
      cmod ((slp_center_average tau f c - f c) ^ 2)"
      using average_limit[of c]
      by (intro tendsto_intros)
  qed
  have sequence_measurable:
      "(\<lambda>c. ennreal (cmod
          ((slp_damped_center_average (S n) tau f c - f c) ^ 2)))
        \<in> borel_measurable lborel" for n
  proof -
    have damped_integrable:
        "integrable lborel (slp_damped_center_average (S n) tau f)"
      by (rule slp_damped_center_average_integrable[OF
            S_positive f_integrable])
    show ?thesis
      using damped_integrable f_integrable by measurable
  qed
  have pointwise_limit:
      "AE c in lborel.
        (\<lambda>n. ennreal (cmod
          ((slp_damped_center_average (S n) tau f c - f c) ^ 2)))
          \<longlonglongrightarrow>
        ennreal (cmod ((slp_center_average tau f c - f c) ^ 2))"
    using mass_limit by simp
  show ?thesis
    by (rule slp_nn_integral_le_liminf_of_AE_tendsto[OF
          sequence_measurable pointwise_limit])
qed

end
