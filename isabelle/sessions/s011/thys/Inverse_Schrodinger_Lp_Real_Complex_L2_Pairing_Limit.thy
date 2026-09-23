theory Inverse_Schrodinger_Lp_Real_Complex_L2_Pairing_Limit
  imports Inverse_Schrodinger_Lp_Real_Complex_L2_Pairing
begin

section \<open>Strong \(L^2\) decay under a fixed real pairing\<close>

lemma slp_real_complex_l2_pairing_limit:
  fixes f :: "slp_point \<Rightarrow> real"
    and g :: "'a \<Rightarrow> slp_point \<Rightarrow> complex"
    and F :: "'a filter"
  assumes f_l2: "aim_real_lp_on_plane 2 f"
    and g_l2: "\<And>i. aim_complex_lp_on_plane 2 (g i)"
    and g_square_decay:
      "((\<lambda>i. \<integral>\<^sup>+x.
          ennreal (Real_Vector_Spaces.norm (g i x)) ^ 2 \<partial>lborel)
        \<longlongrightarrow> 0) F"
  shows "((\<lambda>i. integral\<^sup>L lborel
        (\<lambda>x. of_real (f x) * g i x)) \<longlongrightarrow> 0) F"
proof -
  let ?A = "\<integral>\<^sup>+x. ennreal (abs (f x)) ^ 2 \<partial>lborel"
  let ?B = "\<lambda>i. \<integral>\<^sup>+x.
    ennreal (Real_Vector_Spaces.norm (g i x)) ^ 2 \<partial>lborel"
  let ?I = "\<lambda>i. integral\<^sup>L lborel
    (\<lambda>x. of_real (f x) * g i x)"
  have f_power_integrable:
      "integrable lborel (\<lambda>x. abs (f x) powr 2)"
    using f_l2 unfolding aim_real_lp_on_plane_def by auto
  have A_finite: "?A < top_class.top"
  proof -
    have "(\<integral>\<^sup>+x.
          ennreal (Real_Vector_Spaces.norm (abs (f x) powr 2))
          \<partial>lborel) < top_class.top"
      using f_power_integrable by (simp add: integrable_iff_bounded)
    then show ?thesis
      by (simp add: powr_numeral ennreal_power)
  qed
  have product_decay: "((\<lambda>i. ?A * ?B i) \<longlongrightarrow> 0) F"
  proof -
    have "((\<lambda>i. ?A * ?B i) \<longlongrightarrow> ?A * 0) F"
      by (rule tendsto_mult_ennreal[OF tendsto_const g_square_decay])
        (use A_finite in auto)
    then show ?thesis by simp
  qed
  have square_bound:
      "\<And>i. ennreal (Real_Vector_Spaces.norm (?I i)) ^ 2
        \<le> ?A * ?B i"
    using slp_real_complex_l2_pairing(3)[OF f_l2 g_l2] .
  have integral_square_ennreal_decay:
      "((\<lambda>i. ennreal (Real_Vector_Spaces.norm (?I i)) ^ 2)
        \<longlongrightarrow> 0) F"
    by (rule tendsto_sandwich[where f = "\<lambda>_. 0" and
          h = "\<lambda>i. ?A * ?B i"])
      (use square_bound product_decay in auto)
  have integral_square_real_decay:
      "((\<lambda>i. Real_Vector_Spaces.norm (?I i) ^ 2)
        \<longlongrightarrow> 0) F"
  proof -
    have cast_square:
        "\<And>i. ennreal (Real_Vector_Spaces.norm (?I i) ^ 2) =
          ennreal (Real_Vector_Spaces.norm (?I i)) ^ 2"
      by (rule ennreal_power[symmetric]) (rule norm_ge_zero)
    have cast_decay:
        "((\<lambda>i. ennreal (Real_Vector_Spaces.norm (?I i) ^ 2))
          \<longlongrightarrow> ennreal 0) F"
      using integral_square_ennreal_decay
      by (simp only: cast_square ennreal_0)
    show ?thesis
      by (rule tendsto_ennrealD[OF cast_decay])
        (simp_all add: eventuallyI)
  qed
  have integral_norm_decay:
      "((\<lambda>i. Real_Vector_Spaces.norm (?I i)) \<longlongrightarrow> 0) F"
    using integral_square_real_decay
    by (simp only: power_tendsto_0_iff[OF zero_less_numeral])
  show ?thesis
    using integral_norm_decay by (rule tendsto_norm_zero_cancel)
qed

end
