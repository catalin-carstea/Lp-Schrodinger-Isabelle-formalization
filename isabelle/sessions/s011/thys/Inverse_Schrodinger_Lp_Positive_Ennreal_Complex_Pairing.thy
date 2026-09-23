theory Inverse_Schrodinger_Lp_Positive_Ennreal_Complex_Pairing
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Positive_Ennreal_Lp"
begin

section \<open>Finite pairings of positive densities and complex data\<close>

lemma slp_positive_ennreal_lp_norm_of_complex:
  assumes f_lp: "aim_complex_lp_on_plane p f"
  shows
    "slp_positive_ennreal_lp_on_plane p
      (\<lambda>x. ennreal (norm (f x)))"
proof -
  have f_measurable: "f \<in> borel_measurable lborel"
    and f_power_integrable:
      "integrable lborel (\<lambda>x. norm (f x) powr p)"
    using f_lp unfolding aim_complex_lp_on_plane_def by blast+
  have norm_measurable:
      "(\<lambda>x. ennreal (norm (f x))) \<in> borel_measurable lborel"
    using f_measurable by measurable
  have norm_finite:
      "AE x in lborel. ennreal (norm (f x)) < top"
    by simp
  have norm_power_integrable:
      "integrable lborel
        (\<lambda>x. enn2real (ennreal (norm (f x))) powr p)"
    using f_power_integrable by simp
  show ?thesis
    unfolding slp_positive_ennreal_lp_on_plane_def
    using norm_measurable norm_finite norm_power_integrable by blast
qed

lemma slp_positive_ennreal_l1_integral_lt_top:
  assumes F_lp: "slp_positive_ennreal_lp_on_plane 1 F"
  shows "(\<integral>\<^sup>+ x. F x \<partial>lborel) < top"
proof -
  have F_finite: "AE x in lborel. F x < top"
    and F_power_integrable:
      "integrable lborel (\<lambda>x. enn2real (F x) powr 1)"
    using F_lp unfolding slp_positive_ennreal_lp_on_plane_def by blast+
  have F_real_integrable:
      "integrable lborel (\<lambda>x. enn2real (F x))"
    using F_power_integrable by simp
  have F_real_norm_finite:
      "(\<integral>\<^sup>+ x. ennreal (norm (enn2real (F x)))
        \<partial>lborel) < top"
    using F_real_integrable
    unfolding integrable_iff_bounded by simp
  have F_representation:
      "AE x in lborel.
        F x = ennreal (norm (enn2real (F x)))"
    using F_finite
  proof eventually_elim
    fix x
    assume "F x < top"
    then show "F x = ennreal (norm (enn2real (F x)))"
      by (simp add: ennreal_enn2real_if)
  qed
  have integral_representation:
      "(\<integral>\<^sup>+ x. F x \<partial>lborel) =
        (\<integral>\<^sup>+ x. ennreal (norm (enn2real (F x)))
          \<partial>lborel)"
    by (rule nn_integral_cong_AE[OF F_representation])
  show ?thesis
    using integral_representation F_real_norm_finite by simp
qed

lemma slp_positive_ennreal_lp_complex_pairing_lt_top:
  fixes q r :: real
  assumes q_lower: "1 < q"
    and r_lower: "1 < r"
    and conjugate: "1 / q + 1 / r = 1"
    and F_lp: "slp_positive_ennreal_lp_on_plane q F"
    and g_lp: "aim_complex_lp_on_plane r g"
  shows
    "(\<integral>\<^sup>+ x. F x * ennreal (norm (g x)) \<partial>lborel) < top"
proof -
  have norm_lp:
      "slp_positive_ennreal_lp_on_plane r
        (\<lambda>x. ennreal (norm (g x)))"
    by (rule slp_positive_ennreal_lp_norm_of_complex[OF g_lp])
  have product_lp:
      "slp_positive_ennreal_lp_on_plane 1
        (\<lambda>x. F x * ennreal (norm (g x)))"
    by (rule slp_positive_ennreal_lp_product[where a = 1 and q = q and r = r,
          OF zero_less_one _ _ _ F_lp norm_lp])
      (use q_lower r_lower conjugate in simp_all)
  show ?thesis
    by (rule slp_positive_ennreal_l1_integral_lt_top[OF product_lp])
qed

end
