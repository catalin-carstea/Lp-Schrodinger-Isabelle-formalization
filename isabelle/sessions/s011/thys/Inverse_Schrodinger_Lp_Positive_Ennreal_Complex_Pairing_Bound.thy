theory Inverse_Schrodinger_Lp_Positive_Ennreal_Complex_Pairing_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Positive_Ennreal_Complex_Pairing"
begin

section \<open>Quantitative positive-density and complex-data pairings\<close>

lemma slp_positive_ennreal_lp_complex_pairing_le:
  fixes q r L :: real
  assumes q_lower: "1 < q"
    and r_lower: "1 < r"
    and conjugate: "1 / q + 1 / r = 1"
    and F_lp: "slp_positive_ennreal_lp_on_plane q F"
    and F_power_bound:
      "integral\<^sup>L lborel (\<lambda>x. enn2real (F x) powr q) \<le> L"
    and L_nonnegative: "0 \<le> L"
    and g_lp: "aim_complex_lp_on_plane r g"
  shows
    "(\<integral>\<^sup>+ x. F x * ennreal (norm (g x)) \<partial>lborel) \<le>
      ennreal
        (L / q +
          integral\<^sup>L lborel (\<lambda>x. norm (g x) powr r) / r)"
proof -
  have q_positive: "0 < q"
    using q_lower by simp
  have r_positive: "0 < r"
    using r_lower by simp
  have F_finite: "AE x in lborel. F x < top"
    and F_power_integrable:
      "integrable lborel (\<lambda>x. enn2real (F x) powr q)"
    using F_lp unfolding slp_positive_ennreal_lp_on_plane_def by blast+
  have g_power_integrable:
      "integrable lborel (\<lambda>x. norm (g x) powr r)"
    using g_lp unfolding aim_complex_lp_on_plane_def by blast
  let ?majorant =
    "\<lambda>x. enn2real (F x) powr q / q + norm (g x) powr r / r"
  have majorant_integrable: "integrable lborel ?majorant"
    using F_power_integrable g_power_integrable by simp
  have majorant_nonnegative: "0 \<le> ?majorant x" for x
  proof -
    have F_quotient_nonnegative:
        "0 \<le> enn2real (F x) powr q / q"
    proof (rule divide_nonneg_pos)
      show "0 \<le> enn2real (F x) powr q" by simp
      show "0 < q" using q_positive .
    qed
    have g_quotient_nonnegative:
        "0 \<le> norm (g x) powr r / r"
    proof (rule divide_nonneg_pos)
      show "0 \<le> norm (g x) powr r" by simp
      show "0 < r" using r_positive .
    qed
    show ?thesis
      by (rule add_nonneg_nonneg[OF
            F_quotient_nonnegative g_quotient_nonnegative])
  qed
  have pointwise:
      "AE x in lborel.
        F x * ennreal (norm (g x)) \<le> ennreal (?majorant x)"
    using F_finite
  proof eventually_elim
    fix x
    assume F_finite_at: "F x < top"
    have young:
        "enn2real (F x) * norm (g x) \<le> ?majorant x"
      by (rule Youngs_inequality[OF q_lower r_lower conjugate]) simp_all
    have product_lift:
        "F x * ennreal (norm (g x)) =
          ennreal (enn2real (F x) * norm (g x))"
      using F_finite_at
      by (simp add: ennreal_enn2real_if ennreal_mult)
    show
        "F x * ennreal (norm (g x)) \<le> ennreal (?majorant x)"
      unfolding product_lift by (rule ennreal_leI[OF young])
  qed
  have pairing_le_majorant:
      "(\<integral>\<^sup>+ x. F x * ennreal (norm (g x)) \<partial>lborel) \<le>
        (\<integral>\<^sup>+ x. ennreal (?majorant x) \<partial>lborel)"
    by (rule nn_integral_mono_AE[OF pointwise])
  have majorant_nn:
      "(\<integral>\<^sup>+ x. ennreal (?majorant x) \<partial>lborel) =
        ennreal (integral\<^sup>L lborel ?majorant)"
    by (rule nn_integral_eq_integral[OF majorant_integrable])
      (rule AE_I2, rule majorant_nonnegative)
  have majorant_integral:
      "integral\<^sup>L lborel ?majorant =
        integral\<^sup>L lborel (\<lambda>x. enn2real (F x) powr q) / q +
        integral\<^sup>L lborel (\<lambda>x. norm (g x) powr r) / r"
    using F_power_integrable g_power_integrable by simp
  have F_quotient_bound:
      "integral\<^sup>L lborel (\<lambda>x. enn2real (F x) powr q) / q \<le>
        L / q"
    by (rule divide_right_mono[OF F_power_bound])
      (rule less_imp_le[OF q_positive])
  have majorant_bound:
      "integral\<^sup>L lborel ?majorant \<le>
        L / q +
          integral\<^sup>L lborel (\<lambda>x. norm (g x) powr r) / r"
    unfolding majorant_integral
    using F_quotient_bound by simp
  have lifted_majorant_bound:
      "ennreal (integral\<^sup>L lborel ?majorant) \<le>
        ennreal
          (L / q +
            integral\<^sup>L lborel (\<lambda>x. norm (g x) powr r) / r)"
    by (rule ennreal_leI[OF majorant_bound])
  show ?thesis
    using pairing_le_majorant majorant_nn lifted_majorant_bound by simp
qed

end
