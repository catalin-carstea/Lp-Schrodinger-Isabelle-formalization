theory Inverse_Schrodinger_Lp_Positive_Ennreal_Lp_Domination
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Mixed_Product_Duality_Exponents"
begin

section \<open>Almost-everywhere domination in the positive plane Lp class\<close>

theorem slp_positive_ennreal_lp_mono_AE:
  fixes F G :: "slp_point \<Rightarrow> ennreal"
  assumes exponent_positive: "0 < s"
    and majorant_lp: "slp_positive_ennreal_lp_on_plane s F"
    and dominated_measurable: "G \<in> borel_measurable lborel"
    and dominated: "AE x in lborel. G x \<le> F x"
  shows "slp_positive_ennreal_lp_on_plane s G"
proof -
  have majorant_finite: "AE x in lborel. F x < top_class.top"
    and majorant_power_integrable:
      "integrable lborel (\<lambda>x. enn2real (F x) powr s)"
    using majorant_lp
    unfolding slp_positive_ennreal_lp_on_plane_def by blast+
  have dominated_finite: "AE x in lborel. G x < top_class.top"
    using dominated majorant_finite
  proof eventually_elim
    fix x :: slp_point
    assume "G x \<le> F x" and "F x < top_class.top"
    then show "G x < top_class.top"
      by (rule order_le_less_trans)
  qed
  have dominated_power_measurable:
      "(\<lambda>x. enn2real (G x) powr s) \<in> borel_measurable lborel"
    using dominated_measurable by measurable
  have dominated_power_integrable:
      "integrable lborel (\<lambda>x. enn2real (G x) powr s)"
  proof (rule Bochner_Integration.integrable_bound[OF
        majorant_power_integrable dominated_power_measurable])
    show "AE x in lborel.
        norm_class.norm (enn2real (G x) powr s) \<le>
          norm_class.norm (enn2real (F x) powr s)"
      using dominated majorant_finite
    proof eventually_elim
      fix x :: slp_point
      assume pointwise: "G x \<le> F x"
        and finite: "F x < top_class.top"
      have real_order: "enn2real (G x) \<le> enn2real (F x)"
        by (rule enn2real_mono[OF pointwise]) (use finite in simp)
      have power_order:
          "enn2real (G x) powr s \<le> enn2real (F x) powr s"
        by (rule powr_mono2[OF less_imp_le[OF exponent_positive]])
          (use real_order in simp_all)
      show "norm_class.norm (enn2real (G x) powr s) \<le>
          norm_class.norm (enn2real (F x) powr s)"
        using power_order by simp
    qed
  qed
  show ?thesis
    unfolding slp_positive_ennreal_lp_on_plane_def
    using dominated_measurable dominated_finite dominated_power_integrable
    by blast
qed

end
