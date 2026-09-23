theory Inverse_Schrodinger_Lp_Ennreal_Majorant_Complex_Integral_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Mixed_Center_Cauchy_Terminal_Smooth_Error_Mass_Decay"
begin

section \<open>Complex integral decay from an ennreal majorant\<close>

theorem slp_complex_kernel_integral_tendsto_zero_from_ennreal_majorant:
  fixes kernel :: "real \<Rightarrow> slp_point \<Rightarrow> complex"
    and majorant :: "real \<Rightarrow> slp_point \<Rightarrow> ennreal"
  assumes kernel_measurable:
      "\<And>tau. kernel tau \<in> borel_measurable lborel"
    and kernel_bound:
      "\<And>tau. AE x in lborel.
        ennreal (norm (kernel tau x)) \<le> majorant tau x"
    and majorant_decay:
      "((\<lambda>tau. \<integral>\<^sup>+ x. majorant tau x \<partial>lborel)
        \<longlongrightarrow> 0) at_top"
  shows
      "((\<lambda>tau. integral\<^sup>L lborel (kernel tau))
        \<longlongrightarrow> 0) at_top"
proof -
  let ?I = "\<lambda>tau. integral\<^sup>L lborel (kernel tau)"
  let ?M = "\<lambda>tau. \<integral>\<^sup>+ x. majorant tau x \<partial>lborel"
  have eventually_M_lt_one:
      "eventually (\<lambda>tau. ?M tau < (1 :: ennreal)) at_top"
    using order_tendstoD(2)[OF majorant_decay, of "1 :: ennreal"] by simp
  have eventually_norm_le:
      "eventually (\<lambda>tau. ennreal (norm (?I tau)) \<le> ?M tau) at_top"
    using eventually_M_lt_one
  proof eventually_elim
    fix tau
    assume M_lt_one: "?M tau < (1 :: ennreal)"
    have M_lt_top: "?M tau < top_class.top"
      by (rule less_trans[OF M_lt_one]) simp
    have norm_mass_finite:
        "(\<integral>\<^sup>+ x. ennreal (norm (kernel tau x)) \<partial>lborel)
          < \<infinity>"
      unfolding infinity_ennreal_def
      by (rule le_less_trans[OF
            nn_integral_mono_AE[OF kernel_bound[of tau]] M_lt_top])
    have kernel_integrable: "integrable lborel (kernel tau)"
      unfolding integrable_iff_bounded
      using kernel_measurable[of tau] norm_mass_finite by blast
    have integral_bound:
        "ennreal (norm (?I tau)) \<le>
          (\<integral>\<^sup>+ x. ennreal (norm (kernel tau x)) \<partial>lborel)"
      by (rule Bochner_Integration.integral_norm_bound_ennreal[OF
            kernel_integrable])
    have norm_mass_le:
        "(\<integral>\<^sup>+ x. ennreal (norm (kernel tau x)) \<partial>lborel)
          \<le> ?M tau"
      by (rule nn_integral_mono_AE[OF kernel_bound[of tau]])
    show "ennreal (norm (?I tau)) \<le> ?M tau"
      by (rule order_trans[OF integral_bound norm_mass_le])
  qed
  have ennreal_norm_decay:
      "((\<lambda>tau. ennreal (norm (?I tau))) \<longlongrightarrow> 0) at_top"
    by (rule tendsto_sandwich[
          where f="\<lambda>_. 0" and h="\<lambda>tau. ?M tau"])
      (use eventually_norm_le majorant_decay in auto)
  have real_norm_decay:
      "((\<lambda>tau. norm (?I tau)) \<longlongrightarrow> 0) at_top"
  proof -
    have cast_decay:
        "((\<lambda>tau. ennreal (norm (?I tau))) \<longlongrightarrow> ennreal 0)
          at_top"
      using ennreal_norm_decay by simp
    show ?thesis
      by (rule tendsto_ennrealD[OF cast_decay])
        (simp_all add: eventuallyI)
  qed
  show ?thesis
    using real_norm_decay by (rule tendsto_norm_zero_cancel)
qed

end
