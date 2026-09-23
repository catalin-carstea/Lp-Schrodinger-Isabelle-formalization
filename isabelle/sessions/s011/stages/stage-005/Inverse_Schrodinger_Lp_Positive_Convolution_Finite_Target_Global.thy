theory Inverse_Schrodinger_Lp_Positive_Convolution_Finite_Target_Global
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Positive_Convolution_Finite_Target_Pointwise"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Positive_Convolution_Mixed_Global"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Positive_Ennreal_Lp"
begin

section \<open>Global Young bound for finite targets\<close>

theorem slp_positive_convolution_finite_target_global:
  fixes t :: real
    and f g :: "slp_point \<Rightarrow> real"
    and H :: "slp_point \<Rightarrow> ennreal"
  assumes t_lower: "1 < t"
    and f_measurable[measurable]: "f \<in> borel_measurable lborel"
    and g_measurable[measurable]: "g \<in> borel_measurable lborel"
    and f_nonnegative: "\<And>x. 0 \<le> f x"
    and g_nonnegative: "\<And>x. 0 \<le> g x"
    and f_power_integrable:
      "integrable lborel
        (\<lambda>x. f x powr slp_mixed_unweighted_branch_exponent t)"
    and g_power_integrable:
      "integrable lborel
        (\<lambda>x. g x powr slp_mixed_unweighted_branch_exponent t)"
  defines
    "H \<equiv> \<lambda>out.
      (\<integral>\<^sup>+ root. ennreal (f root * g (out - root))
        \<partial>lborel)"
  shows H_measurable: "H \<in> borel_measurable lborel"
    and H_finite: "AE out in lborel. H out < \<infinity>"
    and H_power_integrable:
      "integrable lborel (\<lambda>out. enn2real (H out) powr t)"
    and H_power_bound:
      "integral\<^sup>L lborel (\<lambda>out. enn2real (H out) powr t)
        \<le>
        (integral\<^sup>L lborel
            (\<lambda>x. f x powr slp_mixed_unweighted_branch_exponent t) *
          integral\<^sup>L lborel
            (\<lambda>x. g x powr slp_mixed_unweighted_branch_exponent t)) *
        (integral\<^sup>L lborel
            (\<lambda>x. f x powr slp_mixed_unweighted_branch_exponent t) *
          integral\<^sup>L lborel
            (\<lambda>x. g x powr slp_mixed_unweighted_branch_exponent t))
          powr ((t - 1) / 2)"
    and H_lp: "slp_positive_ennreal_lp_on_plane t H"
proof -
  let ?a = "slp_mixed_unweighted_branch_exponent t"
  let ?F = "\<lambda>x. f x powr ?a"
  let ?G = "\<lambda>x. g x powr ?a"
  let ?U = "\<lambda>out.
    (\<integral>\<^sup>+ root. ennreal (?F root * ?G (out - root))
      \<partial>lborel)"
  let ?I_f = "integral\<^sup>L lborel ?F"
  let ?I_g = "integral\<^sup>L lborel ?G"
  let ?K = "(?I_f * ?I_g) powr ((t - 1) / 2)"
  have F_measurable[measurable]: "?F \<in> borel_measurable lborel"
    by measurable
  have G_measurable[measurable]: "?G \<in> borel_measurable lborel"
    by measurable
  have F_nonnegative: "0 \<le> ?F x" for x by simp
  have G_nonnegative: "0 \<le> ?G x" for x by simp
  have I_f_nonnegative: "0 \<le> ?I_f"
    by (rule integral_nonneg_AE, rule AE_I2, rule F_nonnegative)
  have I_g_nonnegative: "0 \<le> ?I_g"
    by (rule integral_nonneg_AE, rule AE_I2, rule G_nonnegative)
  have product_nonnegative: "0 \<le> ?I_f * ?I_g"
    using I_f_nonnegative I_g_nonnegative by simp
  have K_nonnegative: "0 \<le> ?K" by simp
  show H_measurable: "H \<in> borel_measurable lborel"
    unfolding H_def by measurable
  have U_measurable[measurable]: "?U \<in> borel_measurable lborel"
    by measurable
  have U_mass:
      "(\<integral>\<^sup>+ out. ?U out \<partial>lborel) =
        ennreal (?I_f * ?I_g)"
    by (rule slp_positive_real_convolution_mass[OF F_measurable G_measurable
          F_nonnegative G_nonnegative f_power_integrable
          g_power_integrable])
  have U_mass_less_top:
      "(\<integral>\<^sup>+ out. ?U out \<partial>lborel) < \<infinity>"
    using U_mass by simp
  have U_finite: "AE out in lborel. ?U out < \<infinity>"
  proof -
    have U_not_top: "AE out in lborel. ?U out \<noteq> \<infinity>"
      by (rule nn_integral_PInf_AE[OF U_measurable])
        (use U_mass_less_top in simp)
    show ?thesis
      using U_not_top by eventually_elim (simp add: less_top)
  qed
  have pointwise:
      "AE out in lborel.
        enn2real (H out) powr t \<le> enn2real (?U out) * ?K"
    using U_finite
  proof eventually_elim
    fix out :: slp_point
    assume U_output_finite: "?U out < \<infinity>"
    note local_bound =
      slp_positive_convolution_finite_target_pointwise(2)[OF t_lower
        f_measurable g_measurable f_nonnegative g_nonnegative
        f_power_integrable g_power_integrable U_output_finite]
    show "enn2real (H out) powr t \<le> enn2real (?U out) * ?K"
      using local_bound unfolding H_def by simp
  qed
  have H_finite_fact: "AE out in lborel. H out < \<infinity>"
    using U_finite
  proof eventually_elim
    fix out :: slp_point
    assume U_output_finite: "?U out < \<infinity>"
    show "H out < \<infinity>"
      unfolding H_def
      by (rule slp_positive_convolution_finite_target_pointwise(1)[OF
            t_lower f_measurable g_measurable f_nonnegative g_nonnegative
            f_power_integrable g_power_integrable U_output_finite])
  qed
  show H_finite: "AE out in lborel. H out < \<infinity>"
    by (rule H_finite_fact)
  have U_real_measurable:
      "(\<lambda>out. enn2real (?U out)) \<in> borel_measurable lborel"
    using U_measurable by measurable
  have U_real_nn:
      "(\<integral>\<^sup>+ out. enn2real (?U out) \<partial>lborel) =
        (\<integral>\<^sup>+ out. ?U out \<partial>lborel)"
    by (rule nn_integral_cong_AE)
      (use U_finite in eventually_elim; simp)
  have U_real_integrable:
      "integrable lborel (\<lambda>out. enn2real (?U out))"
  proof (rule integrableI_nn_integral_finite[OF U_real_measurable])
    show "AE out in lborel. 0 \<le> enn2real (?U out)" by simp
    show "(\<integral>\<^sup>+ out. enn2real (?U out) \<partial>lborel) =
        ennreal
          (enn2real
            (\<integral>\<^sup>+ out. enn2real (?U out) \<partial>lborel))"
      using U_real_nn U_mass_less_top by simp
  qed
  have U_real_integral_nonnegative:
      "0 \<le> integral\<^sup>L lborel (\<lambda>out. enn2real (?U out))"
    by (rule integral_nonneg_AE, rule AE_I2) simp
  have U_real_integral:
      "integral\<^sup>L lborel (\<lambda>out. enn2real (?U out)) =
        ?I_f * ?I_g"
  proof -
    have lifted:
        "ennreal
            (integral\<^sup>L lborel
              (\<lambda>out. enn2real (?U out))) =
          ennreal (?I_f * ?I_g)"
      using nn_integral_eq_integral[OF U_real_integrable] U_real_nn U_mass
      by simp
    show ?thesis
      using lifted U_real_integral_nonnegative product_nonnegative by simp
  qed
  have majorant_integrable:
      "integrable lborel (\<lambda>out. enn2real (?U out) * ?K)"
    using U_real_integrable by (rule integrable_mult_left)
  have H_power_measurable:
      "(\<lambda>out. enn2real (H out) powr t)
        \<in> borel_measurable lborel"
    using H_measurable by measurable
  have power_integrable:
      "integrable lborel (\<lambda>out. enn2real (H out) powr t)"
    apply (rule Bochner_Integration.integrable_bound[OF majorant_integrable
          H_power_measurable])
    using pointwise K_nonnegative
    apply simp
    done
  show H_power_integrable:
      "integrable lborel (\<lambda>out. enn2real (H out) powr t)"
    by (rule power_integrable)
  have integral_bound:
      "integral\<^sup>L lborel (\<lambda>out. enn2real (H out) powr t)
        \<le>
        integral\<^sup>L lborel (\<lambda>out. enn2real (?U out) * ?K)"
    by (rule integral_mono_AE[OF power_integrable majorant_integrable
          pointwise])
  show H_power_bound:
      "integral\<^sup>L lborel (\<lambda>out. enn2real (H out) powr t)
        \<le> (?I_f * ?I_g) * ?K"
    using integral_bound U_real_integral by simp
  have H_finite_top:
      "AE out in lborel. H out < (top_class.top :: ennreal)"
    using H_finite_fact by simp
  show H_lp: "slp_positive_ennreal_lp_on_plane t H"
    unfolding slp_positive_ennreal_lp_on_plane_def
    apply (rule conjI)
     apply (rule H_measurable)
    apply (rule conjI)
     apply (rule H_finite_top)
    apply (rule power_integrable)
    done
qed

end
