theory Inverse_Schrodinger_Lp_Integral_Minkowski_Power_Plane_AE
  imports Inverse_Schrodinger_Lp_Weighted_Source_Power_Bound_Plane
begin

section \<open>Integral Minkowski over a planar root with almost-everywhere fibers\<close>

lemma slp_integral_minkowski_power_plane_AE:
  fixes weight :: "slp_point \<Rightarrow> real"
    and datum :: "slp_point \<Rightarrow> slp_point \<Rightarrow> real"
  assumes a_lower: "1 < a"
    and b_lower: "1 < b"
    and conjugate: "1 / a + 1 / b = 1"
    and weight_measurable: "weight \<in> borel_measurable lborel"
    and datum_joint_measurable:
      "case_prod datum \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    and weight_nonnegative: "\<And>root. 0 \<le> weight root"
    and datum_nonnegative: "\<And>root output. 0 \<le> datum root output"
    and weight_integrable: "integrable lborel weight"
    and fiber_power_integrable:
      "AE output in lborel.
        integrable lborel
          (\<lambda>root. weight root * datum root output powr a)"
    and source_power_integrable:
      "integrable lborel
        (\<lambda>output. integral\<^sup>L lborel
          (\<lambda>root. weight root * datum root output powr a))"
  shows target_integrable:
    "integrable lborel
      (\<lambda>output. (integral\<^sup>L lborel
        (\<lambda>root. weight root * datum root output)) powr a)"
    and target_bound:
    "integral\<^sup>L lborel
        (\<lambda>output. (integral\<^sup>L lborel
          (\<lambda>root. weight root * datum root output)) powr a) \<le>
      (integral\<^sup>L lborel weight) powr (a / b) *
        integral\<^sup>L lborel
          (\<lambda>output. integral\<^sup>L lborel
            (\<lambda>root. weight root * datum root output powr a))"
proof -
  note [measurable] = datum_joint_measurable weight_measurable
  let ?H = "\<lambda>output. integral\<^sup>L lborel
    (\<lambda>root. weight root * datum root output)"
  let ?P = "\<lambda>output. integral\<^sup>L lborel
    (\<lambda>root. weight root * datum root output powr a)"
  let ?W = "integral\<^sup>L lborel weight"
  have datum_swapped_joint_measurable:
      "(\<lambda>pair. datum (snd pair) (fst pair))
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by measurable
  have weighted_swapped_joint_measurable:
      "(\<lambda>pair. weight (snd pair) * datum (snd pair) (fst pair))
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by measurable
  have weighted_power_swapped_joint_measurable:
      "(\<lambda>pair. weight (snd pair) *
        datum (snd pair) (fst pair) powr a)
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by measurable
  have H_measurable: "?H \<in> borel_measurable lborel"
    by (rule lborel.borel_measurable_lebesgue_integral[
          where f="\<lambda>output root. weight root * datum root output"])
      (use weighted_swapped_joint_measurable in simp)
  have P_measurable: "?P \<in> borel_measurable lborel"
    by (rule lborel.borel_measurable_lebesgue_integral[
          where f="\<lambda>output root.
            weight root * datum root output powr a"])
      (use weighted_power_swapped_joint_measurable in simp)
  have H_nonnegative: "0 \<le> ?H out" for out
    by (rule integral_nonneg_AE)
      (simp add: weight_nonnegative datum_nonnegative)
  have P_nonnegative: "0 \<le> ?P out" for out
    by (rule integral_nonneg_AE) (simp add: weight_nonnegative)
  have W_nonnegative: "0 \<le> ?W"
    by (rule integral_nonneg_AE) (simp add: weight_nonnegative)
  have pointwise_bound:
      "AE output in lborel.
        ?H output powr a \<le> ?W powr (a / b) * ?P output"
    using fiber_power_integrable
  proof eventually_elim
    fix out :: slp_point
    assume fiber:
      "integrable lborel
        (\<lambda>root. weight root * datum root out powr a)"
    have datum_section_measurable:
        "(\<lambda>root. datum root out) \<in> borel_measurable lborel"
      by measurable
    show "?H out powr a \<le> ?W powr (a / b) * ?P out"
      by (rule slp_weighted_holder_power(2)[OF
            a_lower b_lower conjugate weight_measurable
            datum_section_measurable weight_nonnegative _
            weight_integrable fiber])
        (rule datum_nonnegative)
  qed
  have target_measurable:
      "(\<lambda>output. ?H output powr a) \<in> borel_measurable lborel"
    using H_measurable by measurable
  have majorant_integrable:
      "integrable lborel
        (\<lambda>output. ?W powr (a / b) * ?P output)"
    using source_power_integrable by simp
  have target_integrable_fact:
      "integrable lborel (\<lambda>output. ?H output powr a)"
  proof (rule Bochner_Integration.integrable_bound[OF majorant_integrable
        target_measurable])
    show "AE output in lborel.
        norm (?H output powr a) \<le>
          norm (?W powr (a / b) * ?P output)"
      using pointwise_bound
    proof eventually_elim
      fix out :: slp_point
      assume bound: "?H out powr a \<le> ?W powr (a / b) * ?P out"
      show "norm (?H out powr a) \<le>
          norm (?W powr (a / b) * ?P out)"
        using bound H_nonnegative[of out] P_nonnegative[of out] W_nonnegative
        by simp
    qed
  qed
  show target_integrable:
      "integrable lborel (\<lambda>output. ?H output powr a)"
    by (rule target_integrable_fact)
  show target_bound:
      "integral\<^sup>L lborel (\<lambda>output. ?H output powr a) \<le>
        ?W powr (a / b) * integral\<^sup>L lborel ?P"
  proof -
    have integral_bound:
        "integral\<^sup>L lborel (\<lambda>output. ?H output powr a) \<le>
          integral\<^sup>L lborel
            (\<lambda>output. ?W powr (a / b) * ?P output)"
      by (rule integral_mono_AE[OF target_integrable_fact
            majorant_integrable pointwise_bound])
    show ?thesis using integral_bound source_power_integrable by simp
  qed
qed

end
