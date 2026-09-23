theory Inverse_Schrodinger_Lp_Integral_Minkowski_Power_Pair
  imports Inverse_Schrodinger_Lp_Integral_Minkowski_Power
begin

section \<open>Integral Minkowski over a pair of branch variables\<close>

lemma slp_integral_minkowski_power_pair:
  fixes weight :: "(slp_point \<times> slp_point) \<Rightarrow> real"
    and datum ::
      "(slp_point \<times> slp_point) \<Rightarrow> slp_point \<Rightarrow> real"
  assumes a_lower: "1 < a"
    and b_lower: "1 < b"
    and conjugate: "1 / a + 1 / b = 1"
    and weight_measurable: "weight \<in> borel_measurable lborel"
    and datum_joint_measurable:
      "case_prod datum \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    and weight_nonnegative: "\<And>t. 0 \<le> weight t"
    and datum_nonnegative: "\<And>t u. 0 \<le> datum t u"
    and weight_integrable: "integrable lborel weight"
    and fiber_power_integrable:
      "\<And>u. integrable lborel (\<lambda>t. weight t * datum t u powr a)"
    and source_power_integrable:
      "integrable lborel
        (\<lambda>u. integral\<^sup>L lborel
          (\<lambda>t. weight t * datum t u powr a))"
  shows
    "integrable lborel
      (\<lambda>u. (integral\<^sup>L lborel
        (\<lambda>t. weight t * datum t u)) powr a)"
    "integral\<^sup>L lborel
        (\<lambda>u. (integral\<^sup>L lborel
          (\<lambda>t. weight t * datum t u)) powr a) \<le>
      (integral\<^sup>L lborel weight) powr (a / b) *
        integral\<^sup>L lborel
          (\<lambda>u. integral\<^sup>L lborel
            (\<lambda>t. weight t * datum t u powr a))"
proof -
  note [measurable] = datum_joint_measurable weight_measurable
  let ?H = "\<lambda>u. integral\<^sup>L lborel
    (\<lambda>t. weight t * datum t u)"
  let ?P = "\<lambda>u. integral\<^sup>L lborel
    (\<lambda>t. weight t * datum t u powr a)"
  let ?W = "integral\<^sup>L lborel weight"
  have datum_swapped_joint_measurable:
      "(\<lambda>ut. datum (snd ut) (fst ut))
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by measurable
  have weighted_swapped_joint_measurable:
      "(\<lambda>ut. weight (snd ut) * datum (snd ut) (fst ut))
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by measurable
  have weighted_power_swapped_joint_measurable:
      "(\<lambda>ut.
        weight (snd ut) * datum (snd ut) (fst ut) powr a)
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by measurable
  have H_measurable: "?H \<in> borel_measurable lborel"
    by (rule lborel.borel_measurable_lebesgue_integral[
          where f="\<lambda>u t. weight t * datum t u"])
      (use weighted_swapped_joint_measurable in simp)
  have P_measurable: "?P \<in> borel_measurable lborel"
    by (rule lborel.borel_measurable_lebesgue_integral[
          where f="\<lambda>u t. weight t * datum t u powr a"])
      (use weighted_power_swapped_joint_measurable in simp)
  have H_nonnegative: "0 \<le> ?H u" for u
    by (rule integral_nonneg_AE)
      (simp add: weight_nonnegative datum_nonnegative)
  have P_nonnegative: "0 \<le> ?P u" for u
    by (rule integral_nonneg_AE)
      (simp add: weight_nonnegative)
  have W_nonnegative: "0 \<le> ?W"
    by (rule integral_nonneg_AE) (simp add: weight_nonnegative)
  have pointwise_bound:
      "?H u powr a \<le> ?W powr (a / b) * ?P u"
    for u
  proof -
    have datum_section_measurable:
        "(\<lambda>t. datum t u) \<in> borel_measurable lborel"
      by measurable
    show ?thesis
      by (rule slp_weighted_holder_power(2)[OF a_lower b_lower conjugate
            weight_measurable datum_section_measurable
            weight_nonnegative _ weight_integrable
            fiber_power_integrable])
        (rule datum_nonnegative)
  qed
  have target_measurable:
      "(\<lambda>u. ?H u powr a) \<in> borel_measurable lborel"
    using H_measurable by measurable
  have majorant_integrable:
      "integrable lborel (\<lambda>u. ?W powr (a / b) * ?P u)"
    using source_power_integrable by simp
  have target_integrable:
      "integrable lborel (\<lambda>u. ?H u powr a)"
  proof (rule Bochner_Integration.integrable_bound[OF majorant_integrable
        target_measurable])
    show "AE u in lborel.
        norm (?H u powr a) \<le>
          norm (?W powr (a / b) * ?P u)"
    proof (rule AE_I2)
      fix u :: slp_point
      show "norm (?H u powr a) \<le>
          norm (?W powr (a / b) * ?P u)"
        using pointwise_bound[of u] H_nonnegative[of u]
          P_nonnegative[of u] W_nonnegative
        by simp
    qed
  qed
  show "integrable lborel (\<lambda>u. ?H u powr a)"
    by (rule target_integrable)
  show "integral\<^sup>L lborel (\<lambda>u. ?H u powr a) \<le>
      ?W powr (a / b) * integral\<^sup>L lborel ?P"
  proof -
    have integral_bound:
        "integral\<^sup>L lborel (\<lambda>u. ?H u powr a) \<le>
          integral\<^sup>L lborel (\<lambda>u. ?W powr (a / b) * ?P u)"
      by (rule integral_mono[OF target_integrable majorant_integrable
            pointwise_bound])
    show ?thesis
      using integral_bound source_power_integrable by simp
  qed
qed

end
