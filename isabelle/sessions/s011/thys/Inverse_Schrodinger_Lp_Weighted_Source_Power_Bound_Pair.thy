theory Inverse_Schrodinger_Lp_Weighted_Source_Power_Bound_Pair
  imports Inverse_Schrodinger_Lp_Integral_Minkowski_Power_Pair_AE
begin

section \<open>Quantitative weighted source-power bound\<close>

lemma slp_weighted_source_power_bound_pair:
  fixes weight :: "(slp_point \<times> slp_point) \<Rightarrow> real"
    and datum ::
      "(slp_point \<times> slp_point) \<Rightarrow> slp_point \<Rightarrow> real"
  assumes weight_measurable: "weight \<in> borel_measurable lborel"
    and datum_joint_measurable:
      "case_prod datum \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    and weight_nonnegative: "\<And>pair. 0 \<le> weight pair"
    and datum_nonnegative: "\<And>pair output. 0 \<le> datum pair output"
    and weight_integrable: "integrable lborel weight"
    and datum_power_integrable:
      "\<And>pair. integrable lborel (\<lambda>output. datum pair output powr a)"
    and datum_power_bound:
      "\<And>pair. integral\<^sup>L lborel (\<lambda>output. datum pair output powr a)
        \<le> L"
    and L_nonnegative: "0 \<le> L"
  shows source_integrable:
    "integrable lborel
      (\<lambda>output. integral\<^sup>L lborel
        (\<lambda>pair. weight pair * datum pair output powr a))"
    and source_bound:
    "integral\<^sup>L lborel
        (\<lambda>output. integral\<^sup>L lborel
          (\<lambda>pair. weight pair * datum pair output powr a))
      \<le> L * integral\<^sup>L lborel weight"
proof -
  let ?F = "\<lambda>(output, pair). weight pair * datum pair output powr a"
  have joint_integrable:
      "integrable
        ((lborel :: slp_point measure) \<Otimes>\<^sub>M
          (lborel :: (slp_point \<times> slp_point) measure)) ?F"
    by (rule slp_weighted_joint_integrable_pair(1)[OF
          weight_measurable datum_joint_measurable weight_nonnegative
          datum_nonnegative weight_integrable datum_power_integrable
          datum_power_bound L_nonnegative])
  have source_integrable_fact:
      "integrable lborel
        (\<lambda>output. integral\<^sup>L lborel
          (\<lambda>pair. weight pair * datum pair output powr a))"
    by (rule slp_weighted_joint_integrable_pair(3)[OF
          weight_measurable datum_joint_measurable weight_nonnegative
          datum_nonnegative weight_integrable datum_power_integrable
          datum_power_bound L_nonnegative])
  have source_product:
      "integral\<^sup>L lborel
          (\<lambda>output. integral\<^sup>L lborel
            (\<lambda>pair. weight pair * datum pair output powr a)) =
        integral\<^sup>L
          ((lborel :: slp_point measure) \<Otimes>\<^sub>M
            (lborel :: (slp_point \<times> slp_point) measure)) ?F"
    using lborel_pair.integral_fst[
      where f="\<lambda>output pair. weight pair * datum pair output powr a",
      OF joint_integrable]
    by simp
  have pair_product:
      "integral\<^sup>L lborel
          (\<lambda>pair. integral\<^sup>L lborel
            (\<lambda>output. weight pair * datum pair output powr a)) =
        integral\<^sup>L
          ((lborel :: slp_point measure) \<Otimes>\<^sub>M
            (lborel :: (slp_point \<times> slp_point) measure)) ?F"
    using lborel_pair.integral_snd[
      where f="\<lambda>output pair. weight pair * datum pair output powr a",
      OF joint_integrable]
    by simp
  have inner_bound:
      "integral\<^sup>L lborel
          (\<lambda>output. weight pair * datum pair output powr a)
        \<le> weight pair * L"
    for pair
  proof -
    have factor:
        "integral\<^sup>L lborel
            (\<lambda>output. weight pair * datum pair output powr a) =
          weight pair * integral\<^sup>L lborel
            (\<lambda>output. datum pair output powr a)"
      using datum_power_integrable[of pair] by simp
    show ?thesis
      unfolding factor
      by (rule mult_left_mono[OF datum_power_bound weight_nonnegative])
  qed
  have pair_outer_integrable:
      "integrable lborel
        (\<lambda>pair. integral\<^sup>L lborel
          (\<lambda>output. weight pair * datum pair output powr a))"
    using lborel_pair.integrable_snd[
      where f="\<lambda>output pair. weight pair * datum pair output powr a",
      OF joint_integrable]
    by simp
  have majorant_integrable:
      "integrable lborel (\<lambda>pair. weight pair * L)"
    using weight_integrable by simp
  have pair_outer_bound:
      "integral\<^sup>L lborel
          (\<lambda>pair. integral\<^sup>L lborel
            (\<lambda>output. weight pair * datum pair output powr a))
        \<le> integral\<^sup>L lborel (\<lambda>pair. weight pair * L)"
  proof (rule integral_mono[OF pair_outer_integrable majorant_integrable])
    fix pair :: "slp_point \<times> slp_point"
    assume "pair \<in> space lborel"
    show
      "integral\<^sup>L lborel
          (\<lambda>output. weight pair * datum pair output powr a)
        \<le> weight pair * L"
      by (rule inner_bound)
  qed
  show source_integrable:
      "integrable lborel
        (\<lambda>output. integral\<^sup>L lborel
          (\<lambda>pair. weight pair * datum pair output powr a))"
    by (rule source_integrable_fact)
  show source_bound:
      "integral\<^sup>L lborel
          (\<lambda>output. integral\<^sup>L lborel
            (\<lambda>pair. weight pair * datum pair output powr a))
        \<le> L * integral\<^sup>L lborel weight"
  proof -
    have rhs_factor:
        "integral\<^sup>L lborel (\<lambda>pair. weight pair * L) =
          L * integral\<^sup>L lborel weight"
      using weight_integrable by (simp add: mult.commute)
    have source_pair:
        "integral\<^sup>L lborel
            (\<lambda>output. integral\<^sup>L lborel
              (\<lambda>pair. weight pair * datum pair output powr a)) =
          integral\<^sup>L lborel
            (\<lambda>pair. integral\<^sup>L lborel
              (\<lambda>output. weight pair * datum pair output powr a))"
      using source_product pair_product by simp
    show ?thesis
      using pair_outer_bound by (simp only: source_pair rhs_factor)
  qed
qed

end
