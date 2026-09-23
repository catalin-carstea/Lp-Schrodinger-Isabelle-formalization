theory Inverse_Schrodinger_Lp_Weighted_Source_Power_Bound_Plane
  imports Inverse_Schrodinger_Lp_Integral_Minkowski_Power
begin

section \<open>Weighted source-power bound over a planar root\<close>

lemma slp_weighted_source_power_bound_plane:
  fixes weight :: "slp_point \<Rightarrow> real"
    and datum :: "slp_point \<Rightarrow> slp_point \<Rightarrow> real"
  assumes weight_measurable: "weight \<in> borel_measurable lborel"
    and datum_joint_measurable:
      "case_prod datum \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    and weight_nonnegative: "\<And>root. 0 \<le> weight root"
    and datum_nonnegative: "\<And>root output. 0 \<le> datum root output"
    and weight_integrable: "integrable lborel weight"
    and datum_power_integrable:
      "\<And>root. integrable lborel (\<lambda>output. datum root output powr a)"
    and datum_power_bound:
      "\<And>root. integral\<^sup>L lborel
        (\<lambda>output. datum root output powr a) \<le> L"
    and L_nonnegative: "0 \<le> L"
  shows joint_integrable:
    "integrable (lborel \<Otimes>\<^sub>M lborel)
      (\<lambda>(output, root). weight root * datum root output powr a)"
    and fiber_integrable_AE:
    "AE output in lborel.
      integrable lborel
        (\<lambda>root. weight root * datum root output powr a)"
    and source_integrable:
    "integrable lborel
      (\<lambda>output. integral\<^sup>L lborel
        (\<lambda>root. weight root * datum root output powr a))"
    and source_bound:
    "integral\<^sup>L lborel
        (\<lambda>output. integral\<^sup>L lborel
          (\<lambda>root. weight root * datum root output powr a))
      \<le> L * integral\<^sup>L lborel weight"
proof -
  note [measurable] = weight_measurable datum_joint_measurable
  let ?F = "\<lambda>(output, root). weight root * datum root output powr a"
  let ?N = "\<lambda>(output, root). ennreal (norm (?F (output, root)))"
  have F_measurable:
      "?F \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by measurable
  have N_measurable:
      "?N \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using F_measurable by measurable
  have weight_nn_finite:
      "(\<integral>\<^sup>+ root. weight root \<partial>lborel) < top"
    using weight_integrable
    unfolding integrable_iff_bounded
    by (simp add: weight_nonnegative)
  have power_nn:
      "(\<integral>\<^sup>+ output. datum root output powr a \<partial>lborel) =
        ennreal (integral\<^sup>L lborel
          (\<lambda>output. datum root output powr a))"
    for root
    by (rule nn_integral_eq_integral[OF datum_power_integrable]) simp
  have power_nn_bound:
      "(\<integral>\<^sup>+ output. datum root output powr a \<partial>lborel) \<le>
        ennreal L"
    for root
    unfolding power_nn
    by (rule ennreal_leI) (rule datum_power_bound)
  have inner_formula:
      "(\<integral>\<^sup>+ output. ?N (output, root) \<partial>lborel) =
        ennreal (weight root) *
          (\<integral>\<^sup>+ output. datum root output powr a \<partial>lborel)"
    for root
  proof -
    have power_measurable:
        "(\<lambda>output. ennreal (datum root output powr a))
          \<in> borel_measurable lborel"
      by measurable
    have factor:
        "(\<integral>\<^sup>+ output.
            ennreal (weight root) * ennreal (datum root output powr a)
            \<partial>lborel) =
          ennreal (weight root) *
            (\<integral>\<^sup>+ output. datum root output powr a \<partial>lborel)"
      by (rule nn_integral_cmult[OF power_measurable])
    have integrand_eq:
        "?N (out, root) =
          ennreal (weight root) * ennreal (datum root out powr a)"
      for out
      by (simp add: weight_nonnegative datum_nonnegative ennreal_mult)
    have first:
        "(\<integral>\<^sup>+ output. ?N (output, root) \<partial>lborel) =
          (\<integral>\<^sup>+ output.
            ennreal (weight root) * ennreal (datum root output powr a)
            \<partial>lborel)"
      by (rule nn_integral_cong) (rule integrand_eq)
    show ?thesis using first factor by simp
  qed
  have inner_bound:
      "(\<integral>\<^sup>+ output. ?N (output, root) \<partial>lborel) \<le>
        ennreal (weight root) * ennreal L"
    for root
    unfolding inner_formula
    by (rule mult_left_mono[OF power_nn_bound]) simp
  have outer_bound:
      "(\<integral>\<^sup>+ root. \<integral>\<^sup>+ output.
          ?N (output, root) \<partial>lborel \<partial>lborel) \<le>
        ennreal L * (\<integral>\<^sup>+ root. weight root \<partial>lborel)"
  proof -
    have mono:
        "(\<integral>\<^sup>+ root. \<integral>\<^sup>+ output.
            ?N (output, root) \<partial>lborel \<partial>lborel) \<le>
          (\<integral>\<^sup>+ root. ennreal (weight root) * ennreal L
            \<partial>lborel)"
      by (rule nn_integral_mono) (rule inner_bound)
    have factor:
        "(\<integral>\<^sup>+ root. ennreal L * ennreal (weight root)
            \<partial>lborel) =
          ennreal L * (\<integral>\<^sup>+ root. weight root \<partial>lborel)"
      by (rule nn_integral_cmult) measurable
    show ?thesis using mono factor by (simp add: mult.commute)
  qed
  have outer_finite:
      "(\<integral>\<^sup>+ root. \<integral>\<^sup>+ output.
          ?N (output, root) \<partial>lborel \<partial>lborel) < top"
  proof (rule le_less_trans[OF outer_bound])
    show "ennreal L *
        (\<integral>\<^sup>+ root. weight root \<partial>lborel) < top"
      using weight_nn_finite by (simp add: ennreal_mult_less_top)
  qed
  have product_formula:
      "integral\<^sup>N (lborel \<Otimes>\<^sub>M lborel) ?N =
        (\<integral>\<^sup>+ root. \<integral>\<^sup>+ output.
          ?N (output, root) \<partial>lborel \<partial>lborel)"
    using lborel_pair.nn_integral_snd[OF N_measurable] by simp
  have product_finite:
      "integral\<^sup>N (lborel \<Otimes>\<^sub>M lborel) ?N < top"
    using product_formula outer_finite by simp
  have F_integrable:
      "integrable (lborel \<Otimes>\<^sub>M lborel) ?F"
    unfolding integrable_iff_bounded
  proof (intro conjI)
    show "?F \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
      by (rule F_measurable)
    show "integral\<^sup>N (lborel \<Otimes>\<^sub>M lborel)
        (\<lambda>x. ennreal (norm (?F x))) < \<infinity>"
    proof -
      have norm_N: "(\<lambda>x. ennreal (norm (?F x))) = ?N"
        by (rule ext) (case_tac x, simp)
      show ?thesis using product_finite unfolding norm_N by simp
    qed
  qed
  have source_product:
      "integral\<^sup>L lborel
          (\<lambda>output. integral\<^sup>L lborel
            (\<lambda>root. weight root * datum root output powr a)) =
        integral\<^sup>L (lborel \<Otimes>\<^sub>M lborel) ?F"
    using lborel_pair.integral_fst[
      where f="\<lambda>output root. weight root * datum root output powr a",
      OF F_integrable]
    by simp
  have root_product:
      "integral\<^sup>L lborel
          (\<lambda>root. integral\<^sup>L lborel
            (\<lambda>output. weight root * datum root output powr a)) =
        integral\<^sup>L (lborel \<Otimes>\<^sub>M lborel) ?F"
    using lborel_pair.integral_snd[
      where f="\<lambda>output root. weight root * datum root output powr a",
      OF F_integrable]
    by simp
  have inner_real_bound:
      "integral\<^sup>L lborel
          (\<lambda>output. weight root * datum root output powr a)
        \<le> weight root * L"
    for root
  proof -
    have factor:
        "integral\<^sup>L lborel
            (\<lambda>output. weight root * datum root output powr a) =
          weight root * integral\<^sup>L lborel
            (\<lambda>output. datum root output powr a)"
      using datum_power_integrable[of root] by simp
    show ?thesis
      unfolding factor
      by (rule mult_left_mono[OF datum_power_bound weight_nonnegative])
  qed
  have root_outer_integrable:
      "integrable lborel
        (\<lambda>root. integral\<^sup>L lborel
          (\<lambda>output. weight root * datum root output powr a))"
    using lborel_pair.integrable_snd[OF F_integrable] by simp
  have majorant_integrable:
      "integrable lborel (\<lambda>root. weight root * L)"
    using weight_integrable by simp
  have root_outer_bound:
      "integral\<^sup>L lborel
          (\<lambda>root. integral\<^sup>L lborel
            (\<lambda>output. weight root * datum root output powr a)) \<le>
        integral\<^sup>L lborel (\<lambda>root. weight root * L)"
    by (rule integral_mono[OF root_outer_integrable majorant_integrable
          inner_real_bound])
  show joint_integrable:
      "integrable (lborel \<Otimes>\<^sub>M lborel) ?F"
    by (rule F_integrable)
  show fiber_integrable_AE:
      "AE output in lborel. integrable lborel
        (\<lambda>root. weight root * datum root output powr a)"
    using lborel_pair.AE_integrable_fst[OF F_integrable] by simp
  show source_integrable:
      "integrable lborel
        (\<lambda>output. integral\<^sup>L lborel
          (\<lambda>root. weight root * datum root output powr a))"
    using lborel_pair.integrable_fst[OF F_integrable] by simp
  show source_bound:
      "integral\<^sup>L lborel
          (\<lambda>output. integral\<^sup>L lborel
            (\<lambda>root. weight root * datum root output powr a))
        \<le> L * integral\<^sup>L lborel weight"
  proof -
    have source_root:
        "integral\<^sup>L lborel
            (\<lambda>output. integral\<^sup>L lborel
              (\<lambda>root. weight root * datum root output powr a)) =
          integral\<^sup>L lborel
            (\<lambda>root. integral\<^sup>L lborel
              (\<lambda>output. weight root * datum root output powr a))"
      using source_product root_product by simp
    have rhs_factor:
        "integral\<^sup>L lborel (\<lambda>root. weight root * L) =
          L * integral\<^sup>L lborel weight"
      using weight_integrable by (simp add: mult.commute)
    show ?thesis using root_outer_bound
      by (simp only: source_root rhs_factor)
  qed
qed

end
