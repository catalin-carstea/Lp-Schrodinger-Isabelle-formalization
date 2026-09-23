theory Inverse_Schrodinger_Lp_Weighted_Joint_Integrable_Pair
  imports Inverse_Schrodinger_Lp_Born_Block_Real_Integrable
begin

section \<open>Joint integrability from a uniform weighted power bound\<close>

lemma slp_weighted_joint_integrable_pair:
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
  shows joint_integrable:
    "integrable
      ((lborel :: slp_point measure) \<Otimes>\<^sub>M
        (lborel :: (slp_point \<times> slp_point) measure))
      (\<lambda>(output, pair). weight pair * datum pair output powr a)"
    and fiber_integrable_AE:
    "AE output in lborel.
      integrable lborel
        (\<lambda>pair. weight pair * datum pair output powr a)"
    and source_integrable:
    "integrable lborel
      (\<lambda>output. integral\<^sup>L lborel
        (\<lambda>pair. weight pair * datum pair output powr a))"
proof -
  note [measurable] = weight_measurable datum_joint_measurable
  let ?F = "\<lambda>(output, pair). weight pair * datum pair output powr a"
  let ?N = "\<lambda>(output, pair). ennreal (norm (?F (output, pair)))"
  have F_measurable:
      "?F \<in> borel_measurable
        ((lborel :: slp_point measure) \<Otimes>\<^sub>M
          (lborel :: (slp_point \<times> slp_point) measure))"
    by measurable
  have N_measurable:
      "?N \<in> borel_measurable
        ((lborel :: slp_point measure) \<Otimes>\<^sub>M
          (lborel :: (slp_point \<times> slp_point) measure))"
    using F_measurable by measurable
  have weight_nn_finite:
      "(\<integral>\<^sup>+ pair. weight pair \<partial>lborel) < top"
    using weight_integrable
    unfolding integrable_iff_bounded
    by (simp add: weight_nonnegative)
  have power_nn:
      "(\<integral>\<^sup>+ output. datum pair output powr a \<partial>lborel) =
        ennreal
          (integral\<^sup>L lborel (\<lambda>output. datum pair output powr a))"
    for pair
    by (rule nn_integral_eq_integral[OF datum_power_integrable]) simp
  have power_nn_bound:
      "(\<integral>\<^sup>+ output. datum pair output powr a \<partial>lborel) \<le>
        ennreal L"
    for pair
    unfolding power_nn
    by (rule ennreal_leI) (rule datum_power_bound)
  have inner_formula:
      "(\<integral>\<^sup>+ output. ?N (output, pair) \<partial>lborel) =
        ennreal (weight pair) *
          (\<integral>\<^sup>+ output. datum pair output powr a \<partial>lborel)"
    for pair
  proof -
    have power_measurable:
        "(\<lambda>output. ennreal (datum pair output powr a))
          \<in> borel_measurable lborel"
      by measurable
    have factor:
        "(\<integral>\<^sup>+ output.
            ennreal (weight pair) * ennreal (datum pair output powr a)
            \<partial>lborel) =
          ennreal (weight pair) *
            (\<integral>\<^sup>+ output. datum pair output powr a \<partial>lborel)"
      by (rule nn_integral_cmult[OF power_measurable])
  have integrand_eq:
      "?N (out, pair) =
        ennreal (weight pair) * ennreal (datum pair out powr a)"
    for out
      by (simp add: weight_nonnegative datum_nonnegative ennreal_mult)
    have first:
      "(\<integral>\<^sup>+ output. ?N (output, pair) \<partial>lborel) =
        (\<integral>\<^sup>+ output.
          ennreal (weight pair) * ennreal (datum pair output powr a)
          \<partial>lborel)"
      by (rule nn_integral_cong) (rule integrand_eq)
    show ?thesis
      using first factor by simp
  qed
  have inner_bound:
      "(\<integral>\<^sup>+ output. ?N (output, pair) \<partial>lborel) \<le>
        ennreal (weight pair) * ennreal L"
    for pair
    unfolding inner_formula
    by (rule mult_left_mono[OF power_nn_bound]) simp
  have outer_bound:
      "(\<integral>\<^sup>+ pair. \<integral>\<^sup>+ output.
          ?N (output, pair) \<partial>lborel \<partial>lborel) \<le>
        ennreal L * (\<integral>\<^sup>+ pair. weight pair \<partial>lborel)"
  proof -
    have mono:
        "(\<integral>\<^sup>+ pair. \<integral>\<^sup>+ output.
            ?N (output, pair) \<partial>lborel \<partial>lborel) \<le>
          (\<integral>\<^sup>+ pair. ennreal (weight pair) * ennreal L
            \<partial>lborel)"
      by (rule nn_integral_mono) (rule inner_bound)
    have factor:
        "(\<integral>\<^sup>+ pair. ennreal L * ennreal (weight pair)
            \<partial>lborel) =
          ennreal L * (\<integral>\<^sup>+ pair. weight pair \<partial>lborel)"
      by (rule nn_integral_cmult) measurable
    show ?thesis
      using mono factor by (simp add: mult.commute)
  qed
  have outer_finite:
      "(\<integral>\<^sup>+ pair. \<integral>\<^sup>+ output.
          ?N (output, pair) \<partial>lborel \<partial>lborel) < top"
  proof (rule le_less_trans[OF outer_bound])
    show
      "ennreal L * (\<integral>\<^sup>+ pair. weight pair \<partial>lborel) < top"
      using weight_nn_finite by (simp add: ennreal_mult_less_top)
  qed
  have product_formula:
      "integral\<^sup>N
          ((lborel :: slp_point measure) \<Otimes>\<^sub>M
            (lborel :: (slp_point \<times> slp_point) measure)) ?N =
        (\<integral>\<^sup>+ pair. \<integral>\<^sup>+ output.
          ?N (output, pair) \<partial>lborel \<partial>lborel)"
    using lborel_pair.nn_integral_snd[OF N_measurable] by simp
  have product_finite:
      "integral\<^sup>N
          ((lborel :: slp_point measure) \<Otimes>\<^sub>M
            (lborel :: (slp_point \<times> slp_point) measure)) ?N < top"
    using product_formula outer_finite by simp
  have F_integrable:
      "integrable
        ((lborel :: slp_point measure) \<Otimes>\<^sub>M
          (lborel :: (slp_point \<times> slp_point) measure)) ?F"
    unfolding integrable_iff_bounded
  proof (intro conjI)
    show
      "?F \<in> borel_measurable
        ((lborel :: slp_point measure) \<Otimes>\<^sub>M
          (lborel :: (slp_point \<times> slp_point) measure))"
      by (rule F_measurable)
    show
      "integral\<^sup>N
        ((lborel :: slp_point measure) \<Otimes>\<^sub>M
          (lborel :: (slp_point \<times> slp_point) measure))
        (\<lambda>x. ennreal (norm (?F x))) < \<infinity>"
    proof -
      have norm_N:
          "(\<lambda>x. ennreal (norm (?F x))) = ?N"
        by (rule ext) (case_tac x, simp)
      show ?thesis
        using product_finite unfolding norm_N by simp
    qed
  qed
  show joint_integrable: "integrable
      ((lborel :: slp_point measure) \<Otimes>\<^sub>M
        (lborel :: (slp_point \<times> slp_point) measure)) ?F"
    by (rule F_integrable)
  show fiber_integrable_AE:
      "AE output in lborel.
        integrable lborel
          (\<lambda>pair. weight pair * datum pair output powr a)"
    using lborel_pair.AE_integrable_fst[OF F_integrable] by simp
  show source_integrable:
      "integrable lborel
        (\<lambda>output. integral\<^sup>L lborel
          (\<lambda>pair. weight pair * datum pair output powr a))"
    using lborel_pair.integrable_fst[OF F_integrable] by simp
qed

end
