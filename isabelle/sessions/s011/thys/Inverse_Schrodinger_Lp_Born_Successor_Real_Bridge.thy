theory Inverse_Schrodinger_Lp_Born_Successor_Real_Bridge
  imports Inverse_Schrodinger_Lp_Born_Block_Finite_Power
begin

section \<open>Almost-everywhere bridge to the exact successor density\<close>

context aim_planar_riesz_hls
begin

lemma slp_positive_output_density_Suc_real_bridge_AE:
  fixes R C p a b L :: real
    and cutoff potential :: "slp_point \<Rightarrow> complex"
    and terminal_weight :: "slp_point \<Rightarrow> ennreal"
    and origin :: slp_point
    and n :: nat
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and a_lower: "1 < a"
    and b_lower: "1 < b"
    and conjugate: "1 / a + 1 / b = 1"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and terminal_weight_measurable:
      "terminal_weight \<in> borel_measurable lborel"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and density_lp:
      "\<And>inner_origin. slp_positive_ennreal_lp_on_plane a
        (slp_positive_output_density R cutoff potential terminal_weight n
          inner_origin)"
    and density_power_bound:
      "\<And>inner_origin.
        integral\<^sup>L lborel
          (\<lambda>inner_output.
            enn2real
              (slp_positive_output_density R cutoff potential terminal_weight n
                inner_origin inner_output) powr a) \<le> L"
    and L_nonnegative: "0 \<le> L"
  shows
    "AE output in lborel.
      slp_positive_output_density R cutoff potential terminal_weight (Suc n)
          origin output =
        ennreal (inverse (pi ^ 2)) *
          ennreal
            (integral\<^sup>L lborel
              (\<lambda>pair.
                slp_positive_branch_block_weight_real R cutoff potential origin
                  pair *
                slp_positive_branch_block_datum_real R cutoff potential
                  terminal_weight n pair output))"
proof -
  let ?weight =
    "slp_positive_branch_block_weight_real R cutoff potential origin"
  let ?datum =
    "slp_positive_branch_block_datum_real R cutoff potential terminal_weight n"
  let ?extended =
    "\<lambda>output pair.
      slp_positive_branch_block_weight R cutoff potential origin
        (fst pair) (snd pair) *
      slp_positive_output_density R cutoff potential terminal_weight n
        (snd pair) (output - fst pair + snd pair)"
  have potential_measurable:
      "potential \<in> borel_measurable lborel"
    using potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have weight_measurable: "?weight \<in> borel_measurable lborel"
    by (rule slp_positive_branch_block_weight_real_measurable[OF
          cutoff_measurable potential_measurable])
  have datum_joint_measurable:
      "case_prod ?datum \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_positive_branch_block_datum_real_joint_measurable[OF
          cutoff_measurable potential_measurable
          terminal_weight_measurable])
  note [measurable] = weight_measurable datum_joint_measurable
  have weight_integrable: "integrable lborel ?weight"
    by (rule slp_positive_branch_block_weight_real_integrable[OF
          radius_nonnegative p_lower p_upper cutoff_measurable
          potential_lp cutoff_bound])
  have weight_nonnegative: "0 \<le> ?weight pair" for pair
    by (rule slp_positive_branch_block_weight_real_nonnegative)
  have datum_nonnegative: "0 \<le> ?datum pair out" for pair out
    by (rule slp_positive_branch_block_datum_real_nonnegative)
  have datum_power_integrable:
      "integrable lborel (\<lambda>output. ?datum pair output powr a)"
    for pair
    by (rule slp_positive_branch_block_datum_real_power_integrable[OF density_lp])
  have datum_power_bound:
      "integral\<^sup>L lborel (\<lambda>output. ?datum pair output powr a)
        \<le> L"
    for pair
  proof -
    have inner_integrable:
        "integrable lborel
          (\<lambda>inner_output.
            enn2real
              (slp_positive_output_density R cutoff potential terminal_weight n
                (snd pair) inner_output) powr a)"
      using density_lp[of "snd pair"]
      unfolding slp_positive_ennreal_lp_on_plane_def by blast
    have translated:
        "integral\<^sup>L lborel
            (\<lambda>output.
              enn2real
                (slp_positive_output_density R cutoff potential terminal_weight n
                  (snd pair) ((- fst pair + snd pair) + output)) powr a) =
          integral\<^sup>L lborel
            (\<lambda>inner_output.
              enn2real
                (slp_positive_output_density R cutoff potential terminal_weight n
                  (snd pair) inner_output) powr a)"
      by (rule slp_lborel_integral_translate[OF inner_integrable])
    have exact_translate:
        "integral\<^sup>L lborel (\<lambda>output. ?datum pair output powr a) =
          integral\<^sup>L lborel
            (\<lambda>inner_output.
              enn2real
                (slp_positive_output_density R cutoff potential terminal_weight n
                  (snd pair) inner_output) powr a)"
      using translated
      unfolding slp_positive_branch_block_datum_real_def
      by (simp add: algebra_simps)
    show ?thesis
      unfolding exact_translate by (rule density_power_bound)
  qed
  have joint_power_integrable:
      "integrable
        ((lborel :: slp_point measure) \<Otimes>\<^sub>M
          (lborel :: (slp_point \<times> slp_point) measure))
        (\<lambda>(output, pair). ?weight pair * ?datum pair output powr a)"
    by (rule slp_weighted_joint_integrable_pair(1)[OF
          weight_measurable datum_joint_measurable weight_nonnegative
          datum_nonnegative weight_integrable datum_power_integrable
          datum_power_bound L_nonnegative])
  have fiber_power_integrable_AE:
      "AE output in lborel.
        integrable lborel
          (\<lambda>pair. ?weight pair * ?datum pair output powr a)"
    using lborel_pair.AE_integrable_fst[OF joint_power_integrable] by simp
  have fiber_integrable_AE:
      "AE output in lborel.
        integrable lborel (\<lambda>pair. ?weight pair * ?datum pair output)"
    using fiber_power_integrable_AE
  proof eventually_elim
    fix out :: slp_point
    assume power_integrable:
      "integrable lborel (\<lambda>pair. ?weight pair * ?datum pair out powr a)"
    have datum_section_measurable:
        "(\<lambda>pair. ?datum pair out) \<in> borel_measurable lborel"
      by measurable
    show "integrable lborel (\<lambda>pair. ?weight pair * ?datum pair out)"
      by (rule slp_weighted_holder_power(1)[OF
            a_lower b_lower conjugate weight_measurable
            datum_section_measurable weight_nonnegative _ weight_integrable
            power_integrable])
        (rule datum_nonnegative)
  qed
  have datum_lift_pair_output:
      "AE pair in lborel. AE output in lborel.
        ennreal (?datum pair output) =
          slp_positive_output_density R cutoff potential terminal_weight n
            (snd pair) (output - fst pair + snd pair)"
  proof (rule AE_I2)
    fix pair :: "slp_point \<times> slp_point"
    show "AE output in lborel.
        ennreal (?datum pair output) =
          slp_positive_output_density R cutoff potential terminal_weight n
            (snd pair) (output - fst pair + snd pair)"
      by (rule slp_positive_branch_block_datum_real_lift_AE[OF density_lp])
  qed
  have lift_left_measurable:
      "(\<lambda>pair_output.
          ennreal (?datum (fst pair_output) (snd pair_output)))
        \<in> borel_measurable
        ((lborel :: (slp_point \<times> slp_point) measure) \<Otimes>\<^sub>M
          (lborel :: slp_point measure))"
    by measurable
  have lift_right_measurable:
      "(\<lambda>pair_output.
          slp_positive_output_density R cutoff potential terminal_weight n
            (snd (fst pair_output))
            (snd pair_output - fst (fst pair_output) + snd (fst pair_output)))
        \<in> borel_measurable
        ((lborel :: (slp_point \<times> slp_point) measure) \<Otimes>\<^sub>M
          (lborel :: slp_point measure))"
  proof -
    have density_measurable:
        "case_prod
            (slp_positive_output_density R cutoff potential terminal_weight n)
          \<in> borel_measurable
            ((lborel :: slp_point measure) \<Otimes>\<^sub>M
              (lborel :: slp_point measure))"
      by (rule slp_positive_output_density_joint_measurable[
            OF cutoff_measurable potential_measurable
              terminal_weight_measurable])
    have input_measurable:
        "(\<lambda>pair_output.
            (snd (fst pair_output),
              snd pair_output - fst (fst pair_output) + snd (fst pair_output)))
          \<in> measurable
            ((lborel :: (slp_point \<times> slp_point) measure) \<Otimes>\<^sub>M
              (lborel :: slp_point measure))
            ((lborel :: slp_point measure) \<Otimes>\<^sub>M
              (lborel :: slp_point measure))"
    proof -
      have identity_continuous:
          "continuous_on UNIV
            (\<lambda>x :: (slp_point \<times> slp_point) \<times> slp_point. x)"
        by (rule continuous_on_id)
      have outer_fst_continuous:
          "continuous_on UNIV
            (\<lambda>x :: (slp_point \<times> slp_point) \<times> slp_point. fst x)"
        by (rule continuous_on_fst[OF identity_continuous])
      have outer_snd_continuous:
          "continuous_on UNIV
            (\<lambda>x :: (slp_point \<times> slp_point) \<times> slp_point. snd x)"
        by (rule continuous_on_snd[OF identity_continuous])
      have pos_continuous:
          "continuous_on UNIV
            (\<lambda>x :: (slp_point \<times> slp_point) \<times> slp_point.
              fst (fst x))"
        by (rule continuous_on_fst[OF outer_fst_continuous])
      have neg_continuous:
          "continuous_on UNIV
            (\<lambda>x :: (slp_point \<times> slp_point) \<times> slp_point.
              snd (fst x))"
        by (rule continuous_on_snd[OF outer_fst_continuous])
      have shifted_continuous:
          "continuous_on UNIV
            (\<lambda>x :: (slp_point \<times> slp_point) \<times> slp_point.
              snd x - fst (fst x) + snd (fst x))"
        by (rule continuous_on_add[OF
              continuous_on_diff[OF outer_snd_continuous pos_continuous]
              neg_continuous])
      have neg_measurable:
          "(\<lambda>x :: (slp_point \<times> slp_point) \<times> slp_point.
              snd (fst x))
            \<in> borel_measurable
              (lborel :: ((slp_point \<times> slp_point) \<times> slp_point) measure)"
        using borel_measurable_continuous_onI[OF neg_continuous] by simp
      have shifted_measurable:
          "(\<lambda>x :: (slp_point \<times> slp_point) \<times> slp_point.
              snd x - fst (fst x) + snd (fst x))
            \<in> borel_measurable
              (lborel :: ((slp_point \<times> slp_point) \<times> slp_point) measure)"
        using borel_measurable_continuous_onI[OF shifted_continuous] by simp
      have neg_measurable_lborel:
          "(\<lambda>x :: (slp_point \<times> slp_point) \<times> slp_point.
              snd (fst x))
            \<in> measurable
              (lborel :: ((slp_point \<times> slp_point) \<times> slp_point) measure)
              (lborel :: slp_point measure)"
        using neg_measurable by simp
      have shifted_measurable_lborel:
          "(\<lambda>x :: (slp_point \<times> slp_point) \<times> slp_point.
              snd x - fst (fst x) + snd (fst x))
            \<in> measurable
              (lborel :: ((slp_point \<times> slp_point) \<times> slp_point) measure)
              (lborel :: slp_point measure)"
        using shifted_measurable by simp
      have product_measurable:
          "(\<lambda>pair_output.
              (snd (fst pair_output),
                snd pair_output - fst (fst pair_output) + snd (fst pair_output)))
            \<in> measurable
              (lborel :: ((slp_point \<times> slp_point) \<times> slp_point) measure)
              ((lborel :: slp_point measure) \<Otimes>\<^sub>M
                (lborel :: slp_point measure))"
        by (rule measurable_Pair[OF
              neg_measurable_lborel shifted_measurable_lborel])
      have plain_measurable:
          "(\<lambda>pair_output.
              (snd (fst pair_output),
                snd pair_output - fst (fst pair_output) + snd (fst pair_output)))
            \<in> measurable
              (lborel :: ((slp_point \<times> slp_point) \<times> slp_point) measure)
              (lborel :: (slp_point \<times> slp_point) measure)"
        using product_measurable by (simp only: lborel_prod)
      show ?thesis
        using plain_measurable by (simp only: lborel_prod)
    qed
    show ?thesis
      using measurable_compose[OF input_measurable density_measurable] by simp
  qed
  have lift_predicate_set:
      "{pair_output \<in> space
          ((lborel :: (slp_point \<times> slp_point) measure) \<Otimes>\<^sub>M
            (lborel :: slp_point measure)).
        ennreal (?datum (fst pair_output) (snd pair_output)) =
          slp_positive_output_density R cutoff potential terminal_weight n
            (snd (fst pair_output))
            (snd pair_output - fst (fst pair_output) + snd (fst pair_output))}
        \<in> sets
          ((lborel :: (slp_point \<times> slp_point) measure) \<Otimes>\<^sub>M
            (lborel :: slp_point measure))"
    by (rule measurable_equality_set[OF
          lift_left_measurable lift_right_measurable])
  have datum_lift_output_pair:
      "AE output in lborel. AE pair in lborel.
        ennreal (?datum pair output) =
          slp_positive_output_density R cutoff potential terminal_weight n
            (snd pair) (output - fst pair + snd pair)"
    using datum_lift_pair_output
      lborel_pair.AE_commute[OF lift_predicate_set]
    by blast
  show ?thesis
    using fiber_integrable_AE datum_lift_output_pair
  proof eventually_elim
    fix out :: slp_point
    assume fiber_integrable:
      "integrable lborel (\<lambda>pair. ?weight pair * ?datum pair out)"
      and datum_lift:
      "AE pair in lborel.
        ennreal (?datum pair out) =
          slp_positive_output_density R cutoff potential terminal_weight n
            (snd pair) (out - fst pair + snd pair)"
    have integrand_lift:
        "AE pair in lborel.
          ennreal (?weight pair * ?datum pair out) = ?extended out pair"
      using datum_lift
    proof eventually_elim
      fix pair :: "slp_point \<times> slp_point"
      assume datum_eq:
        "ennreal (?datum pair out) =
          slp_positive_output_density R cutoff potential terminal_weight n
            (snd pair) (out - fst pair + snd pair)"
      show "ennreal (?weight pair * ?datum pair out) = ?extended out pair"
        using slp_positive_branch_block_weight_real_lift[of
          R cutoff potential origin pair] datum_eq
        by (simp add: ennreal_mult weight_nonnegative datum_nonnegative)
    qed
    have real_nn:
        "(\<integral>\<^sup>+ pair. ?weight pair * ?datum pair out \<partial>lborel) =
          ennreal (integral\<^sup>L lborel
            (\<lambda>pair. ?weight pair * ?datum pair out))"
      by (rule nn_integral_eq_integral[OF fiber_integrable])
        (rule AE_I2, simp add: weight_nonnegative datum_nonnegative)
    have extended_real:
        "(\<integral>\<^sup>+ pair. ?extended out pair \<partial>lborel) =
          ennreal (integral\<^sup>L lborel
            (\<lambda>pair. ?weight pair * ?datum pair out))"
    proof -
      have congruence:
          "(\<integral>\<^sup>+ pair. ?extended out pair \<partial>lborel) =
            (\<integral>\<^sup>+ pair. ?weight pair * ?datum pair out \<partial>lborel)"
        by (rule nn_integral_cong_AE)
          (use integrand_lift in \<open>eventually_elim, simp\<close>)
      show ?thesis using congruence real_nn by simp
    qed
    have pair_nested:
        "(\<integral>\<^sup>+ pair. ?extended out pair
            \<partial>(lborel :: (slp_point \<times> slp_point) measure)) =
          (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
            slp_positive_branch_block_weight R cutoff potential origin
              pos_point neg_point *
            slp_positive_output_density R cutoff potential terminal_weight n
              neg_point (out - pos_point + neg_point)
            \<partial>lborel \<partial>lborel)"
    proof -
      have block_measurable:
          "case_prod
              (slp_positive_branch_block_weight R cutoff potential origin)
            \<in> borel_measurable
              ((lborel :: slp_point measure) \<Otimes>\<^sub>M
                (lborel :: slp_point measure))"
        by (rule slp_positive_branch_block_weight_measurable[OF
              cutoff_measurable potential_measurable])
      have density_measurable:
          "case_prod
              (slp_positive_output_density R cutoff potential terminal_weight n)
            \<in> borel_measurable
              ((lborel :: slp_point measure) \<Otimes>\<^sub>M
                (lborel :: slp_point measure))"
        by (rule slp_positive_output_density_joint_measurable[OF
              cutoff_measurable potential_measurable
                terminal_weight_measurable])
      have extended_measurable:
          "?extended out \<in> borel_measurable
            ((lborel :: slp_point measure) \<Otimes>\<^sub>M
              (lborel :: slp_point measure))"
        using block_measurable density_measurable by measurable
      have product_nested:
          "(\<integral>\<^sup>+ pair. ?extended out pair
              \<partial>((lborel :: slp_point measure) \<Otimes>\<^sub>M
                (lborel :: slp_point measure))) =
            (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
              slp_positive_branch_block_weight R cutoff potential origin
                pos_point neg_point *
              slp_positive_output_density R cutoff potential terminal_weight n
                neg_point (out - pos_point + neg_point)
              \<partial>lborel \<partial>lborel)"
        using lborel.nn_integral_fst[OF extended_measurable] by simp
      show ?thesis
        using product_nested by (simp only: lborel_prod)
    qed
    have successor_identity:
        "slp_positive_output_density R cutoff potential terminal_weight (Suc n)
            origin out =
          ennreal (inverse (pi ^ 2)) *
            (\<integral>\<^sup>+ pair. ?extended out pair
              \<partial>(lborel :: (slp_point \<times> slp_point) measure))"
      using pair_nested
      by (simp only: slp_positive_output_density.simps
          slp_positive_branch_block_weight_def)
    show
      "slp_positive_output_density R cutoff potential terminal_weight (Suc n)
          origin out =
        ennreal (inverse (pi ^ 2)) *
          ennreal
            (integral\<^sup>L lborel
              (\<lambda>pair. ?weight pair * ?datum pair out))"
      using successor_identity extended_real by simp
  qed
qed

end

end
