theory Inverse_Schrodinger_Lp_Born_Block_Real_Representatives
  imports
    Inverse_Schrodinger_Lp_Integral_Affine_Output_Power_Transport
    Inverse_Schrodinger_Lp_Born_Block_Mass_Endpoint
begin

section \<open>Real representatives of positive Born blocks\<close>

definition slp_positive_branch_block_weight_real ::
    "real \<Rightarrow> (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow> slp_point \<Rightarrow>
      (slp_point \<times> slp_point) \<Rightarrow> real"
where
  "slp_positive_branch_block_weight_real R cutoff potential origin pair =
    enn2real
      (slp_positive_branch_block_weight R cutoff potential origin
        (fst pair) (snd pair))"

definition slp_positive_branch_block_datum_real ::
    "real \<Rightarrow> (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> ennreal) \<Rightarrow> nat \<Rightarrow>
      (slp_point \<times> slp_point) \<Rightarrow> slp_point \<Rightarrow> real"
where
  "slp_positive_branch_block_datum_real R cutoff potential terminal_weight n
      pair output =
    enn2real
      (slp_positive_output_density R cutoff potential terminal_weight n
        (snd pair) (output - fst pair + snd pair))"

lemma slp_AE_translate:
  fixes P :: "slp_point \<Rightarrow> bool"
  assumes P_measurable: "Measurable.pred lborel P"
    and P_AE: "AE x in lborel. P x"
  shows "AE x in lborel. P (shift + x)"
proof -
  have shift_measurable: "(+) shift \<in> measurable lborel borel"
    by measurable
  have P_borel_measurable: "Measurable.pred borel P"
    using P_measurable by simp
  have P_borel_set: "{x \<in> space borel. P x} \<in> sets borel"
    using P_borel_measurable by simp
  have P_distr: "AE x in distr lborel borel ((+) shift). P x"
    using P_AE by (simp only: lborel_distr_plus)
  show ?thesis
    using AE_distr_iff[OF shift_measurable P_borel_set] P_distr
    by blast
qed

lemma slp_positive_branch_block_weight_real_measurable:
  assumes cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
  shows
    "slp_positive_branch_block_weight_real R cutoff potential origin
      \<in> borel_measurable lborel"
proof -
  have block_measurable:
      "case_prod
          (slp_positive_branch_block_weight R cutoff potential origin)
        \<in> borel_measurable
          ((lborel :: slp_point measure) \<Otimes>\<^sub>M
            (lborel :: slp_point measure))"
    by (rule slp_positive_branch_block_weight_measurable[
          OF cutoff_measurable potential_measurable])
  have paired_measurable:
      "(\<lambda>pair.
          slp_positive_branch_block_weight R cutoff potential origin
            (fst pair) (snd pair))
        \<in> borel_measurable
          (lborel :: (slp_point \<times> slp_point) measure)"
  proof -
    have paired_eq:
        "(\<lambda>pair.
            slp_positive_branch_block_weight R cutoff potential origin
              (fst pair) (snd pair)) =
          case_prod
            (slp_positive_branch_block_weight R cutoff potential origin)"
      by (rule ext) (simp split: prod.splits)
    show ?thesis
      unfolding paired_eq
      using block_measurable by (simp only: lborel_prod)
  qed
  show ?thesis
    unfolding slp_positive_branch_block_weight_real_def
    using paired_measurable by measurable
qed

lemma slp_positive_branch_block_datum_real_joint_measurable:
  assumes cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
    and terminal_weight_measurable:
      "terminal_weight \<in> borel_measurable lborel"
  shows
    "case_prod
      (slp_positive_branch_block_datum_real R cutoff potential terminal_weight n)
      \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
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
  have pulled_density_measurable:
      "(\<lambda>pair_output.
          slp_positive_output_density R cutoff potential terminal_weight n
            (snd (fst pair_output))
            (snd pair_output - fst (fst pair_output) + snd (fst pair_output)))
        \<in> borel_measurable
          ((lborel :: (slp_point \<times> slp_point) measure) \<Otimes>\<^sub>M
            (lborel :: slp_point measure))"
    using measurable_compose[OF input_measurable density_measurable] by simp
  show ?thesis
    unfolding slp_positive_branch_block_datum_real_def
    using pulled_density_measurable by measurable
qed

lemma slp_positive_branch_block_weight_real_nonnegative:
  "0 \<le> slp_positive_branch_block_weight_real R cutoff potential origin pair"
  unfolding slp_positive_branch_block_weight_real_def by simp

lemma slp_positive_branch_block_datum_real_nonnegative:
  "0 \<le> slp_positive_branch_block_datum_real R cutoff potential
    terminal_weight n pair output"
  unfolding slp_positive_branch_block_datum_real_def by simp

lemma slp_positive_branch_block_weight_real_lift:
  "ennreal
      (slp_positive_branch_block_weight_real R cutoff potential origin pair) =
    slp_positive_branch_block_weight R cutoff potential origin
      (fst pair) (snd pair)"
  unfolding slp_positive_branch_block_weight_real_def
    slp_positive_branch_block_weight_def
  by (simp add: ennreal_mult_less_top)

lemma slp_positive_branch_block_datum_real_lift_AE:
  assumes density_lp:
    "\<And>origin. slp_positive_ennreal_lp_on_plane a
      (slp_positive_output_density R cutoff potential terminal_weight n
        origin)"
  shows
    "AE output in lborel.
      ennreal
        (slp_positive_branch_block_datum_real R cutoff potential
          terminal_weight n pair output) =
      slp_positive_output_density R cutoff potential terminal_weight n
        (snd pair) (output - fst pair + snd pair)"
proof -
  let ?density =
    "slp_positive_output_density R cutoff potential terminal_weight n
      (snd pair)"
  have density_measurable: "?density \<in> borel_measurable lborel"
    and density_finite: "AE x in lborel. ?density x < top"
    using density_lp[of "snd pair"]
    unfolding slp_positive_ennreal_lp_on_plane_def by blast+
  have finite_predicate:
      "Measurable.pred lborel (\<lambda>x. ?density x < top)"
    using density_measurable by measurable
  have translated_finite:
      "AE output in lborel.
        ?density ((- fst pair + snd pair) + output) < top"
    by (rule slp_AE_translate[OF finite_predicate density_finite])
  show ?thesis
    using translated_finite
  proof eventually_elim
    fix out :: slp_point
    assume finite:
      "?density ((- fst pair + snd pair) + out) < top"
    show
      "ennreal
          (slp_positive_branch_block_datum_real R cutoff potential
            terminal_weight n pair out) =
        ?density (out - fst pair + snd pair)"
      using finite
      unfolding slp_positive_branch_block_datum_real_def
      by (simp add: algebra_simps)
  qed
qed

end
