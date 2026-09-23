theory Inverse_Schrodinger_Lp_Joint_Fiber_Geometric_Series
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Left_Neumann_Iterate_Joint_Measurable"
begin

hide_const (open) Commutative_Ring.norm

section \<open>From measurable fiber bounds to product-almost-everywhere bounds\<close>

theorem slp_joint_AE_from_measurable_fibers:
  fixes predicate :: "(slp_point \<times> slp_point) \<Rightarrow> bool"
  assumes predicate_measurable:
      "Measurable.pred (lborel \<Otimes>\<^sub>M lborel) predicate"
    and fiberwise:
      "AE center in lborel. AE output in lborel.
        predicate (center, output)"
  shows "AE pair in lborel \<Otimes>\<^sub>M lborel. predicate pair"
proof -
  have predicate_set:
      "{pair \<in> space (lborel \<Otimes>\<^sub>M lborel). predicate pair}
        \<in> sets (lborel \<Otimes>\<^sub>M lborel)"
    using predicate_measurable
    unfolding Measurable.pred_def .
  show ?thesis
    by (rule lborel_pair.AE_pair_measure[OF predicate_set fiberwise])
qed

theorem slp_joint_measurable_sequence_simultaneous_fiber_bounds:
  fixes U :: "nat \<Rightarrow> slp_point \<Rightarrow> slp_point \<Rightarrow> complex"
    and bound :: "nat \<Rightarrow> slp_point \<Rightarrow> real"
  assumes term_measurable:
      "\<And>j. (\<lambda>pair :: slp_point \<times> slp_point.
        U j (fst pair) (snd pair)) \<in>
          borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    and bound_measurable:
      "\<And>j. bound j \<in> borel_measurable lborel"
    and fiber_bounds:
      "\<And>j. AE center in lborel. AE output in lborel.
        norm (U j center output) \<le> bound j center"
  shows
    "AE pair in lborel \<Otimes>\<^sub>M lborel. \<forall>j.
      norm (U j (fst pair) (snd pair)) \<le> bound j (fst pair)"
proof -
  have each_product:
      "\<And>j. AE pair in lborel \<Otimes>\<^sub>M lborel.
        norm (U j (fst pair) (snd pair)) \<le> bound j (fst pair)"
  proof -
    fix j :: nat
    have predicate_measurable:
        "Measurable.pred (lborel \<Otimes>\<^sub>M lborel)
          (\<lambda>pair :: slp_point \<times> slp_point.
            norm (U j (fst pair) (snd pair)) \<le> bound j (fst pair))"
      using term_measurable[of j] bound_measurable[of j] by measurable
    show
        "AE pair in lborel \<Otimes>\<^sub>M lborel.
          norm (U j (fst pair) (snd pair)) \<le> bound j (fst pair)"
    proof (rule slp_joint_AE_from_measurable_fibers[
        where predicate="\<lambda>pair :: slp_point \<times> slp_point.
          norm (U j (fst pair) (snd pair)) \<le> bound j (fst pair)"])
      show
          "Measurable.pred (lborel \<Otimes>\<^sub>M lborel)
            (\<lambda>pair :: slp_point \<times> slp_point.
              norm (U j (fst pair) (snd pair)) \<le> bound j (fst pair))"
        by (rule predicate_measurable)
    next
      show
          "AE center in lborel. AE output in lborel.
            norm (U j (fst (center, output)) (snd (center, output))) \<le>
              bound j (fst (center, output))"
        using fiber_bounds[of j] by simp
    qed
  qed
  show ?thesis
    using each_product unfolding AE_all_countable by blast
qed

section \<open>Jointly measurable geometric pointwise sums\<close>

theorem slp_joint_measurable_geometric_series_from_fibers:
  fixes U :: "nat \<Rightarrow> slp_point \<Rightarrow> slp_point \<Rightarrow> complex"
    and majorant :: "slp_point \<Rightarrow> real"
    and rho :: real
  assumes term_measurable:
      "\<And>j. (\<lambda>pair :: slp_point \<times> slp_point.
        U j (fst pair) (snd pair)) \<in>
          borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    and majorant_measurable:
      "majorant \<in> borel_measurable lborel"
    and majorant_nonnegative: "\<And>center. 0 \<le> majorant center"
    and rho_nonnegative: "0 \<le> rho"
    and rho_strict: "rho < 1"
    and fiber_bounds:
      "\<And>j. AE center in lborel. AE output in lborel.
        norm (U j center output) \<le> majorant center * rho ^ j"
  shows simultaneous_bounds:
      "AE pair in lborel \<Otimes>\<^sub>M lborel. \<forall>j.
        norm (U j (fst pair) (snd pair)) \<le>
          majorant (fst pair) * rho ^ j"
    and sum_joint_measurable:
      "(\<lambda>pair :: slp_point \<times> slp_point.
        \<Sum>j. U j (fst pair) (snd pair)) \<in>
          borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    and norm_summable_AE:
      "AE pair in lborel \<Otimes>\<^sub>M lborel.
        summable (\<lambda>j. norm (U j (fst pair) (snd pair)))"
    and summable_AE:
      "AE pair in lborel \<Otimes>\<^sub>M lborel.
        summable (\<lambda>j. U j (fst pair) (snd pair))"
    and sum_bound_AE:
      "AE pair in lborel \<Otimes>\<^sub>M lborel.
        norm (\<Sum>j. U j (fst pair) (snd pair)) \<le>
          majorant (fst pair) / (1 - rho)"
proof -
  have bound_measurable:
      "\<And>j. (\<lambda>center. majorant center * rho ^ j) \<in>
        borel_measurable lborel"
    using majorant_measurable by measurable
  have all_bounds:
      "AE pair in lborel \<Otimes>\<^sub>M lborel. \<forall>j.
        norm (U j (fst pair) (snd pair)) \<le>
          majorant (fst pair) * rho ^ j"
    apply (rule slp_joint_measurable_sequence_simultaneous_fiber_bounds[
        where U=U and
          bound="\<lambda>j center. majorant center * rho ^ j"])
    apply (rule term_measurable)
    apply (rule bound_measurable)
    apply (rule fiber_bounds)
    done
  show
      "AE pair in lborel \<Otimes>\<^sub>M lborel. \<forall>j.
        norm (U j (fst pair) (snd pair)) \<le>
          majorant (fst pair) * rho ^ j"
    by (rule all_bounds)

  show
      "(\<lambda>pair :: slp_point \<times> slp_point.
        \<Sum>j. U j (fst pair) (snd pair)) \<in>
          borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule borel_measurable_suminf[OF term_measurable])

  have rho_norm: "norm rho < 1"
    using rho_nonnegative rho_strict
    by (simp add: real_norm_def abs_of_nonneg)
  have geometric_summable: "summable (\<lambda>j. rho ^ j)"
    by (rule summable_geometric[OF rho_norm])

  have pointwise:
      "\<And>pair :: slp_point \<times> slp_point.
        (\<forall>j. norm (U j (fst pair) (snd pair)) \<le>
          majorant (fst pair) * rho ^ j) \<Longrightarrow>
        summable (\<lambda>j. norm (U j (fst pair) (snd pair))) \<and>
        summable (\<lambda>j. U j (fst pair) (snd pair)) \<and>
        norm (\<Sum>j. U j (fst pair) (snd pair)) \<le>
          majorant (fst pair) / (1 - rho)"
  proof -
    fix pair :: "slp_point \<times> slp_point"
    assume bounds:
      "\<forall>j. norm (U j (fst pair) (snd pair)) \<le>
        majorant (fst pair) * rho ^ j"
    have majorant_summable:
        "summable (\<lambda>j. majorant (fst pair) * rho ^ j)"
      by (rule summable_mult[OF geometric_summable])
    have norm_summable:
        "summable (\<lambda>j. norm (U j (fst pair) (snd pair)))"
    proof (rule summable_comparison_test'[
        OF majorant_summable, where N=0])
      fix j :: nat
      assume "0 \<le> j"
      show
          "norm (norm (U j (fst pair) (snd pair))) \<le>
            majorant (fst pair) * rho ^ j"
        using bounds[rule_format, of j] by simp
    qed
    have term_summable:
        "summable (\<lambda>j. U j (fst pair) (snd pair))"
      by (rule summable_norm_cancel[OF norm_summable])
    have norm_sum:
        "norm (\<Sum>j. U j (fst pair) (snd pair)) \<le>
          (\<Sum>j. majorant (fst pair) * rho ^ j)"
      by (rule norm_suminf_le[OF bounds[rule_format] majorant_summable])
    have majorant_sum:
        "(\<Sum>j. majorant (fst pair) * rho ^ j) =
          majorant (fst pair) / (1 - rho)"
    proof -
      have geometric_value: "(\<Sum>j. rho ^ j) = 1 / (1 - rho)"
        by (rule suminf_geometric[OF rho_norm])
      show ?thesis
        using suminf_mult[OF geometric_summable,
            of "majorant (fst pair)"] geometric_value
        by (simp add: divide_inverse)
    qed
    show
        "summable (\<lambda>j. norm (U j (fst pair) (snd pair))) \<and>
          summable (\<lambda>j. U j (fst pair) (snd pair)) \<and>
          norm (\<Sum>j. U j (fst pair) (snd pair)) \<le>
            majorant (fst pair) / (1 - rho)"
      using norm_summable term_summable norm_sum majorant_sum by simp
  qed

  show
      "AE pair in lborel \<Otimes>\<^sub>M lborel.
        summable (\<lambda>j. norm (U j (fst pair) (snd pair)))"
    using all_bounds by eventually_elim (use pointwise in blast)
  show
      "AE pair in lborel \<Otimes>\<^sub>M lborel.
        summable (\<lambda>j. U j (fst pair) (snd pair))"
    using all_bounds by eventually_elim (use pointwise in blast)
  show
      "AE pair in lborel \<Otimes>\<^sub>M lborel.
        norm (\<Sum>j. U j (fst pair) (snd pair)) \<le>
          majorant (fst pair) / (1 - rho)"
    using all_bounds by eventually_elim (use pointwise in blast)
qed

end
