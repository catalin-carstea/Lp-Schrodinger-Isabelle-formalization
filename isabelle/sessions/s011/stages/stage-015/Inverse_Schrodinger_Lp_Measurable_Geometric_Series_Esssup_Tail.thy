theory Inverse_Schrodinger_Lp_Measurable_Geometric_Series_Esssup_Tail
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Left_Neumann_Iterate_Lpstar_Geometric"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Measurable geometric series with raw essential-supremum tails\<close>

theorem slp_measurable_geometric_series_esssup_tail:
  fixes M :: "'x measure"
    and U :: "nat \<Rightarrow> 'x \<Rightarrow> 'b::{banach, second_countable_topology}"
    and P rho :: real
  assumes terms_measurable:
      "\<And>j. U j \<in> borel_measurable M"
    and P_nonnegative: "0 \<le> P"
    and rho_nonnegative: "0 \<le> rho"
    and rho_strict: "rho < 1"
    and term_bound:
      "\<And>j. AE x in M. norm (U j x) \<le> P * rho ^ j"
  shows sum_measurable:
      "(\<lambda>x. \<Sum>j. U j x) \<in> borel_measurable M"
    and norm_summable_AE:
      "AE x in M. summable (\<lambda>j. norm (U j x))"
    and summable_AE:
      "AE x in M. summable (\<lambda>j. U j x)"
    and tail_esssup:
      "\<And>N. esssup M
          (\<lambda>x. ereal
            (norm ((\<Sum>j. U j x) - (\<Sum>j<N. U j x))))
        \<le> ereal (P * rho ^ N / (1 - rho))"
proof -
  have rho_norm: "norm rho < 1"
    using rho_nonnegative rho_strict
    by (simp add: real_norm_def abs_of_nonneg)
  have geometric_summable: "summable (\<lambda>j. rho ^ j)"
    by (rule summable_geometric[OF rho_norm])
  have majorant_summable: "summable (\<lambda>j. P * rho ^ j)"
    by (rule summable_mult[OF geometric_summable])
  have all_bounds:
      "AE x in M. \<forall>j. norm (U j x) \<le> P * rho ^ j"
    using term_bound
    unfolding AE_all_countable
    by blast

  show "(\<lambda>x. \<Sum>j. U j x) \<in> borel_measurable M"
    by (rule borel_measurable_suminf[OF terms_measurable])

  have pointwise_norm_summable:
      "\<And>x. (\<forall>j. norm (U j x) \<le> P * rho ^ j) \<Longrightarrow>
        summable (\<lambda>j. norm (U j x))"
  proof -
    fix x
    assume bounds:
      "\<forall>j. norm (U j x) \<le> P * rho ^ j"
    show "summable (\<lambda>j. norm (U j x))"
    proof (rule summable_comparison_test'[
        OF majorant_summable, where N = 0])
      fix j :: nat
      assume "0 \<le> j"
      show "norm (norm (U j x)) \<le> P * rho ^ j"
        using bounds[rule_format, of j] by simp
    qed
  qed

  show "AE x in M. summable (\<lambda>j. norm (U j x))"
    using all_bounds
    by eventually_elim (rule pointwise_norm_summable)

  show "AE x in M. summable (\<lambda>j. U j x)"
    using all_bounds
    by eventually_elim
      (rule summable_norm_cancel, rule pointwise_norm_summable)

  fix N :: nat
  have shifted_majorant_summable:
      "summable (\<lambda>j. P * rho ^ (j + N))"
  proof -
    have shifted:
        "(\<lambda>j. P * rho ^ (j + N)) =
          (\<lambda>j. (P * rho ^ N) * rho ^ j)"
      by (rule ext) (simp add: power_add algebra_simps)
    show ?thesis
      unfolding shifted
      by (rule summable_mult[OF geometric_summable])
  qed
  have shifted_majorant_value:
      "(\<Sum>j. P * rho ^ (j + N)) =
        P * rho ^ N / (1 - rho)"
  proof -
    have shifted:
        "(\<lambda>j. P * rho ^ (j + N)) =
          (\<lambda>j. (P * rho ^ N) * rho ^ j)"
      by (rule ext) (simp add: power_add algebra_simps)
    have geometric_value:
        "(\<Sum>j. rho ^ j) = 1 / (1 - rho)"
      by (rule suminf_geometric[OF rho_norm])
    show ?thesis
      unfolding shifted
      using suminf_mult[OF geometric_summable, of "P * rho ^ N"]
        geometric_value
      by (simp add: divide_inverse)
  qed

  have tail_AE:
      "AE x in M.
        norm ((\<Sum>j. U j x) - (\<Sum>j<N. U j x))
          \<le> P * rho ^ N / (1 - rho)"
    using all_bounds
  proof eventually_elim
    fix x
    assume bounds:
      "\<forall>j. norm (U j x) \<le> P * rho ^ j"
    have U_summable: "summable (\<lambda>j. U j x)"
      by (rule summable_norm_cancel, rule pointwise_norm_summable,
          rule bounds)
    have tail_identity:
        "(\<Sum>j. U j x) - (\<Sum>j<N. U j x) =
          (\<Sum>j. U (j + N) x)"
      using suminf_minus_initial_segment[OF U_summable, of N]
      by simp
    have tail_norm:
        "norm (\<Sum>j. U (j + N) x)
          \<le> (\<Sum>j. P * rho ^ (j + N))"
      by (rule norm_suminf_le[OF _ shifted_majorant_summable])
        (rule bounds[rule_format])
    show
        "norm ((\<Sum>j. U j x) - (\<Sum>j<N. U j x))
          \<le> P * rho ^ N / (1 - rho)"
      using tail_identity tail_norm shifted_majorant_value by simp
  qed
  have tail_ereal_AE:
      "AE x in M.
        ereal (norm ((\<Sum>j. U j x) - (\<Sum>j<N. U j x)))
          \<le> ereal (P * rho ^ N / (1 - rho))"
    using tail_AE by eventually_elim simp
  have tail_measurable:
      "(\<lambda>x. ereal
        (norm ((\<Sum>j. U j x) - (\<Sum>j<N. U j x))))
        \<in> borel_measurable M"
    using terms_measurable
    by measurable
  show
      "esssup M
          (\<lambda>x. ereal
            (norm ((\<Sum>j. U j x) - (\<Sum>j<N. U j x))))
        \<le> ereal (P * rho ^ N / (1 - rho))"
    by (rule esssup_I[OF tail_measurable tail_ereal_AE])
qed

end
