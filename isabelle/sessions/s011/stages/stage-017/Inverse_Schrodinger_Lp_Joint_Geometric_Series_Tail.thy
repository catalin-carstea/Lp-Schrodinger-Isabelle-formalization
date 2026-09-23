theory Inverse_Schrodinger_Lp_Joint_Geometric_Series_Tail
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Joint_Fiber_Geometric_Series"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Variable-majorant geometric tails on a joint carrier\<close>

theorem slp_variable_majorant_geometric_series_tail_AE:
  fixes M :: "'x measure"
    and U :: "nat \<Rightarrow> 'x \<Rightarrow> 'b::banach"
    and majorant :: "'x \<Rightarrow> real"
    and rho :: real
  assumes majorant_nonnegative: "\<And>x. 0 \<le> majorant x"
    and rho_nonnegative: "0 \<le> rho"
    and rho_strict: "rho < 1"
    and simultaneous_bounds:
      "AE x in M. \<forall>j. norm (U j x) \<le> majorant x * rho ^ j"
  shows
    "AE x in M. \<forall>N.
      norm ((\<Sum>j. U j x) - (\<Sum>j<N. U j x)) \<le>
        majorant x * rho ^ N / (1 - rho)"
proof -
  have rho_norm: "norm rho < 1"
    using rho_nonnegative rho_strict
    by (simp add: real_norm_def abs_of_nonneg)
  have geometric_summable: "summable (\<lambda>j. rho ^ j)"
    by (rule summable_geometric[OF rho_norm])

  have pointwise:
      "\<And>x N. (\<forall>j. norm (U j x) \<le> majorant x * rho ^ j) \<Longrightarrow>
        norm ((\<Sum>j. U j x) - (\<Sum>j<N. U j x)) \<le>
          majorant x * rho ^ N / (1 - rho)"
  proof -
    fix x N
    assume bounds:
      "\<forall>j. norm (U j x) \<le> majorant x * rho ^ j"
    have majorant_summable:
        "summable (\<lambda>j. majorant x * rho ^ j)"
      by (rule summable_mult[OF geometric_summable])
    have U_summable: "summable (\<lambda>j. U j x)"
    proof (rule summable_norm_cancel)
      show "summable (\<lambda>j. norm (U j x))"
      proof (rule summable_comparison_test'[
          OF majorant_summable, where N=0])
        fix j :: nat
        assume "0 \<le> j"
        show "norm (norm (U j x)) \<le> majorant x * rho ^ j"
          using bounds[rule_format, of j] by simp
      qed
    qed
    have tail_identity:
        "(\<Sum>j. U j x) - (\<Sum>j<N. U j x) =
          (\<Sum>j. U (j + N) x)"
      using suminf_minus_initial_segment[OF U_summable, of N]
      by simp
    have shifted_majorant_summable:
        "summable (\<lambda>j. majorant x * rho ^ (j + N))"
    proof -
      have shifted:
          "(\<lambda>j. majorant x * rho ^ (j + N)) =
            (\<lambda>j. (majorant x * rho ^ N) * rho ^ j)"
        by (rule ext) (simp add: power_add algebra_simps)
      show ?thesis
        unfolding shifted
        by (rule summable_mult[OF geometric_summable])
    qed
    have tail_norm:
        "norm (\<Sum>j. U (j + N) x) \<le>
          (\<Sum>j. majorant x * rho ^ (j + N))"
      by (rule norm_suminf_le[OF _ shifted_majorant_summable])
        (rule bounds[rule_format])
    have shifted_majorant_value:
        "(\<Sum>j. majorant x * rho ^ (j + N)) =
          majorant x * rho ^ N / (1 - rho)"
    proof -
      have shifted:
          "(\<lambda>j. majorant x * rho ^ (j + N)) =
            (\<lambda>j. (majorant x * rho ^ N) * rho ^ j)"
        by (rule ext) (simp add: power_add algebra_simps)
      have geometric_value:
          "(\<Sum>j. rho ^ j) = 1 / (1 - rho)"
        by (rule suminf_geometric[OF rho_norm])
      show ?thesis
        unfolding shifted
        using suminf_mult[OF geometric_summable,
            of "majorant x * rho ^ N"] geometric_value
        by (simp add: divide_inverse)
    qed
    show
        "norm ((\<Sum>j. U j x) - (\<Sum>j<N. U j x)) \<le>
          majorant x * rho ^ N / (1 - rho)"
      using tail_identity tail_norm shifted_majorant_value by simp
  qed

  show ?thesis
    using simultaneous_bounds
    by eventually_elim (intro allI, rule pointwise)
qed

end
