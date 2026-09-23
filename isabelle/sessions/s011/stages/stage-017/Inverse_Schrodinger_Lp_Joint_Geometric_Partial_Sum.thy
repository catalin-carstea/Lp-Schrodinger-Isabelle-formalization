theory Inverse_Schrodinger_Lp_Joint_Geometric_Partial_Sum
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_Joint_Geometric_Series_Tail"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Variable-majorant finite geometric prefixes on a joint carrier\<close>

theorem slp_variable_majorant_geometric_partial_sum_AE:
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
      norm (\<Sum>j<N. U j x) \<le> majorant x / (1 - rho)"
proof -
  have rho_norm: "norm rho < 1"
    using rho_nonnegative rho_strict
    by (simp add: real_norm_def abs_of_nonneg)
  have geometric_summable: "summable (\<lambda>j. rho ^ j)"
    by (rule summable_geometric[OF rho_norm])

  have pointwise:
      "\<And>x N. (\<forall>j. norm (U j x) \<le> majorant x * rho ^ j) \<Longrightarrow>
        norm (\<Sum>j<N. U j x) \<le> majorant x / (1 - rho)"
  proof -
    fix x N
    assume bounds:
      "\<forall>j. norm (U j x) \<le> majorant x * rho ^ j"
    have majorant_summable:
        "summable (\<lambda>j. majorant x * rho ^ j)"
      by (rule summable_mult[OF geometric_summable])
    have norm_finite:
        "norm (\<Sum>j<N. U j x) \<le>
          (\<Sum>j<N. majorant x * rho ^ j)"
    proof (rule order_trans[OF norm_sum])
      show
          "(\<Sum>j<N. norm (U j x)) \<le>
            (\<Sum>j<N. majorant x * rho ^ j)"
        by (rule sum_mono) (rule bounds[rule_format])
    qed
    have finite_le_suminf:
        "(\<Sum>j<N. majorant x * rho ^ j) \<le>
          (\<Sum>j. majorant x * rho ^ j)"
    proof (rule sum_le_suminf[OF majorant_summable])
      show "finite {..<N}"
        by simp
      fix j
      assume "j \<in> - {..<N}"
      show "0 \<le> majorant x * rho ^ j"
        by (rule mult_nonneg_nonneg[OF majorant_nonnegative])
          (use rho_nonnegative in simp)
    qed
    have majorant_value:
        "(\<Sum>j. majorant x * rho ^ j) =
          majorant x / (1 - rho)"
    proof -
      have geometric_value:
          "(\<Sum>j. rho ^ j) = 1 / (1 - rho)"
        by (rule suminf_geometric[OF rho_norm])
      show ?thesis
        using suminf_mult[OF geometric_summable,
            of "majorant x"] geometric_value
        by (simp add: divide_inverse)
    qed
    show
        "norm (\<Sum>j<N. U j x) \<le> majorant x / (1 - rho)"
      using norm_finite finite_le_suminf majorant_value by linarith
  qed

  show ?thesis
    using simultaneous_bounds
    by eventually_elim (intro allI, rule pointwise)
qed

end
