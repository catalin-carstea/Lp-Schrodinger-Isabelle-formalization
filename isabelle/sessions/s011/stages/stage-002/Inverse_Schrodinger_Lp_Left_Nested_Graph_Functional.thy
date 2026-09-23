theory Inverse_Schrodinger_Lp_Left_Nested_Graph_Functional
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Left_Oscillatory_Graph_Kernel"
begin

section \<open>The recursively nested complex left graph functional\<close>

primrec slp_left_branch_nested_graph_functional ::
    "nat \<Rightarrow> real \<Rightarrow> slp_point \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      slp_point \<Rightarrow> complex"
where
  "slp_left_branch_nested_graph_functional 0 tau center cutoff potential
      terminal_value origin =
    integral\<^sup>L lborel
      (slp_left_branch_oscillatory_graph_kernel tau center cutoff potential
        terminal_value [] origin)"
| "slp_left_branch_nested_graph_functional (Suc n) tau center cutoff
      potential terminal_value origin =
    inverse (of_real (pi ^ 2)) *
      integral\<^sup>L lborel
        (\<lambda>pos. integral\<^sup>L lborel
          (\<lambda>neg.
            slp_center_kernel tau center pos *
            slp_center_kernel (- tau) center neg *
            slp_left_branch_complex_block cutoff potential origin pos neg *
            slp_left_branch_nested_graph_functional n tau center cutoff
              potential terminal_value neg))"

lemma slp_left_branch_nested_graph_functional_zero:
  "slp_left_branch_nested_graph_functional 0 tau center cutoff potential
      terminal_value origin =
    integral\<^sup>L lborel
      (slp_left_branch_oscillatory_graph_kernel tau center cutoff potential
        terminal_value [] origin)"
  by simp

lemma slp_left_branch_nested_graph_functional_Suc:
  "slp_left_branch_nested_graph_functional (Suc n) tau center cutoff potential
      terminal_value origin =
    inverse (of_real (pi ^ 2)) *
      integral\<^sup>L lborel
        (\<lambda>pos. integral\<^sup>L lborel
          (\<lambda>neg.
            slp_center_kernel tau center pos *
            slp_center_kernel (- tau) center neg *
            slp_left_branch_complex_block cutoff potential origin pos neg *
            slp_left_branch_nested_graph_functional n tau center cutoff
              potential terminal_value neg))"
  by simp

theorem slp_left_recursive_branch_eq_nested_graph_functional:
  "slp_left_recursive_branch n tau center cutoff potential terminal_value
      origin =
    slp_left_branch_nested_graph_functional n tau center cutoff potential
      terminal_value origin"
proof (induction n arbitrary: origin)
  case 0
  show ?case
    by (simp only: slp_left_recursive_branch_zero_eq_graph_integral
        slp_left_branch_zero_graph_integral_oscillatory_kernel
        slp_left_branch_nested_graph_functional.simps)
next
  case (Suc n)
  let ?tail =
    "slp_left_branch_nested_graph_functional n tau center cutoff potential
      terminal_value"
  let ?raw_inner =
    "\<lambda>pos neg.
      (slp_center_kernel (- tau) center neg *
        (potential neg * ?tail neg)) *
      slp_cauchy_kernel SLP_Dbar_Inverse pos neg"
  let ?graph_inner =
    "\<lambda>pos neg.
      slp_center_kernel tau center pos *
      slp_center_kernel (- tau) center neg *
      slp_left_branch_complex_block cutoff potential origin pos neg *
      ?tail neg"
  have inner_integrand:
      "(\<lambda>neg. ?graph_inner pos neg) =
        (\<lambda>neg.
          (slp_center_kernel tau center pos * cutoff pos *
            slp_cauchy_kernel SLP_Partial_Inverse origin pos) *
          ?raw_inner pos neg)"
    for pos
    unfolding slp_left_branch_complex_block_def
    by (rule ext)
      (simp only: mult.assoc mult.commute mult.left_commute)
  have inner_integral:
      "integral\<^sup>L lborel (\<lambda>neg. ?graph_inner pos neg) =
        (slp_center_kernel tau center pos * cutoff pos *
          slp_cauchy_kernel SLP_Partial_Inverse origin pos) *
        integral\<^sup>L lborel (?raw_inner pos)"
    for pos
    unfolding inner_integrand
    by (simp only: Bochner_Integration.integral_mult_right_zero)
  have outer_integrand:
      "(\<lambda>pos.
          (slp_center_kernel tau center pos *
            (cutoff pos *
              (inverse (of_real pi) *
                integral\<^sup>L lborel (?raw_inner pos)))) *
          slp_cauchy_kernel SLP_Partial_Inverse origin pos) =
        (\<lambda>pos.
          inverse (of_real pi) *
            integral\<^sup>L lborel (\<lambda>neg. ?graph_inner pos neg))"
    apply (rule ext)
    apply (subst inner_integral)
    by (simp only: mult.assoc mult.commute mult.left_commute)
  have coefficient:
      "inverse (of_real pi :: complex) * inverse (of_real pi) =
        inverse (of_real (pi ^ 2))"
    apply (subst power2_eq_square[symmetric])
    apply (subst of_real_power)
    apply (simp only: power2_eq_square)
    apply (rule HOL.sym)
    by (fact inverse_mult_distrib)
  have analytic_expansion:
      "slp_left_recursive_branch (Suc n) tau center cutoff potential
          terminal_value origin =
        inverse (of_real pi) *
          integral\<^sup>L lborel
            (\<lambda>pos.
              (slp_center_kernel tau center pos *
                (cutoff pos *
                  (inverse (of_real pi) *
                    integral\<^sup>L lborel (?raw_inner pos)))) *
              slp_cauchy_kernel SLP_Partial_Inverse origin pos)"
    by (simp only: slp_left_recursive_branch_Suc_integral Suc.IH)
  have scalarized:
      "inverse (of_real pi) *
          integral\<^sup>L lborel
            (\<lambda>pos.
              (slp_center_kernel tau center pos *
                (cutoff pos *
                  (inverse (of_real pi) *
                    integral\<^sup>L lborel (?raw_inner pos)))) *
              slp_cauchy_kernel SLP_Partial_Inverse origin pos) =
        inverse (of_real (pi ^ 2)) *
          integral\<^sup>L lborel
            (\<lambda>pos. integral\<^sup>L lborel
              (\<lambda>neg. ?graph_inner pos neg))"
    apply (subst outer_integrand)
    apply (subst Bochner_Integration.integral_mult_right_zero)
    apply (subst mult.assoc[symmetric])
    apply (subst coefficient)
    by (rule HOL.refl)
  show ?case
    unfolding slp_left_branch_nested_graph_functional.simps
    by (rule trans[OF analytic_expansion scalarized])
qed

end
