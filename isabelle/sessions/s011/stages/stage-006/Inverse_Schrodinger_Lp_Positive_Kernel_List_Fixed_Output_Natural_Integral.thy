theory Inverse_Schrodinger_Lp_Positive_Kernel_List_Fixed_Output_Natural_Integral
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Positive_Kernel_List_Fixed_Output_Integral"
begin

section \<open>Natural-range fixed-output positive kernel integral\<close>

theorem slp_left_branch_positive_kernel_list_fixed_output_integral_natural:
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_value_measurable[measurable]:
      "terminal_value \<in> borel_measurable lborel"
  shows
    "nn_integral
        ((PiM {..<n}
            (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
          (PiM {..<n}
            (\<lambda>_::nat. (lborel :: slp_point measure))))
        (\<lambda>(pos, neg).
          slp_left_branch_positive_kernel_list_fixed_output R cutoff
            potential terminal_value
            (map (\<lambda>k. (pos k, neg k)) [0..<n]) origin target) =
      slp_positive_output_density R cutoff potential
        (\<lambda>x. ennreal (norm (terminal_value x))) n origin target"
proof -
  have distinct_indices: "distinct [0..<n]"
    by (rule distinct_upt)
  note result =
    slp_left_branch_positive_kernel_list_fixed_output_integral_distinct[
      where ks = "[0..<n]" and R = R and cutoff = cutoff
        and potential = potential and terminal_value = terminal_value
        and origin = origin and target = target,
      OF distinct_indices cutoff_measurable potential_measurable
        terminal_value_measurable]
  show ?thesis
    using result
    by (simp only: set_upt atLeast0LessThan length_upt diff_zero)
qed

end
