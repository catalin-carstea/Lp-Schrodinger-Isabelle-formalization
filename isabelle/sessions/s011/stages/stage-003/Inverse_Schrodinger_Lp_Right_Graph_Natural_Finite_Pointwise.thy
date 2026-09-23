theory Inverse_Schrodinger_Lp_Right_Graph_Natural_Finite_Pointwise
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Right_Graph_Natural_Conjugate"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Graph_Natural_Finite_Pointwise"
begin

section \<open>Pointwise natural-to-finite transport of the right graph\<close>

definition slp_right_branch_oscillatory_graph_kernel_fixed_root_finite ::
    "real \<Rightarrow> slp_point \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow> slp_point \<Rightarrow>
      (((slp_point^'i::finite) \<times> (slp_point^'i)) \<times> slp_point)
        \<Rightarrow> complex"
where
  "slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau center
      cutoff potential terminal_value origin coordinates =
    cnj (slp_left_branch_oscillatory_graph_kernel_fixed_root_finite (- tau)
      center (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (potential x))
      (\<lambda>x. cnj (terminal_value x)) origin coordinates)"

lemma slp_right_branch_oscillatory_graph_kernel_fixed_root_finite_norm [simp]:
  "cmod (slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau
      center cutoff potential terminal_value origin coordinates) =
    cmod (slp_left_branch_oscillatory_graph_kernel_fixed_root_finite (- tau)
      center (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (potential x))
      (\<lambda>x. cnj (terminal_value x)) origin coordinates)"
  by (simp add:
      slp_right_branch_oscillatory_graph_kernel_fixed_root_finite_def)

theorem slp_right_branch_oscillatory_graph_kernel_natural_to_finite_pointwise:
  fixes branch_dummy :: "'i::finite itself"
  shows
    "slp_right_branch_oscillatory_graph_kernel_natural CARD('i) tau center
        cutoff potential terminal_value origin
        ((pos_natural, neg_natural), terminal) =
      slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau center
        cutoff potential terminal_value origin
        (((\<chi> i::'i. pos_natural (to_nat_on UNIV i)),
          (\<chi> i::'i. neg_natural (to_nat_on UNIV i))), terminal)"
  unfolding slp_right_branch_oscillatory_graph_kernel_natural_def
    slp_right_branch_oscillatory_graph_kernel_fixed_root_finite_def
  by (simp only:
      slp_left_branch_oscillatory_graph_kernel_natural_to_finite_pointwise)

end
