theory Inverse_Schrodinger_Lp_Left_Oscillatory_Graph_Kernel
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Left_Recursive_Branch_Zero_Graph"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Phase_Modulation"
begin

section \<open>The exact oscillatory left graph kernel\<close>

definition slp_left_branch_oscillatory_graph_kernel ::
    "real \<Rightarrow> slp_point \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<times> slp_point) list \<Rightarrow>
      slp_point \<Rightarrow> slp_point \<Rightarrow> complex"
where
  "slp_left_branch_oscillatory_graph_kernel tau center cutoff potential
      terminal_value pairs origin terminal =
    exp (\<i> * of_real
      (tau * slp_left_branch_phase center pairs terminal)) *
    slp_left_branch_complex_kernel_list cutoff potential terminal_value
      pairs origin terminal"

lemma slp_left_branch_oscillatory_graph_kernel_Nil:
  "slp_left_branch_oscillatory_graph_kernel tau center cutoff potential
      terminal_value [] origin terminal =
    slp_center_kernel tau center terminal *
      slp_left_branch_complex_kernel_list cutoff potential terminal_value
        [] origin terminal"
  unfolding slp_left_branch_oscillatory_graph_kernel_def
    slp_left_branch_phase_def slp_branch_phase_def slp_center_kernel_def
  by simp

lemma slp_left_branch_oscillatory_graph_kernel_Cons:
  "slp_left_branch_oscillatory_graph_kernel tau center cutoff potential
      terminal_value (pair # pairs) origin terminal =
    inverse (of_real (pi ^ 2)) *
      slp_center_kernel tau center (fst pair) *
      slp_center_kernel (- tau) center (snd pair) *
      slp_left_branch_complex_block cutoff potential origin (fst pair)
        (snd pair) *
      slp_left_branch_oscillatory_graph_kernel tau center cutoff potential
        terminal_value pairs (snd pair) terminal"
proof -
  have phase_Cons:
      "slp_left_branch_phase center (pair # pairs) terminal =
        slp_center_phase center (fst pair) -
        slp_center_phase center (snd pair) +
        slp_left_branch_phase center pairs terminal"
    unfolding slp_left_branch_phase_def slp_branch_phase_def
    by simp
  have exponent_split:
      "\<i> * of_real
          (tau * (slp_center_phase center (fst pair) -
            slp_center_phase center (snd pair) +
            slp_left_branch_phase center pairs terminal)) =
        \<i> * of_real (tau * slp_center_phase center (fst pair)) +
        \<i> * of_real ((- tau) * slp_center_phase center (snd pair)) +
        \<i> * of_real
          (tau * slp_left_branch_phase center pairs terminal)"
    by (simp add: algebra_simps)
  have oscillation_Cons:
      "exp (\<i> * of_real
          (tau * slp_left_branch_phase center (pair # pairs) terminal)) =
        slp_center_kernel tau center (fst pair) *
        slp_center_kernel (- tau) center (snd pair) *
        exp (\<i> * of_real
          (tau * slp_left_branch_phase center pairs terminal))"
    unfolding phase_Cons exponent_split slp_center_kernel_def
    by (simp only: exp_add mult.assoc)
  show ?thesis
    unfolding slp_left_branch_oscillatory_graph_kernel_def
      slp_left_branch_complex_kernel_list.simps oscillation_Cons
    by (simp only: mult.assoc mult.commute mult.left_commute)
qed

lemma slp_left_branch_zero_graph_integral_oscillatory_kernel:
  "slp_left_branch_zero_graph_integral tau center cutoff potential
      terminal_value origin =
    integral\<^sup>L lborel
      (slp_left_branch_oscillatory_graph_kernel tau center cutoff potential
        terminal_value [] origin)"
  unfolding slp_left_branch_zero_graph_integral_def
    slp_left_branch_oscillatory_graph_kernel_Nil
  by (rule refl)

end
