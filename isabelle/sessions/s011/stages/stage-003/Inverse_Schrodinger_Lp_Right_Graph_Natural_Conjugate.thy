theory Inverse_Schrodinger_Lp_Right_Graph_Natural_Conjugate
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Right_Neumann_Iterate"
begin

section \<open>The natural-coordinate right branch graph by conjugation\<close>

definition slp_right_branch_oscillatory_graph_kernel_natural ::
    "nat \<Rightarrow> real \<Rightarrow> slp_point \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow> slp_point \<Rightarrow>
      (((nat \<Rightarrow> slp_point) \<times> (nat \<Rightarrow> slp_point)) \<times>
        slp_point) \<Rightarrow> complex"
where
  "slp_right_branch_oscillatory_graph_kernel_natural n tau center cutoff
      potential terminal_value origin coordinates =
    cnj (slp_left_branch_oscillatory_graph_kernel_natural n (- tau) center
      (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (potential x))
      (\<lambda>x. cnj (terminal_value x)) origin coordinates)"

lemma slp_right_branch_oscillatory_graph_kernel_natural_norm [simp]:
  "cmod (slp_right_branch_oscillatory_graph_kernel_natural n tau center
      cutoff potential terminal_value origin coordinates) =
    cmod (slp_left_branch_oscillatory_graph_kernel_natural n (- tau) center
      (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (potential x))
      (\<lambda>x. cnj (terminal_value x)) origin coordinates)"
  by (simp add: slp_right_branch_oscillatory_graph_kernel_natural_def)

lemma slp_right_branch_oscillatory_graph_kernel_natural_integrable_iff:
  "integrable M
      (slp_right_branch_oscillatory_graph_kernel_natural n tau center cutoff
        potential terminal_value origin) \<longleftrightarrow>
    integrable M
      (slp_left_branch_oscillatory_graph_kernel_natural n (- tau) center
        (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (potential x))
        (\<lambda>x. cnj (terminal_value x)) origin)"
  unfolding slp_right_branch_oscillatory_graph_kernel_natural_def
proof
  assume right_integrable:
    "integrable M (\<lambda>coordinates.
      cnj (slp_left_branch_oscillatory_graph_kernel_natural n (- tau) center
        (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (potential x))
        (\<lambda>x. cnj (terminal_value x)) origin coordinates))"
  have twice_integrable:
    "integrable M (\<lambda>coordinates.
      cnj (cnj
        (slp_left_branch_oscillatory_graph_kernel_natural n (- tau) center
          (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (potential x))
          (\<lambda>x. cnj (terminal_value x)) origin coordinates)))"
    by (rule integrable_cnj[OF right_integrable])
  show
    "integrable M
      (slp_left_branch_oscillatory_graph_kernel_natural n (- tau) center
        (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (potential x))
        (\<lambda>x. cnj (terminal_value x)) origin)"
    using twice_integrable by simp
next
  assume left_integrable:
    "integrable M
      (slp_left_branch_oscillatory_graph_kernel_natural n (- tau) center
        (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (potential x))
        (\<lambda>x. cnj (terminal_value x)) origin)"
  show
    "integrable M (\<lambda>coordinates.
      cnj (slp_left_branch_oscillatory_graph_kernel_natural n (- tau) center
        (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (potential x))
        (\<lambda>x. cnj (terminal_value x)) origin coordinates))"
    by (rule integrable_cnj[OF left_integrable])
qed

theorem slp_right_branch_oscillatory_graph_kernel_natural_integral:
  "integral\<^sup>L M
      (slp_right_branch_oscillatory_graph_kernel_natural n tau center cutoff
        potential terminal_value origin) =
    cnj (integral\<^sup>L M
      (slp_left_branch_oscillatory_graph_kernel_natural n (- tau) center
        (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (potential x))
        (\<lambda>x. cnj (terminal_value x)) origin))"
  unfolding slp_right_branch_oscillatory_graph_kernel_natural_def
  by (rule Bochner_Integration.integral_cnj)

end
