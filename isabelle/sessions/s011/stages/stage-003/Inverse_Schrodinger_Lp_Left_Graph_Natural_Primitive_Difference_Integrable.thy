theory Inverse_Schrodinger_Lp_Left_Graph_Natural_Primitive_Difference_Integrable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Graph_Natural_Cauchy_Recursive_Identity"
begin

section \<open>Natural graph integrability for the primitive difference\<close>

lemma slp_left_branch_complex_kernel_list_terminal_diff:
  fixes scalar :: complex
  shows
    "slp_left_branch_complex_kernel_list cutoff potential
        (\<lambda>x. terminal_value x - scalar) pairs origin terminal =
      slp_left_branch_complex_kernel_list cutoff potential terminal_value
          pairs origin terminal -
        scalar * slp_left_branch_complex_kernel_list cutoff potential
          (\<lambda>_. 1) pairs origin terminal"
proof (induction pairs arbitrary: origin)
  case Nil
  show ?case
    unfolding slp_left_branch_complex_kernel_list.simps
      slp_left_branch_complex_terminal_def
    by (simp add: algebra_simps)
next
  case (Cons pair pairs)
  show ?case
    unfolding slp_left_branch_complex_kernel_list.simps
      Cons.IH[of "snd pair"]
    by (simp add: algebra_simps)
qed

lemma slp_left_branch_oscillatory_graph_kernel_natural_terminal_diff:
  fixes scalar :: complex
  shows
    "slp_left_branch_oscillatory_graph_kernel_natural n tau center cutoff
        potential (\<lambda>x. terminal_value x - scalar) origin coordinates =
      slp_left_branch_oscillatory_graph_kernel_natural n tau center cutoff
          potential terminal_value origin coordinates -
        scalar *
          slp_left_branch_oscillatory_graph_kernel_natural n tau center cutoff
            potential (\<lambda>_. 1) origin coordinates"
  unfolding slp_left_branch_oscillatory_graph_kernel_natural_def
    slp_left_branch_oscillatory_graph_kernel_def
    slp_left_branch_complex_kernel_list_terminal_diff
  by (simp add: algebra_simps)

context aim_planar_riesz_hls_cauchy
begin

theorem slp_left_branch_oscillatory_graph_kernel_natural_primitive_diff_integrable:
  fixes B C p tau :: real
    and center origin :: slp_point
    and cutoff potential :: "slp_point \<Rightarrow> complex"
    and orientation :: slp_cauchy_orientation
  assumes B_nonnegative: "0 \<le> B"
    and origin_bound: "Real_Vector_Spaces.norm origin \<le> B"
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and potential_support:
      "\<And>x. potential x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "integrable
      (((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))
          \<Otimes>\<^sub>M
        (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))))
          \<Otimes>\<^sub>M (lborel :: slp_point measure))
      (slp_left_branch_oscillatory_graph_kernel_natural n tau center cutoff
        potential
          (\<lambda>x. slp_cauchy_transform orientation potential x -
            slp_cauchy_transform orientation potential center)
        origin)"
proof -
  let ?M =
    "((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))
        \<Otimes>\<^sub>M
      (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))))
        \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?A = "slp_cauchy_transform orientation potential"
  have cauchy_integrable:
      "integrable ?M
        (slp_left_branch_oscillatory_graph_kernel_natural n tau center cutoff
          potential ?A origin)"
    by (rule
        slp_left_branch_oscillatory_graph_kernel_natural_cauchy_integrable[
          OF B_nonnegative origin_bound cutoff_support potential_support
            p_lower p_upper cutoff_measurable potential_lp cutoff_bound
            C_nonnegative])
  have unit_integrable:
      "integrable ?M
        (slp_left_branch_oscillatory_graph_kernel_natural n tau center cutoff
          potential (\<lambda>_. 1) origin)"
    by (rule
        slp_left_branch_oscillatory_graph_kernel_natural_integrable_hls[
          OF B_nonnegative origin_bound cutoff_support potential_support
            p_lower p_upper cutoff_measurable potential_lp cutoff_bound
            C_nonnegative])
  have scaled_unit_integrable:
      "integrable ?M (\<lambda>coordinates.
        ?A center *
          slp_left_branch_oscillatory_graph_kernel_natural n tau center cutoff
            potential (\<lambda>_. 1) origin coordinates)"
    by (rule Bochner_Integration.integrable_mult_right[OF unit_integrable])
  have graph_eq:
      "slp_left_branch_oscillatory_graph_kernel_natural n tau center cutoff
          potential (\<lambda>x. ?A x - ?A center) origin =
        (\<lambda>coordinates.
          slp_left_branch_oscillatory_graph_kernel_natural n tau center cutoff
              potential ?A origin coordinates -
            ?A center *
              slp_left_branch_oscillatory_graph_kernel_natural n tau center
                cutoff potential (\<lambda>_. 1) origin coordinates)"
    by (rule ext)
      (rule
        slp_left_branch_oscillatory_graph_kernel_natural_terminal_diff)
  have difference_integrable:
      "integrable ?M (\<lambda>coordinates.
        slp_left_branch_oscillatory_graph_kernel_natural n tau center cutoff
            potential ?A origin coordinates -
          ?A center *
            slp_left_branch_oscillatory_graph_kernel_natural n tau center
              cutoff potential (\<lambda>_. 1) origin coordinates)"
    by (rule Bochner_Integration.integrable_diff[
          OF cauchy_integrable scaled_unit_integrable])
  show ?thesis
    apply (subst graph_eq)
    by (rule difference_integrable)
qed

end

end
