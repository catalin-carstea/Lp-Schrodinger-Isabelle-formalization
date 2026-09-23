theory Inverse_Schrodinger_Lp_Right_Neumann_Iterate
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Neumann_Iterate"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Right_Recursive_Branch"
begin

section \<open>The exact manuscript right Neumann iterate\<close>

definition slp_right_neumann_iterate ::
    "nat \<Rightarrow> real \<Rightarrow> slp_point \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      slp_cauchy_orientation \<Rightarrow> slp_point \<Rightarrow> complex"
where
  "slp_right_neumann_iterate n tau center cutoff potential orientation =
    slp_right_recursive_branch n tau center cutoff potential
      (\<lambda>x. slp_cauchy_transform orientation potential x -
        slp_cauchy_transform orientation potential center)"

lemma slp_right_neumann_iterate_zero:
  "slp_right_neumann_iterate 0 tau center cutoff potential orientation =
    slp_dbar_psi_inverse (- tau) center
      (\<lambda>terminal. cutoff terminal *
        (slp_cauchy_transform orientation potential terminal -
          slp_cauchy_transform orientation potential center))"
  unfolding slp_right_neumann_iterate_def
  by (rule slp_right_recursive_branch.simps)

lemma slp_right_neumann_iterate_Suc:
  "slp_right_neumann_iterate (Suc n) tau center cutoff potential orientation =
    slp_dbar_psi_inverse (- tau) center
      (\<lambda>pos. cutoff pos *
        slp_partial_psi_inverse (- tau) center
          (\<lambda>neg. potential neg *
            slp_right_neumann_iterate n tau center cutoff potential orientation
              neg)
          pos)"
  unfolding slp_right_neumann_iterate_def
  by (rule slp_right_recursive_branch.simps)

theorem slp_left_neumann_iterate_conjugate_eq_right:
  "cnj (slp_left_neumann_iterate n (- tau) center
      (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (potential x))
      (slp_opposite_cauchy_orientation orientation) origin) =
    slp_right_neumann_iterate n tau center cutoff potential orientation origin"
proof -
  let ?terminal =
    "\<lambda>x. slp_cauchy_transform orientation potential x -
      slp_cauchy_transform orientation potential center"
  have conjugate_terminal:
      "(\<lambda>x. cnj (?terminal x)) =
        (\<lambda>x.
          slp_cauchy_transform
              (slp_opposite_cauchy_orientation orientation)
              (\<lambda>y. cnj (potential y)) x -
            slp_cauchy_transform
              (slp_opposite_cauchy_orientation orientation)
              (\<lambda>y. cnj (potential y)) center)"
    by (rule ext) simp
  note branch_conjugate = slp_left_recursive_branch_conjugate_eq_right[
    of n tau center cutoff potential ?terminal origin]
  show ?thesis
    unfolding slp_left_neumann_iterate_def slp_right_neumann_iterate_def
    using branch_conjugate conjugate_terminal by simp
qed

end
