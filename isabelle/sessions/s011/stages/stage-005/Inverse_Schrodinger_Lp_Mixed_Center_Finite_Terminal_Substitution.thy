theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Terminal_Substitution
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Parameterized_Real_Phase_Fiber_Integral"
begin

section \<open>Finite mixed-center terminal substitution\<close>

type_synonym ('i, 'j) slp_mixed_center_finite_coordinates =
  "slp_point \<times>
    ((((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) \<times>
      ((slp_point^'j) \<times> (slp_point^'j)))"

definition slp_mixed_center_finite_right_terminal ::
    "slp_point \<Rightarrow>
      ('i::finite, 'j::finite) slp_mixed_center_finite_coordinates \<Rightarrow>
      slp_point"
where
  "slp_mixed_center_finite_right_terminal center coordinates =
    center + fst coordinates -
      slp_left_branch_output
        (slp_finite_branch_pair_list
          (\<lambda>i. fst (fst (fst (snd coordinates))) $ i)
          (\<lambda>i. snd (fst (fst (snd coordinates))) $ i))
        (snd (fst (snd coordinates))) -
      slp_right_branch_output
        (slp_finite_branch_pair_list
          (\<lambda>i. fst (snd (snd coordinates)) $ i)
          (\<lambda>i. snd (snd (snd coordinates)) $ i))
        0"

theorem slp_mixed_center_finite_right_terminal_reconstructs_center:
  fixes coordinates ::
    "('i::finite, 'j::finite) slp_mixed_center_finite_coordinates"
  shows
    "slp_mixed_branch_center
      (fst coordinates)
      (slp_finite_branch_pair_list
        (\<lambda>i. fst (fst (fst (snd coordinates))) $ i)
        (\<lambda>i. snd (fst (fst (snd coordinates))) $ i))
      (snd (fst (snd coordinates)))
      (slp_finite_branch_pair_list
        (\<lambda>i. fst (snd (snd coordinates)) $ i)
        (\<lambda>i. snd (snd (snd coordinates)) $ i))
      (slp_mixed_center_finite_right_terminal center coordinates) =
    center"
  unfolding slp_mixed_branch_center_def
    slp_mixed_center_finite_right_terminal_def
    slp_right_branch_output_def
  by (simp add: algebra_simps)

end
