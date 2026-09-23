theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Residual
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Terminal_Substitution"
begin

section \<open>Finite mixed-center residual after terminal substitution\<close>

definition slp_mixed_center_finite_inserted_coordinates ::
    "slp_point \<Rightarrow>
      ('i::finite, 'j::finite) slp_mixed_center_finite_coordinates \<Rightarrow>
      ('i slp_left_branch_finite_coordinates) \<times>
        ('j slp_left_branch_finite_coordinates)"
where
  "slp_mixed_center_finite_inserted_coordinates center coordinates =
    ((fst coordinates, fst (snd coordinates)),
      (fst coordinates,
        (snd (snd coordinates),
          slp_mixed_center_finite_right_terminal center coordinates)))"

definition slp_mixed_center_finite_residual ::
    "slp_point \<Rightarrow>
      ('i::finite, 'j::finite) slp_mixed_center_finite_coordinates \<Rightarrow> real"
where
  "slp_mixed_center_finite_residual center coordinates =
    slp_mixed_branch_residual
      (fst coordinates)
      (slp_finite_branch_pair_list
        (\<lambda>i. fst (fst (fst (snd coordinates))) $ i)
        (\<lambda>i. snd (fst (fst (snd coordinates))) $ i))
      (snd (fst (snd coordinates)))
      (slp_finite_branch_pair_list
        (\<lambda>i. fst (snd (snd coordinates)) $ i)
        (\<lambda>i. snd (snd (snd coordinates)) $ i))
      (slp_mixed_center_finite_right_terminal center coordinates)"

theorem slp_mixed_center_finite_phase_eq_residual:
  fixes coordinates ::
    "('i::finite, 'j::finite) slp_mixed_center_finite_coordinates"
  shows
    "slp_mixed_branch_phase center
      (fst coordinates)
      (slp_finite_branch_pair_list
        (\<lambda>i. fst (fst (fst (snd coordinates))) $ i)
        (\<lambda>i. snd (fst (fst (snd coordinates))) $ i))
      (snd (fst (snd coordinates)))
      (slp_finite_branch_pair_list
        (\<lambda>i. fst (snd (snd coordinates)) $ i)
        (\<lambda>i. snd (snd (snd coordinates)) $ i))
      (slp_mixed_center_finite_right_terminal center coordinates) =
    slp_mixed_center_finite_residual center coordinates"
proof -
  have phase_split:
      "slp_mixed_branch_phase center
        (fst coordinates)
        (slp_finite_branch_pair_list
          (\<lambda>i. fst (fst (fst (snd coordinates))) $ i)
          (\<lambda>i. snd (fst (fst (snd coordinates))) $ i))
        (snd (fst (snd coordinates)))
        (slp_finite_branch_pair_list
          (\<lambda>i. fst (snd (snd coordinates)) $ i)
          (\<lambda>i. snd (snd (snd coordinates)) $ i))
        (slp_mixed_center_finite_right_terminal center coordinates) =
      slp_center_phase center
        (slp_mixed_branch_center
          (fst coordinates)
          (slp_finite_branch_pair_list
            (\<lambda>i. fst (fst (fst (snd coordinates))) $ i)
            (\<lambda>i. snd (fst (fst (snd coordinates))) $ i))
          (snd (fst (snd coordinates)))
          (slp_finite_branch_pair_list
            (\<lambda>i. fst (snd (snd coordinates)) $ i)
            (\<lambda>i. snd (snd (snd coordinates)) $ i))
          (slp_mixed_center_finite_right_terminal center coordinates)) +
        slp_mixed_branch_residual
          (fst coordinates)
          (slp_finite_branch_pair_list
            (\<lambda>i. fst (fst (fst (snd coordinates))) $ i)
            (\<lambda>i. snd (fst (fst (snd coordinates))) $ i))
          (snd (fst (snd coordinates)))
          (slp_finite_branch_pair_list
            (\<lambda>i. fst (snd (snd coordinates)) $ i)
            (\<lambda>i. snd (snd (snd coordinates)) $ i))
          (slp_mixed_center_finite_right_terminal center coordinates)"
    by (rule slp_mixed_branch_phase_split)
  show ?thesis
    using phase_split
      slp_mixed_center_finite_right_terminal_reconstructs_center[
        where coordinates = coordinates and center = center]
    by (simp add: slp_mixed_center_finite_residual_def slp_center_phase_def)
qed

end
