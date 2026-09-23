theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Signed_Residual
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Mixed_Branch_Finite_Signed_Residual"
begin

section \<open>Solved-center finite residual in the combined signed family\<close>

theorem slp_mixed_center_finite_residual_as_signed:
  fixes coordinates ::
    "('i::finite, 'j::finite) slp_mixed_center_finite_coordinates"
  shows
    "slp_mixed_center_finite_residual center coordinates =
      slp_signed_residual slp_mixed_combined_sign
        (slp_mixed_combined_family
          (slp_point_as_complex (fst coordinates))
          (\<lambda>i. slp_point_as_complex
            (fst (fst (fst (snd coordinates))) $ i))
          (\<lambda>i. slp_point_as_complex
            (snd (fst (fst (snd coordinates))) $ i))
          (slp_point_as_complex (snd (fst (snd coordinates))))
          (\<lambda>j. slp_point_as_complex
            (fst (snd (snd coordinates)) $ j))
          (\<lambda>j. slp_point_as_complex
            (snd (snd (snd coordinates)) $ j))
          (slp_point_as_complex
            (slp_mixed_center_finite_right_terminal center coordinates)))"
  unfolding slp_mixed_center_finite_residual_def
  by (rule slp_mixed_branch_finite_residual_as_signed)

end
