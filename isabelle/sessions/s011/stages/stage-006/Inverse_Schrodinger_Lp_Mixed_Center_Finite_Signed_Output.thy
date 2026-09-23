theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Signed_Output
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Signed_Residual"
begin

section \<open>Solved-center finite signed output\<close>

theorem slp_mixed_center_finite_signed_output:
  fixes coordinates ::
    "('i::finite, 'j::finite) slp_mixed_center_finite_coordinates"
  shows
    "slp_signed_output slp_mixed_combined_sign
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
            (slp_mixed_center_finite_right_terminal center coordinates))) =
      slp_point_as_complex center"
proof -
  let ?origin = "fst coordinates"
  let ?left_positive = "fst (fst (fst (snd coordinates)))"
  let ?left_negative = "snd (fst (fst (snd coordinates)))"
  let ?left_terminal = "snd (fst (snd coordinates))"
  let ?right_positive = "fst (snd (snd coordinates))"
  let ?right_negative = "snd (snd (snd coordinates))"
  let ?right_terminal =
    "slp_mixed_center_finite_right_terminal center coordinates"
  let ?left_pairs = "slp_finite_branch_pair_list
    (\<lambda>i. ?left_positive $ i) (\<lambda>i. ?left_negative $ i)"
  let ?right_pairs = "slp_finite_branch_pair_list
    (\<lambda>j. ?right_positive $ j) (\<lambda>j. ?right_negative $ j)"
  let ?left_output = "slp_left_branch_output ?left_pairs ?left_terminal"
  let ?right_output = "slp_right_branch_output ?right_pairs ?right_terminal"
  let ?family = "slp_mixed_combined_family
    (slp_point_as_complex ?origin)
    (\<lambda>i. slp_point_as_complex (?left_positive $ i))
    (\<lambda>i. slp_point_as_complex (?left_negative $ i))
    (slp_point_as_complex ?left_terminal)
    (\<lambda>j. slp_point_as_complex (?right_positive $ j))
    (\<lambda>j. slp_point_as_complex (?right_negative $ j))
    (slp_point_as_complex ?right_terminal)"

  have combined_output:
      "slp_signed_output slp_mixed_combined_sign ?family =
        - slp_point_as_complex ?origin +
          (\<Sum>i\<in>UNIV. slp_point_as_complex (?left_positive $ i) -
            slp_point_as_complex (?left_negative $ i)) +
          slp_point_as_complex ?left_terminal +
          (\<Sum>j\<in>UNIV. slp_point_as_complex (?right_positive $ j) -
            slp_point_as_complex (?right_negative $ j)) +
          slp_point_as_complex ?right_terminal"
    by (rule slp_mixed_combined_output_identity)
  have left_output_complex:
      "slp_point_as_complex ?left_output =
        slp_point_as_complex ?left_terminal +
          (\<Sum>i\<in>UNIV. slp_point_as_complex (?left_positive $ i) -
            slp_point_as_complex (?left_negative $ i))"
    by (rule slp_finite_branch_pair_list_output_as_complex)
  have right_output_complex:
      "slp_point_as_complex ?right_output =
        slp_point_as_complex ?right_terminal +
          (\<Sum>j\<in>UNIV. slp_point_as_complex (?right_positive $ j) -
            slp_point_as_complex (?right_negative $ j))"
    using slp_finite_branch_pair_list_output_as_complex[
      where pos = ?right_positive and neg = ?right_negative
        and terminal = ?right_terminal]
    by (simp only: slp_left_branch_output_eq_right)
  have origin_neg_complex:
      "slp_point_as_complex (- ?origin) = - slp_point_as_complex ?origin"
    by (rule complex_eqI)
      (simp_all only: slp_point_as_complex_def complex.sel
        vector_uminus_component uminus_complex.sel)
  have mixed_output_complex:
      "slp_point_as_complex
          (slp_mixed_branch_center ?origin ?left_pairs ?left_terminal
            ?right_pairs ?right_terminal) =
        - slp_point_as_complex ?origin +
          (slp_point_as_complex ?left_terminal +
            (\<Sum>i\<in>UNIV. slp_point_as_complex (?left_positive $ i) -
              slp_point_as_complex (?left_negative $ i))) +
          (slp_point_as_complex ?right_terminal +
            (\<Sum>j\<in>UNIV. slp_point_as_complex (?right_positive $ j) -
              slp_point_as_complex (?right_negative $ j)))"
    unfolding slp_mixed_branch_center_def
    using left_output_complex right_output_complex
    by (simp only: slp_point_as_complex_add origin_neg_complex)
  have reconstructed:
      "slp_mixed_branch_center ?origin ?left_pairs ?left_terminal
          ?right_pairs ?right_terminal = center"
    by (rule slp_mixed_center_finite_right_terminal_reconstructs_center)
  have center_complex:
      "slp_point_as_complex center =
        - slp_point_as_complex ?origin +
          (slp_point_as_complex ?left_terminal +
            (\<Sum>i\<in>UNIV. slp_point_as_complex (?left_positive $ i) -
              slp_point_as_complex (?left_negative $ i))) +
          (slp_point_as_complex ?right_terminal +
            (\<Sum>j\<in>UNIV. slp_point_as_complex (?right_positive $ j) -
              slp_point_as_complex (?right_negative $ j)))"
  proof -
    have point_equality:
        "slp_point_as_complex
            (slp_mixed_branch_center ?origin ?left_pairs ?left_terminal
              ?right_pairs ?right_terminal) =
          slp_point_as_complex center"
      by (rule arg_cong[OF reconstructed])
    show ?thesis
      by (rule HOL.trans[OF point_equality[symmetric] mixed_output_complex])
  qed
  have reordered:
      "- slp_point_as_complex ?origin +
          (\<Sum>i\<in>UNIV. slp_point_as_complex (?left_positive $ i) -
            slp_point_as_complex (?left_negative $ i)) +
          slp_point_as_complex ?left_terminal +
          (\<Sum>j\<in>UNIV. slp_point_as_complex (?right_positive $ j) -
            slp_point_as_complex (?right_negative $ j)) +
          slp_point_as_complex ?right_terminal =
        - slp_point_as_complex ?origin +
          (slp_point_as_complex ?left_terminal +
            (\<Sum>i\<in>UNIV. slp_point_as_complex (?left_positive $ i) -
              slp_point_as_complex (?left_negative $ i))) +
          (slp_point_as_complex ?right_terminal +
            (\<Sum>j\<in>UNIV. slp_point_as_complex (?right_positive $ j) -
              slp_point_as_complex (?right_negative $ j)))"
    by (simp only: add.assoc add.left_commute add.commute)
  show ?thesis
    by (rule HOL.trans[OF HOL.trans[OF combined_output reordered]
          center_complex[symmetric]])
qed

end
