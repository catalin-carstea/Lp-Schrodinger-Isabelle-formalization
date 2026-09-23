theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Active_Pack
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Signed_Output"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_Packed_Transport"
begin

section \<open>Solved-center finite active-tail coordinates\<close>

definition slp_mixed_center_finite_active_pack ::
    "('i::finite, 'j::finite) slp_mixed_center_finite_coordinates \<Rightarrow>
      real^((unit + (((('i + 'i) + unit) + ('j + 'j)))) \<times> bool)"
where
  "slp_mixed_center_finite_active_pack coordinates =
    slp_complex_family_pack
      (\<lambda>tail. case tail of
        Inl _ \<Rightarrow> slp_point_as_complex (fst coordinates)
      | Inr branches \<Rightarrow> (case branches of
          Inl left \<Rightarrow> (case left of
              Inl side \<Rightarrow> (case side of
                  Inl i \<Rightarrow> slp_point_as_complex
                    (fst (fst (fst (snd coordinates))) $ i)
                | Inr i \<Rightarrow> slp_point_as_complex
                    (snd (fst (fst (snd coordinates))) $ i))
            | Inr _ \<Rightarrow> slp_point_as_complex
                (snd (fst (snd coordinates))))
        | Inr side \<Rightarrow> (case side of
              Inl j \<Rightarrow> slp_point_as_complex
                (fst (snd (snd coordinates)) $ j)
            | Inr j \<Rightarrow> slp_point_as_complex
                (snd (snd (snd coordinates)) $ j))))"

lemma slp_mixed_center_finite_active_pack_as_combined_tail:
  fixes coordinates ::
    "('i::finite, 'j::finite) slp_mixed_center_finite_coordinates"
  shows
    "slp_complex_family_unpack
        (slp_mixed_center_finite_active_pack coordinates) =
      (\<lambda>tail. slp_mixed_combined_family
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
          (slp_mixed_center_finite_right_terminal center coordinates))
        (Inr tail))"
  unfolding slp_mixed_center_finite_active_pack_def
  apply (simp only: slp_complex_family_unpack_pack)
  apply (rule ext)
  subgoal for tail
    by (cases tail)
      (simp_all only: slp_mixed_combined_family_def sum.case
        split: sum.splits)
  done

theorem slp_mixed_center_finite_active_pack_reconstructs_family:
  fixes coordinates ::
    "('i::finite, 'j::finite) slp_mixed_center_finite_coordinates"
  shows
    "slp_signed_coordinate_join slp_mixed_combined_sign
        (slp_point_as_complex center,
          slp_complex_family_unpack
            (slp_mixed_center_finite_active_pack coordinates)) =
      slp_mixed_combined_family
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
          (slp_mixed_center_finite_right_terminal center coordinates))"
proof -
  let ?family = "slp_mixed_combined_family
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
      (slp_mixed_center_finite_right_terminal center coordinates))"
  have signed_output:
      "slp_signed_output slp_mixed_combined_sign ?family =
        slp_point_as_complex center"
    by (rule slp_mixed_center_finite_signed_output)
  have tail:
      "slp_complex_family_unpack
          (slp_mixed_center_finite_active_pack coordinates) =
        (\<lambda>i. ?family (Inr i))"
    by (rule slp_mixed_center_finite_active_pack_as_combined_tail)
  have split:
      "slp_signed_coordinate_split slp_mixed_combined_sign ?family =
        (slp_point_as_complex center,
          slp_complex_family_unpack
            (slp_mixed_center_finite_active_pack coordinates))"
    unfolding slp_signed_coordinate_split_def
    using signed_output tail
    by (simp only: prod.inject)
  have distinguished_nonzero:
      "slp_mixed_combined_sign (Inl ()) \<noteq> 0"
    by (simp add: slp_mixed_combined_sign_def)
  have joined:
      "slp_signed_coordinate_join slp_mixed_combined_sign
          (slp_signed_coordinate_split slp_mixed_combined_sign ?family) =
        ?family"
    by (rule slp_signed_coordinate_join_split[
          where epsilon = slp_mixed_combined_sign and y = ?family,
          OF distinguished_nonzero])
  show ?thesis
    using joined
    by (simp only: split)
qed

end
