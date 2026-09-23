theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Active_Residual
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Active_Transport"
begin

section \<open>Solved-center residual on active Cartesian coordinates\<close>

definition slp_mixed_center_finite_active_residual ::
    "slp_point \<Rightarrow>
      real^((unit + ((('i::finite + 'i) + unit) + ('j::finite + 'j)))
        \<times> bool) \<Rightarrow> real"
where
  "slp_mixed_center_finite_active_residual center x =
    slp_signed_residual slp_mixed_combined_sign
      (slp_signed_coordinate_join slp_mixed_combined_sign
        (slp_point_as_complex center, slp_complex_family_unpack x))"

theorem slp_mixed_center_finite_active_residual_pack:
  fixes coordinates ::
    "('i::finite, 'j::finite) slp_mixed_center_finite_coordinates"
  shows
    "slp_mixed_center_finite_active_residual center
        (slp_mixed_center_finite_active_pack coordinates) =
      slp_mixed_center_finite_residual center coordinates"
proof -
  have reconstruction:
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
    by (rule slp_mixed_center_finite_active_pack_reconstructs_family)
  have signed_form:
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
    by (rule slp_mixed_center_finite_residual_as_signed)
  show ?thesis
    unfolding slp_mixed_center_finite_active_residual_def
    by (simp only: reconstruction signed_form)
qed

lemma slp_mixed_center_finite_active_residual_measurable:
  "(slp_mixed_center_finite_active_residual center ::
      real^((unit + ((('i::finite + 'i) + unit) + ('j::finite + 'j)))
        \<times> bool) \<Rightarrow> real) \<in>
    borel_measurable lborel"
proof -
  let ?A =
    "lborel ::
      (real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool))
        measure"
  let ?C = "lborel :: (real^bool) measure"
  let ?P =
    "lborel ::
      ((real^bool) \<times>
        (real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)))
        measure"
  have distinguished_sign:
      "slp_mixed_combined_sign
          (Inl () ::
            unit + (unit + ((('i + 'i) + unit) + ('j + 'j)))) = -1 \<or>
        slp_mixed_combined_sign
          (Inl () ::
            unit + (unit + ((('i + 'i) + unit) + ('j + 'j)))) = 1"
    by (rule slp_mixed_combined_sign_values)
  have residual_measurable:
      "(\<lambda>cu. slp_signed_residual slp_mixed_combined_sign
        (slp_signed_coordinate_join slp_mixed_combined_sign
          (slp_complex_coordinate_unpack (fst cu),
            slp_complex_family_unpack (snd cu)))) \<in>
        borel_measurable ?P"
    by (rule slp_signed_residual_product_measurable[
          where epsilon =
            "slp_mixed_combined_sign ::
              (unit + (unit + ((('i + 'i) + unit) + ('j + 'j))))
                \<Rightarrow> real"
          and 'i = "unit + ((('i + 'i) + unit) + ('j + 'j))"])
      (rule distinguished_sign)
  have center_in_space:
      "slp_complex_coordinate_pack (slp_point_as_complex center) \<in>
        space ?C"
    by (simp only: space_lborel space_borel UNIV_I)
  have center_measurable:
      "(\<lambda>_ ::
          real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool).
          slp_complex_coordinate_pack (slp_point_as_complex center)) \<in>
        measurable ?A ?C"
    by (rule measurable_const[OF center_in_space])
  have active_measurable:
      "(\<lambda>x ::
          real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool). x)
        \<in> measurable ?A ?A"
    by (rule measurable_id)
  have pair_measurable:
      "(\<lambda>x ::
          real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool).
          (slp_complex_coordinate_pack (slp_point_as_complex center), x)) \<in>
        measurable ?A ?P"
    using measurable_Pair[OF center_measurable active_measurable]
    by (simp only: lborel_prod)
  have composed:
      "((\<lambda>cu. slp_signed_residual slp_mixed_combined_sign
          (slp_signed_coordinate_join slp_mixed_combined_sign
            (slp_complex_coordinate_unpack (fst cu),
              slp_complex_family_unpack (snd cu)))) \<circ>
        (\<lambda>x.
          (slp_complex_coordinate_pack (slp_point_as_complex center), x)))
        \<in> borel_measurable ?A"
    using measurable_compose[OF pair_measurable residual_measurable]
    by (simp only: comp_def)
  have active_eq:
      "(slp_mixed_center_finite_active_residual center ::
          real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
            \<Rightarrow> real) =
        ((\<lambda>cu. slp_signed_residual slp_mixed_combined_sign
            (slp_signed_coordinate_join slp_mixed_combined_sign
              (slp_complex_coordinate_unpack (fst cu),
                slp_complex_family_unpack (snd cu)))) \<circ>
          (\<lambda>x.
            (slp_complex_coordinate_pack (slp_point_as_complex center), x)))"
  proof (rule ext)
    fix x ::
      "real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)"
    show
      "slp_mixed_center_finite_active_residual center x =
        (((\<lambda>cu. slp_signed_residual slp_mixed_combined_sign
            (slp_signed_coordinate_join slp_mixed_combined_sign
              (slp_complex_coordinate_unpack (fst cu),
                slp_complex_family_unpack (snd cu)))) \<circ>
          (\<lambda>x.
            (slp_complex_coordinate_pack (slp_point_as_complex center), x))) x)"
      unfolding slp_mixed_center_finite_active_residual_def
      by (simp only: comp_apply fst_conv snd_conv
          slp_complex_coordinate_unpack_pack)
  qed
  show ?thesis
    using composed
    by (simp only: active_eq)
qed

end
