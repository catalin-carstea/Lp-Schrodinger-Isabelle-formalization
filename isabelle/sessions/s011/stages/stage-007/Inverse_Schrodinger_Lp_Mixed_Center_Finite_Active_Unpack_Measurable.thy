theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Active_Unpack_Measurable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Active_Unpack"
begin

section \<open>Measurability of the active coordinate unpack\<close>

theorem slp_mixed_center_finite_active_unpack_measurable [measurable]:
  "(slp_mixed_center_finite_active_unpack ::
      real^((unit + ((('i::finite + 'i) + unit) +
        ('j::finite + 'j))) \<times> bool) \<Rightarrow>
        ('i, 'j) slp_mixed_center_finite_coordinates) \<in>
    measurable lborel lborel"
proof -
  have coordinate_continuous:
      "\<And>index. continuous_on UNIV
        (\<lambda>x :: real^((unit + ((('i + 'i) + unit) +
          ('j + 'j))) \<times> bool).
          slp_complex_as_point
            (slp_complex_family_unpack x index))"
  proof -
    fix index
    have inner: "continuous_on UNIV
        (\<lambda>x :: real^((unit + ((('i + 'i) + unit) +
          ('j + 'j))) \<times> bool).
          Complex (x $ (index, False)) (x $ (index, True)))"
      by (intro continuous_intros)
    show "continuous_on UNIV
        (\<lambda>x :: real^((unit + ((('i + 'i) + unit) +
          ('j + 'j))) \<times> bool).
          slp_complex_as_point
            (slp_complex_family_unpack x index))"
      unfolding slp_complex_family_unpack_def
      by (rule continuous_on_compose2[OF
            slp_complex_as_point_continuous_on inner])
        (rule subset_UNIV)
  qed
  have continuous:
      "continuous_on UNIV
        (slp_mixed_center_finite_active_unpack ::
          real^((unit + ((('i + 'i) + unit) +
            ('j + 'j))) \<times> bool) \<Rightarrow>
            ('i, 'j) slp_mixed_center_finite_coordinates)"
    unfolding slp_mixed_center_finite_active_unpack_def Let_def comp_def
    by (intro continuous_intros coordinate_continuous)
  have borel:
      "(slp_mixed_center_finite_active_unpack ::
          real^((unit + ((('i + 'i) + unit) +
            ('j + 'j))) \<times> bool) \<Rightarrow>
            ('i, 'j) slp_mixed_center_finite_coordinates) \<in>
        borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF continuous])
  show ?thesis
    using borel
    by (simp only: measurable_lborel1 measurable_lborel2)
qed

end
