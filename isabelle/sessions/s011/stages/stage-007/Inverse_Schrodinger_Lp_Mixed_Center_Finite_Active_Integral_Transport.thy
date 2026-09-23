theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Active_Integral_Transport
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Active_Complex_Amplitude_Measurable"
begin

section \<open>Bochner transport to active Cartesian coordinates\<close>

corollary slp_mixed_center_finite_active_integrable_iff:
  fixes F ::
    "real^((unit + ((('i::finite + 'i) + unit) + ('j::finite + 'j)))
      \<times> bool) \<Rightarrow> 'a::{banach, second_countable_topology}"
  assumes F_measurable: "F \<in> borel_measurable lborel"
  shows
    "integrable lborel F \<longleftrightarrow>
      integrable lborel
        (\<lambda>coordinates ::
          ('i, 'j) slp_mixed_center_finite_coordinates.
          F (slp_mixed_center_finite_active_pack coordinates))"
proof -
  have pack_measurable:
      "(slp_mixed_center_finite_active_pack ::
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow>
          real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool))
        \<in> measurable lborel lborel"
    by (rule slp_mixed_center_finite_active_pack_measurable)
  have pack_distr:
      "distr
          (lborel ::
            (('i, 'j) slp_mixed_center_finite_coordinates) measure)
          (lborel ::
            (real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool))
              measure)
          slp_mixed_center_finite_active_pack = lborel"
    by (rule slp_mixed_center_finite_active_pack_distr_lborel)
  show ?thesis
    using integrable_distr_eq[OF pack_measurable F_measurable] pack_distr
    by simp
qed

corollary slp_mixed_center_finite_active_integral:
  fixes F ::
    "real^((unit + ((('i::finite + 'i) + unit) + ('j::finite + 'j)))
      \<times> bool) \<Rightarrow> 'a::{banach, second_countable_topology}"
  assumes F_measurable: "F \<in> borel_measurable lborel"
  shows
    "integral\<^sup>L lborel F =
      integral\<^sup>L lborel
        (\<lambda>coordinates ::
          ('i, 'j) slp_mixed_center_finite_coordinates.
          F (slp_mixed_center_finite_active_pack coordinates))"
proof -
  have pack_measurable:
      "(slp_mixed_center_finite_active_pack ::
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow>
          real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool))
        \<in> measurable lborel lborel"
    by (rule slp_mixed_center_finite_active_pack_measurable)
  have pack_distr:
      "distr
          (lborel ::
            (('i, 'j) slp_mixed_center_finite_coordinates) measure)
          (lborel ::
            (real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool))
              measure)
          slp_mixed_center_finite_active_pack = lborel"
    by (rule slp_mixed_center_finite_active_pack_distr_lborel)
  show ?thesis
    using integral_distr[OF pack_measurable F_measurable] pack_distr
    by simp
qed

end
