theory Inverse_Schrodinger_Lp_Qone_Finite_Packed_Transport
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Qone_Inner_Active_Transport"
begin

section \<open>Finite one-sided coordinates as packed QONE coordinates\<close>

definition slp_qone_finite_stage_pack ::
    "(slp_point \<times>
      (((slp_point^'i::finite) \<times> (slp_point^'i)) \<times> slp_point)) \<Rightarrow>
      (real^bool) \<times> (real^((unit + ('i + 'i)) \<times> bool))"
where
  "slp_qone_finite_stage_pack =
    (\<lambda>(root, inner).
      (slp_complex_coordinate_pack (slp_point_as_complex root),
        slp_qone_inner_active_pack inner))"

lemma slp_qone_finite_stage_pack_measurable:
  "(slp_qone_finite_stage_pack ::
      (slp_point \<times>
        (((slp_point^'i::finite) \<times> (slp_point^'i)) \<times> slp_point)) \<Rightarrow>
        (real^bool) \<times> (real^((unit + ('i + 'i)) \<times> bool)))
    \<in> measurable
      (lborel \<Otimes>\<^sub>M ((lborel \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M lborel))
      (lborel \<Otimes>\<^sub>M lborel)"
proof -
  let ?M =
    "(lborel :: slp_point measure) \<Otimes>\<^sub>M
      (((lborel :: (slp_point^'i) measure) \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M
        (lborel :: slp_point measure))"
  have root:
    "(\<lambda>x. slp_complex_coordinate_pack
        (slp_point_as_complex (fst x)))
      \<in> measurable ?M (lborel :: (real^bool) measure)"
    using measurable_compose[OF measurable_fst slp_point_boolean_map_measurable] .
  have active:
    "(\<lambda>x. slp_qone_inner_active_pack (snd x))
      \<in> measurable ?M
        (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure)"
    using measurable_compose[
      OF measurable_snd slp_qone_inner_active_pack_measurable] .
  have paired:
    "(\<lambda>x.
      (slp_complex_coordinate_pack (slp_point_as_complex (fst x)),
        slp_qone_inner_active_pack (snd x)))
      \<in> measurable ?M
        ((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
          (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))"
    by (rule measurable_Pair[OF root active])
  show ?thesis
    using paired
    by (simp only: slp_qone_finite_stage_pack_def measurable_split_conv)
qed

theorem slp_qone_finite_stage_pack_distr_lborel:
  "distr
      ((lborel :: slp_point measure) \<Otimes>\<^sub>M
        (((lborel :: (slp_point^'i::finite) measure) \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M
          (lborel :: slp_point measure)))
      ((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
        (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))
      slp_qone_finite_stage_pack =
    (lborel :: (real^bool) measure) \<Otimes>\<^sub>M
      (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure)"
proof -
  have target_sigma:
    "sigma_finite_measure
      (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure)"
    by standard
  show ?thesis
    unfolding slp_qone_finite_stage_pack_def
    by (rule slp_distr_pair_map_eq[
          OF slp_point_boolean_map_measurable
             slp_qone_inner_active_pack_measurable
             slp_point_boolean_distr_lborel
             slp_qone_inner_active_pack_distr_lborel
             target_sigma])
qed

end
