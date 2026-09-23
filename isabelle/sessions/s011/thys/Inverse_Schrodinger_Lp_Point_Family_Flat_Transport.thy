theory Inverse_Schrodinger_Lp_Point_Family_Flat_Transport
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Nested_Boolean_Family_Lebesgue_Transport"
begin

section \<open>Finite planar families in flat scalar coordinates\<close>

definition slp_point_family_boolean_flat_pack ::
    "(slp_point^'i::finite) \<Rightarrow> real^('i \<times> bool)"
where
  "slp_point_family_boolean_flat_pack =
    slp_nested_boolean_family_flatten \<circ>
      slp_point_family_boolean_nested_pack"

lemma slp_point_family_boolean_flat_pack_measurable:
  "(slp_point_family_boolean_flat_pack ::
      (slp_point^'i::finite) \<Rightarrow> real^('i \<times> bool))
    \<in> measurable lborel lborel"
proof -
  have nested:
    "(slp_point_family_boolean_nested_pack ::
      (slp_point^'i) \<Rightarrow> ((real^bool)^'i))
      \<in> measurable lborel lborel"
    using slp_point_family_boolean_nested_pack_measurable
    by (simp only: measurable_lborel1 measurable_lborel2)
  have composed:
    "(slp_nested_boolean_family_flatten \<circ>
        slp_point_family_boolean_nested_pack ::
      (slp_point^'i) \<Rightarrow> real^('i \<times> bool))
      \<in> measurable lborel lborel"
    using measurable_compose[
      OF nested slp_nested_boolean_family_flatten_measurable]
    by (simp only: comp_def)
  show ?thesis
    using composed
    by (simp only: slp_point_family_boolean_flat_pack_def)
qed

theorem slp_point_family_boolean_flat_pack_distr_lborel:
  "distr
      (lborel :: (slp_point^'i::finite) measure)
      (lborel :: (real^('i \<times> bool)) measure)
      slp_point_family_boolean_flat_pack =
    (lborel :: (real^('i \<times> bool)) measure)"
proof -
  have nested:
    "(slp_point_family_boolean_nested_pack ::
      (slp_point^'i) \<Rightarrow> ((real^bool)^'i))
      \<in> measurable lborel lborel"
    using slp_point_family_boolean_nested_pack_measurable
    by (simp only: measurable_lborel1 measurable_lborel2)
  have flatten:
    "(slp_nested_boolean_family_flatten ::
      ((real^bool)^'i) \<Rightarrow> real^('i \<times> bool))
      \<in> measurable lborel lborel"
    by (rule slp_nested_boolean_family_flatten_measurable)
  have
    "distr
        (lborel :: (slp_point^'i) measure)
        (lborel :: (real^('i \<times> bool)) measure)
        slp_point_family_boolean_flat_pack =
      distr
        (lborel :: (slp_point^'i) measure)
        (lborel :: (real^('i \<times> bool)) measure)
        (slp_nested_boolean_family_flatten \<circ>
          slp_point_family_boolean_nested_pack)"
    by (simp only: slp_point_family_boolean_flat_pack_def)
  also have "... =
      distr
        (distr
          (lborel :: (slp_point^'i) measure)
          (lborel :: ((real^bool)^'i) measure)
          slp_point_family_boolean_nested_pack)
        (lborel :: (real^('i \<times> bool)) measure)
        slp_nested_boolean_family_flatten"
    by (rule distr_distr[OF flatten nested, symmetric])
  also have "... =
      distr
        (lborel :: ((real^bool)^'i) measure)
        (lborel :: (real^('i \<times> bool)) measure)
        slp_nested_boolean_family_flatten"
    by (simp only: slp_point_family_boolean_nested_distr_lborel)
  also have "... = (lborel :: (real^('i \<times> bool)) measure)"
    by (rule slp_nested_boolean_family_flatten_distr_lborel)
  finally show ?thesis .
qed

end
