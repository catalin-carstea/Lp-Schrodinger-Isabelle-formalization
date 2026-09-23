theory Inverse_Schrodinger_Lp_Nested_Boolean_Family_Flatten
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Point_Family_Boolean_Transport"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Finite_Product_Flatten"
begin

section \<open>Flattening nested Boolean Cartesian coordinates\<close>

definition slp_nested_boolean_family_flatten ::
    "((real^bool)^'i::finite) \<Rightarrow> real^('i \<times> bool)"
where
  "slp_nested_boolean_family_flatten x =
    (\<chi> ib. x $ fst ib $ snd ib)"

lemma slp_nested_boolean_family_flatten_linear:
  "linear (slp_nested_boolean_family_flatten ::
      ((real^bool)^'i::finite) \<Rightarrow> real^('i \<times> bool))"
  unfolding slp_nested_boolean_family_flatten_def
  by (rule linearI) (simp_all add: vec_eq_iff)

lemma slp_nested_boolean_family_flatten_measurable:
  "(slp_nested_boolean_family_flatten ::
      ((real^bool)^'i::finite) \<Rightarrow> real^('i \<times> bool))
    \<in> measurable lborel lborel"
proof -
  have bounded:
    "bounded_linear (slp_nested_boolean_family_flatten ::
      ((real^bool)^'i) \<Rightarrow> real^('i \<times> bool))"
    using slp_nested_boolean_family_flatten_linear
    by (simp add: linear_conv_bounded_linear)
  have continuous:
    "continuous_on UNIV (slp_nested_boolean_family_flatten ::
      ((real^bool)^'i) \<Rightarrow> real^('i \<times> bool))"
    by (rule linear_continuous_on[OF bounded])
  have borel:
    "(slp_nested_boolean_family_flatten ::
      ((real^bool)^'i) \<Rightarrow> real^('i \<times> bool))
      \<in> measurable borel borel"
    by (rule borel_measurable_continuous_onI[OF continuous])
  show ?thesis
    using borel
    by (simp only: measurable_lborel1 measurable_lborel2)
qed

end
