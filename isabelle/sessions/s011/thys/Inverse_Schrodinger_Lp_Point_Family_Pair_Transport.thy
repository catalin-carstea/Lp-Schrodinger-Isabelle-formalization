theory Inverse_Schrodinger_Lp_Point_Family_Pair_Transport
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Product_Map_Transport"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Point_Family_Flat_Transport"
begin

section \<open>Exact transport of two planar point families\<close>

theorem slp_point_family_pair_flat_pack_distr_lborel:
  "distr
      ((lborel :: (slp_point^'i::finite) measure) \<Otimes>\<^sub>M
        (lborel :: (slp_point^'i) measure))
      ((lborel :: (real^('i \<times> bool)) measure) \<Otimes>\<^sub>M
        (lborel :: (real^('i \<times> bool)) measure))
      (\<lambda>(positive, negative).
        (slp_point_family_boolean_flat_pack positive,
          slp_point_family_boolean_flat_pack negative)) =
    (lborel :: (real^('i \<times> bool)) measure) \<Otimes>\<^sub>M
      (lborel :: (real^('i \<times> bool)) measure)"
proof -
  have target_sigma:
    "sigma_finite_measure (lborel :: (real^('i \<times> bool)) measure)"
    by standard
  show ?thesis
    by (rule slp_distr_pair_map_eq[
          OF slp_point_family_boolean_flat_pack_measurable
             slp_point_family_boolean_flat_pack_measurable
             slp_point_family_boolean_flat_pack_distr_lborel
             slp_point_family_boolean_flat_pack_distr_lborel
             target_sigma])
qed

end
