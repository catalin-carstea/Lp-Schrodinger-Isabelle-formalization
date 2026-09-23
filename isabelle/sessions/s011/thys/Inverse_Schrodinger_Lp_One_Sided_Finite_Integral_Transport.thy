theory Inverse_Schrodinger_Lp_One_Sided_Finite_Integral_Transport
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_Packed_Transport"
begin

section \<open>Bochner transport between finite and packed one-sided coordinates\<close>

corollary slp_one_sided_finite_packed_integrable_iff:
  fixes F :: "((real^bool) \<times>
      (real^((unit + ('i::finite + 'i)) \<times> bool))) \<Rightarrow>
        'a::{banach, second_countable_topology}"
  assumes F_measurable: "F \<in> borel_measurable lborel"
  shows "integrable lborel F \<longleftrightarrow>
    integrable lborel
      (\<lambda>x. F (slp_one_sided_finite_to_packed_coordinates x))"
proof -
  have pack_measurable:
      "(slp_one_sided_finite_to_packed_coordinates ::
          'i slp_left_branch_finite_coordinates \<Rightarrow>
            (real^bool) \<times>
              (real^((unit + ('i + 'i)) \<times> bool)))
        \<in> measurable lborel lborel"
    using slp_one_sided_finite_to_packed_coordinates_measurable
    by (simp only: lborel_prod)
  have pack_distr:
      "distr
          (lborel :: ('i slp_left_branch_finite_coordinates) measure)
          (lborel :: ((real^bool) \<times>
            (real^((unit + ('i + 'i)) \<times> bool))) measure)
          slp_one_sided_finite_to_packed_coordinates = lborel"
    using slp_one_sided_finite_to_packed_coordinates_distr_lborel[
      where 'i = 'i]
    by (simp only: lborel_prod)
  show ?thesis
    using integrable_distr_eq[OF pack_measurable F_measurable] pack_distr
    by simp
qed

corollary slp_one_sided_finite_packed_integral:
  fixes F :: "((real^bool) \<times>
      (real^((unit + ('i::finite + 'i)) \<times> bool))) \<Rightarrow>
        'a::{banach, second_countable_topology}"
  assumes F_measurable: "F \<in> borel_measurable lborel"
  shows "integral\<^sup>L lborel F =
    integral\<^sup>L lborel
      (\<lambda>x. F (slp_one_sided_finite_to_packed_coordinates x))"
proof -
  have pack_measurable:
      "(slp_one_sided_finite_to_packed_coordinates ::
          'i slp_left_branch_finite_coordinates \<Rightarrow>
            (real^bool) \<times>
              (real^((unit + ('i + 'i)) \<times> bool)))
        \<in> measurable lborel lborel"
    using slp_one_sided_finite_to_packed_coordinates_measurable
    by (simp only: lborel_prod)
  have pack_distr:
      "distr
          (lborel :: ('i slp_left_branch_finite_coordinates) measure)
          (lborel :: ((real^bool) \<times>
            (real^((unit + ('i + 'i)) \<times> bool))) measure)
          slp_one_sided_finite_to_packed_coordinates = lborel"
    using slp_one_sided_finite_to_packed_coordinates_distr_lborel[
      where 'i = 'i]
    by (simp only: lborel_prod)
  show ?thesis
    using integral_distr[OF pack_measurable F_measurable] pack_distr
    by simp
qed

end
