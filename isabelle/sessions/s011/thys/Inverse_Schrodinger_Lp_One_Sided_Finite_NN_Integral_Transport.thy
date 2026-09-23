theory Inverse_Schrodinger_Lp_One_Sided_Finite_NN_Integral_Transport
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_Integral_Transport"
begin

section \<open>Nonnegative transport between finite and packed coordinates\<close>

corollary slp_one_sided_finite_packed_nn_integral:
  fixes F :: "((real^bool) \<times>
      (real^((unit + ('i::finite + 'i)) \<times> bool))) \<Rightarrow> ennreal"
  assumes F_measurable: "F \<in> borel_measurable lborel"
  shows "(\<integral>\<^sup>+ x. F x \<partial>lborel) =
    (\<integral>\<^sup>+ x. F (slp_one_sided_finite_to_packed_coordinates x)
      \<partial>(lborel :: ('i slp_left_branch_finite_coordinates) measure))"
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
  have F_measurable_distr:
      "F \<in> borel_measurable
        (distr
          (lborel :: ('i slp_left_branch_finite_coordinates) measure)
          (lborel :: ((real^bool) \<times>
            (real^((unit + ('i + 'i)) \<times> bool))) measure)
          slp_one_sided_finite_to_packed_coordinates)"
    using F_measurable pack_distr by simp
  have transported:
      "(\<integral>\<^sup>+ x. F x
          \<partial>distr
            (lborel :: ('i slp_left_branch_finite_coordinates) measure)
            (lborel :: ((real^bool) \<times>
              (real^((unit + ('i + 'i)) \<times> bool))) measure)
            slp_one_sided_finite_to_packed_coordinates) =
        (\<integral>\<^sup>+ x. F (slp_one_sided_finite_to_packed_coordinates x)
          \<partial>(lborel :: ('i slp_left_branch_finite_coordinates) measure))"
    by (rule nn_integral_distr[OF pack_measurable F_measurable_distr])
  show ?thesis
    using transported pack_distr by simp
qed

end
