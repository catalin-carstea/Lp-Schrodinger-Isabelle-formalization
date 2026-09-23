theory Inverse_Schrodinger_Lp_Born_Block_Transport
  imports
    Inverse_Schrodinger_Lp_Double_Localized_Cauchy_Raw
    Inverse_Schrodinger_Lp_Affine_Output_Transport
begin

section \<open>Almost-everywhere transport into branch-block coordinates\<close>

lemma slp_AE_reflect_translate:
  fixes P :: "slp_point \<Rightarrow> bool"
  assumes P_measurable: "Measurable.pred lborel P"
    and P_AE: "AE x in lborel. P x"
  shows "AE x in lborel. P (origin - x)"
proof -
  let ?T = "\<lambda>x :: slp_point. origin + (-1 :: real) *\<^sub>R x"
  have T_eq: "?T = (-) origin"
    by (rule ext) simp
  have T_measurable: "?T \<in> measurable lborel borel"
    by measurable
  have P_borel_measurable: "Measurable.pred borel P"
    using P_measurable by simp
  have P_borel_set: "{x \<in> space borel. P x} \<in> sets borel"
    using P_borel_measurable by simp
  have distr_eq:
      "distr lborel borel ?T = (lborel :: slp_point measure)"
  proof -
    have density_identity:
        "(lborel :: slp_point measure) =
          density (distr lborel borel ?T)
            (\<lambda>_. abs (-1 :: real) ^ DIM(slp_point))"
      by (rule lborel_affine) simp
    have density_one:
        "density (distr lborel borel ?T) (\<lambda>_. 1) =
          distr lborel borel ?T"
      by (rule density_1)
    show ?thesis
      using density_identity density_one by simp
  qed
  have reflected_distr_eq:
      "distr lborel borel ((-) origin) = (lborel :: slp_point measure)"
    using distr_eq T_eq by simp
  have P_distr: "AE x in distr lborel borel ?T. P x"
  proof (subst T_eq)
    show "AE x in distr lborel borel ((-) origin). P x"
    proof (subst reflected_distr_eq)
      show "AE x in lborel. P x"
        by (rule P_AE)
    qed
  qed
  have P_composed: "AE x in lborel. P (?T x)"
    using AE_distr_iff[OF T_measurable P_borel_set]
      P_distr by blast
  show ?thesis
    using P_composed by simp
qed

lemma slp_double_localized_cauchy_branch_inner_translate:
  "(\<integral>\<^sup>+ pos_point.
      ennreal
        (slp_localized_cauchy_kernel R (origin - pos_point) *
          slp_localized_cauchy_kernel R (pos_point - neg_point))
      \<partial>lborel) =
    (\<integral>\<^sup>+ y.
      ennreal
        (slp_localized_cauchy_kernel R y *
          slp_localized_cauchy_kernel R ((origin - neg_point) - y))
      \<partial>lborel)"
proof -
  let ?f = "\<lambda>pos_point.
    ennreal
      (slp_localized_cauchy_kernel R (origin - pos_point) *
        slp_localized_cauchy_kernel R (pos_point - neg_point))"
  note [measurable] = slp_localized_cauchy_kernel_borel_measurable
  have f_measurable: "?f \<in> borel_measurable lborel"
    by measurable
  have invariant:
      "(\<integral>\<^sup>+ y. ?f (neg_point + y) \<partial>lborel) =
        (\<integral>\<^sup>+ pos_point. ?f pos_point \<partial>lborel)"
    by (rule slp_nn_integral_translate[OF f_measurable])
  show ?thesis
    using invariant
    by (simp add: algebra_simps mult.commute)
qed

corollary slp_double_localized_cauchy_branch_inner_AE_nn_integral:
  "AE neg_point in lborel.
    (\<integral>\<^sup>+ pos_point.
      ennreal
        (slp_localized_cauchy_kernel R (origin - pos_point) *
          slp_localized_cauchy_kernel R (pos_point - neg_point))
      \<partial>lborel) =
      ennreal
        (slp_double_localized_cauchy_kernel R (origin - neg_point))"
proof -
  note [measurable] = slp_localized_cauchy_kernel_borel_measurable
  let ?raw = "\<lambda>x.
    \<integral>\<^sup>+ y.
      ennreal
        (slp_localized_cauchy_kernel R y *
          slp_localized_cauchy_kernel R (x - y))
      \<partial>lborel"
  let ?double = "\<lambda>x. ennreal (slp_double_localized_cauchy_kernel R x)"
  have raw_measurable: "?raw \<in> borel_measurable lborel"
    by measurable
  have double_measurable: "?double \<in> borel_measurable lborel"
    using slp_double_localized_cauchy_kernel_integrable[of R]
    by measurable
  have predicate_measurable:
      "Measurable.pred lborel (\<lambda>x. ?raw x = ?double x)"
    using raw_measurable double_measurable by measurable
  have raw_AE: "AE x in lborel. ?raw x = ?double x"
    by (rule slp_double_localized_cauchy_raw_AE_nn_integral)
  have shifted_AE:
      "AE neg_point in lborel.
        ?raw (origin - neg_point) = ?double (origin - neg_point)"
    by (rule slp_AE_reflect_translate[OF predicate_measurable raw_AE])
  show ?thesis
    using shifted_AE
  proof eventually_elim
    fix neg_point :: slp_point
    assume shifted:
        "?raw (origin - neg_point) = ?double (origin - neg_point)"
    have transported:
        "(\<integral>\<^sup>+ pos_point.
          ennreal
            (slp_localized_cauchy_kernel R (origin - pos_point) *
              slp_localized_cauchy_kernel R (pos_point - neg_point))
          \<partial>lborel) = ?raw (origin - neg_point)"
      by (rule slp_double_localized_cauchy_branch_inner_translate)
    show "(\<integral>\<^sup>+ pos_point.
        ennreal
          (slp_localized_cauchy_kernel R (origin - pos_point) *
            slp_localized_cauchy_kernel R (pos_point - neg_point))
        \<partial>lborel) =
        ennreal
          (slp_double_localized_cauchy_kernel R (origin - neg_point))"
      using transported shifted by simp
  qed
qed

end
