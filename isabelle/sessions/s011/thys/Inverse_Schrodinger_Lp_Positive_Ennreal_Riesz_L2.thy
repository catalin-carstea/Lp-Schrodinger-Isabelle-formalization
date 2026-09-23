theory Inverse_Schrodinger_Lp_Positive_Ennreal_Riesz_L2
  imports Inverse_Schrodinger_Lp_Positive_Ennreal_Complex_Lp
    Inverse_Schrodinger_Lp_Born_One_Sided_Riesz_L2
begin

section \<open>Compact localized Riesz control for positive densities\<close>

context aim_planar_riesz_hls
begin

theorem slp_positive_ennreal_localized_riesz_l2_compact:
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and F_lp: "slp_positive_ennreal_lp_on_plane p F"
    and F_support: "bounded {x. F x \<noteq> 0}"
  defines "f \<equiv> \<lambda>x. of_real (enn2real (F x)) :: complex"
  shows
    "(AE z in lborel.
        (\<integral>\<^sup>+ y.
          ennreal (slp_localized_cauchy_kernel R (y - z)) * F y
          \<partial>lborel) =
        ennreal (slp_localized_riesz_potential R f z)) \<and>
      aim_real_lp_on_plane 2 (slp_localized_riesz_potential R f) \<and>
      bounded {z. slp_localized_riesz_potential R f z \<noteq> 0}"
proof -
  have f_lp: "aim_complex_lp_on_plane p f"
    unfolding f_def
    by (rule slp_positive_ennreal_lp_to_complex[OF F_lp])
  have f_support_subset:
      "{x. f x \<noteq> 0} \<subseteq> {x. F x \<noteq> 0}"
    unfolding f_def by auto
  have f_support: "bounded {x. f x \<noteq> 0}"
    by (rule bounded_subset[OF F_support f_support_subset])
  have compact_result:
      "(AE z in lborel.
          integrable lborel (slp_localized_riesz_integrand R f z)) \<and>
        aim_real_lp_on_plane 2 (slp_localized_riesz_potential R f) \<and>
        bounded {z. slp_localized_riesz_potential R f z \<noteq> 0}"
    by (rule slp_localized_riesz_l2_compact_lp[OF radius_nonnegative
          p_lower p_upper f_lp f_support])
  have F_finite: "AE y in lborel. F y < top"
    using F_lp unfolding slp_positive_ennreal_lp_on_plane_def by blast
  have source_identity:
      "AE y in lborel. ennreal (norm (f y)) = F y"
    using F_finite
  proof eventually_elim
    fix y
    assume finite: "F y < top"
    show "ennreal (norm (f y)) = F y"
      unfolding f_def using finite by simp
  qed
  have integral_identity:
      "AE z in lborel.
        (\<integral>\<^sup>+ y.
          ennreal (slp_localized_cauchy_kernel R (y - z)) * F y
          \<partial>lborel) =
        ennreal (slp_localized_riesz_potential R f z)"
    using conjunct1[OF compact_result]
  proof eventually_elim
    fix z
    assume fiber_integrable:
      "integrable lborel (slp_localized_riesz_integrand R f z)"
    have congruence:
        "(\<integral>\<^sup>+ y.
            ennreal (slp_localized_cauchy_kernel R (y - z)) * F y
            \<partial>lborel) =
          (\<integral>\<^sup>+ y.
            ennreal (norm (f y)) *
              ennreal (slp_localized_cauchy_kernel R (y - z))
            \<partial>lborel)"
      by (rule nn_integral_cong_AE)
        (use source_identity in eventually_elim; simp add: mult.commute)
    show
      "(\<integral>\<^sup>+ y.
          ennreal (slp_localized_cauchy_kernel R (y - z)) * F y
          \<partial>lborel) =
        ennreal (slp_localized_riesz_potential R f z)"
      using congruence slp_localized_riesz_nn_integral[OF fiber_integrable]
      by simp
  qed
  show ?thesis
    using integral_identity compact_result by blast
qed

end

end
