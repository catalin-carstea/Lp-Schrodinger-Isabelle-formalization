theory Inverse_Schrodinger_Lp_Born_Root_Positive_Order_L2
  imports Inverse_Schrodinger_Lp_Born_Root_All_Order_Terminal_Weighted
    Inverse_Schrodinger_Lp_Born_Root_Bounded_Support
    Inverse_Schrodinger_Lp_Positive_Ennreal_Riesz_L2
    Inverse_Schrodinger_Lp_Born_Root_Terminal_Collapse
    Inverse_Schrodinger_Lp_Born_One_Sided_Zero_L2
begin

section \<open>Positive-order root densities in real L2\<close>

context aim_planar_riesz_hls
begin

theorem slp_positive_root_output_density_real_positive_order_l2:
  fixes R C p :: real
    and X :: "slp_point set"
    and cutoff potential root_weight :: "slp_point \<Rightarrow> complex"
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and root_weight_lp: "aim_complex_lp_on_plane p root_weight"
    and root_weight_outside:
      "\<And>x. x \<notin> X \<Longrightarrow> root_weight x = 0"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "aim_real_lp_on_plane 2
      (slp_positive_root_output_density_real R cutoff potential (\<lambda>_. 1)
        (Suc n) root_weight)"
proof -
  let ?a = "slp_branch_power_exponent p"
  let ?F = "slp_positive_root_output_density R cutoff potential
    (slp_positive_terminal_riesz_weight R potential) n root_weight"
  let ?f = "\<lambda>x. of_real (enn2real (?F x)) :: complex"
  let ?P = "slp_localized_riesz_potential R ?f"
  let ?G = "slp_positive_root_output_density R cutoff potential (\<lambda>_. 1)
    (Suc n) root_weight"
  let ?D = "slp_positive_root_output_density_real R cutoff potential
    (\<lambda>_. 1) (Suc n) root_weight"
  let ?scale = "inverse (pi ^ 2) * C"
  have potential_measurable:
      "potential \<in> borel_measurable lborel"
    using potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    using root_weight_lp unfolding aim_complex_lp_on_plane_def by blast
  have root_support_subset: "{x. root_weight x \<noteq> 0} \<subseteq> X"
    using root_weight_outside by blast
  have root_support: "bounded {x. root_weight x \<noteq> 0}"
    by (rule bounded_subset[OF X_bounded root_support_subset])
  note all_order =
    slp_positive_root_output_density_all_orders_terminal_weighted_lp_root[OF
      radius_nonnegative p_lower p_upper X_measurable X_bounded
      cutoff_measurable potential_lp root_weight_lp root_weight_outside
      cutoff_bound C_nonnegative]
  have a_lower: "1 < ?a" and a_upper_p: "?a < p"
    using all_order(1) by blast+
  obtain L where F_lp:
      "slp_positive_ennreal_lp_on_plane ?a ?F"
    using all_order(2)[of n] by blast
  have a_upper: "?a < 2"
    using a_upper_p p_upper by linarith
  have F_support: "bounded {x. ?F x \<noteq> 0}"
    by (rule slp_positive_root_output_density_bounded_support[OF
          radius_nonnegative root_support])
  have compact_result:
      "(AE z in lborel.
          (\<integral>\<^sup>+y.
            ennreal (slp_localized_cauchy_kernel R (y - z)) * ?F y
            \<partial>lborel) = ennreal (?P z)) \<and>
        aim_real_lp_on_plane 2 ?P \<and>
        bounded {z. ?P z \<noteq> 0}"
    by (rule slp_positive_ennreal_localized_riesz_l2_compact[OF
          radius_nonnegative a_lower a_upper F_lp F_support])
  have convolution_identity:
      "AE z in lborel.
        (\<integral>\<^sup>+y.
          ennreal (slp_localized_cauchy_kernel R (y - z)) * ?F y
          \<partial>lborel) = ennreal (?P z)"
    using compact_result by blast
  have P_l2: "aim_real_lp_on_plane 2 ?P"
    using compact_result by blast
  have collapse:
      "?G z \<le>
        ennreal (inverse (pi ^ 2)) * ennreal C *
          (\<integral>\<^sup>+y.
            ennreal (slp_localized_cauchy_kernel R (y - z)) * ?F y
            \<partial>lborel)"
    for z
    by (rule slp_positive_root_output_density_positive_terminal_collapse[OF
          cutoff_measurable potential_measurable root_weight_measurable
          cutoff_bound C_nonnegative])
  have scale_nonnegative: "0 \<le> ?scale"
    using C_nonnegative by simp
  have inverse_pi_squared_nonnegative: "0 \<le> inverse (pi ^ 2)"
    by simp
  have P_nonnegative: "0 \<le> ?P z" for z
    by (rule slp_localized_riesz_potential_nonnegative)
  have ennreal_domination:
      "AE z in lborel. ?G z \<le> ennreal (?scale * ?P z)"
    using convolution_identity
  proof eventually_elim
    fix z :: slp_point
    assume identity:
      "(\<integral>\<^sup>+y.
        ennreal (slp_localized_cauchy_kernel R (y - z)) * ?F y
        \<partial>lborel) = ennreal (?P z)"
    show "?G z \<le> ennreal (?scale * ?P z)"
    proof -
      have collapse_at_z:
          "?G z \<le>
            ennreal (inverse (pi ^ 2)) * ennreal C * ennreal (?P z)"
        using collapse[of z] identity by simp
      have scalar_identity:
          "ennreal (inverse (pi ^ 2)) * ennreal C * ennreal (?P z) =
            ennreal (?scale * ?P z)"
        using inverse_pi_squared_nonnegative C_nonnegative
          P_nonnegative[of z]
        by (simp add: ennreal_mult mult.assoc)
      show ?thesis using collapse_at_z scalar_identity by simp
    qed
  qed
  have D_measurable: "?D \<in> borel_measurable lborel"
  proof -
    have G_measurable: "?G \<in> borel_measurable lborel"
      by (rule slp_positive_root_output_density_measurable[OF
            cutoff_measurable potential_measurable _
            root_weight_measurable]) measurable
    show ?thesis
      unfolding slp_positive_root_output_density_real_def
      using G_measurable by measurable
  qed
  have D_domination: "AE z in lborel. ?D z \<le> ?scale * ?P z"
    using ennreal_domination
  proof eventually_elim
    fix z :: slp_point
    assume bound: "?G z \<le> ennreal (?scale * ?P z)"
    have real_bound:
        "enn2real (?G z) \<le> enn2real (ennreal (?scale * ?P z))"
      by (rule enn2real_mono[OF bound]) simp
    show "?D z \<le> ?scale * ?P z"
      unfolding slp_positive_root_output_density_real_def
      using real_bound scale_nonnegative P_nonnegative[of z] by simp
  qed
  let ?A = "\<lambda>_ :: slp_point. ?scale"
  have A_measurable: "?A \<in> borel_measurable lborel"
    by measurable
  have A_bound: "abs (?A z) \<le> ?scale" for z
    using scale_nonnegative by simp
  have scaled_P_l2: "aim_real_lp_on_plane 2 (\<lambda>z. ?scale * ?P z)"
    by (rule aim_real_lp_on_plane_two_bounded_multiplier[OF
          A_measurable P_l2 A_bound scale_nonnegative])
  have scaled_power_integrable:
      "integrable lborel (\<lambda>z. abs (?scale * ?P z) powr 2)"
    using scaled_P_l2 unfolding aim_real_lp_on_plane_def by blast
  have D_power_measurable:
      "(\<lambda>z. abs (?D z) powr 2) \<in> borel_measurable lborel"
    using D_measurable by measurable
  have D_power_integrable:
      "integrable lborel (\<lambda>z. abs (?D z) powr 2)"
  proof (rule Bochner_Integration.integrable_bound[OF
        scaled_power_integrable D_power_measurable])
    from D_domination show "AE z in lborel.
        Real_Vector_Spaces.norm (abs (?D z) powr 2) \<le>
          Real_Vector_Spaces.norm (abs (?scale * ?P z) powr 2)"
    proof eventually_elim
      fix z :: slp_point
      assume bound: "?D z \<le> ?scale * ?P z"
      have D_nonnegative: "0 \<le> ?D z"
        unfolding slp_positive_root_output_density_real_def by simp
      have product_nonnegative: "0 \<le> ?scale * ?P z"
        using scale_nonnegative P_nonnegative[of z] by simp
      have square_bound: "(?D z)^2 \<le> (?scale * ?P z)^2"
        by (rule power_mono[OF bound D_nonnegative])
      show "Real_Vector_Spaces.norm (abs (?D z) powr 2) \<le>
          Real_Vector_Spaces.norm (abs (?scale * ?P z) powr 2)"
        using square_bound D_nonnegative product_nonnegative
        by (simp add: powr_numeral)
    qed
  qed
  show ?thesis
    unfolding aim_real_lp_on_plane_def
    using D_measurable D_power_integrable by blast
qed

end

end
