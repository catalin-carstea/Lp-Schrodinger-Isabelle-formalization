theory Inverse_Schrodinger_Lp_Born_One_Sided_All_Order_L1
  imports Inverse_Schrodinger_Lp_Born_One_Sided_All_Order_L2
begin

section \<open>All-order real \(L^1\) interfaces for one-sided densities\<close>

context aim_planar_riesz_hls
begin

theorem slp_left_right_one_sided_output_density_real_all_orders_l1:
  fixes R C p :: real
    and X :: "slp_point set"
    and cutoff potential :: "slp_point \<Rightarrow> complex"
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and potential_outside: "\<And>x. x \<notin> X \<Longrightarrow> potential x = 0"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows left_integrable:
      "integrable lborel (\<lambda>output. enn2real
        (slp_left_one_sided_output_density R cutoff potential
          (\<lambda>_. 1) n potential output))"
    and right_integrable:
      "integrable lborel (\<lambda>output. enn2real
        (slp_right_one_sided_output_density R cutoff potential
          (\<lambda>_. 1) n potential output))"
proof -
  have potential_measurable:
      "potential \<in> borel_measurable lborel"
    using potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have potential_integrable: "integrable lborel potential"
    by (rule aim_complex_lp_on_plane_integrable_bounded_support[OF
          _ X_measurable X_bounded potential_lp potential_outside])
       (use p_lower in simp)
  have terminal_measurable:
      "(\<lambda>_ :: slp_point. 1 :: ennreal) \<in> borel_measurable lborel"
    by measurable
  let ?left = "slp_left_one_sided_output_density R cutoff potential
    (\<lambda>_. 1) n potential"
  let ?right = "slp_right_one_sided_output_density R cutoff potential
    (\<lambda>_. 1) n potential"
  have density_measurable:
      "slp_positive_root_output_density R cutoff potential (\<lambda>_. 1) n
        potential \<in> borel_measurable lborel"
    by (rule slp_positive_root_output_density_measurable[OF
          cutoff_measurable potential_measurable terminal_measurable
          potential_measurable])
  have left_measurable: "?left \<in> borel_measurable lborel"
    using density_measurable
    unfolding slp_left_one_sided_output_density_def .
  have right_measurable: "?right \<in> borel_measurable lborel"
    using density_measurable
    unfolding slp_right_one_sided_output_density_def .
  have left_mass_finite:
      "(\<integral>\<^sup>+ output. ?left output \<partial>lborel) <
        \<infinity>"
    using slp_left_one_sided_output_density_unweighted_mass_finite_lp_root
      [where R=R and C=C and p=p and X=X and cutoff=cutoff
        and potential=potential and root_weight=potential and n=n, OF
        radius_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable potential_lp potential_lp potential_outside
        cutoff_bound C_nonnegative]
    by simp
  have right_mass_finite:
      "(\<integral>\<^sup>+ output. ?right output \<partial>lborel) <
        \<infinity>"
    using slp_right_one_sided_output_density_unweighted_mass_finite_lp_root
      [where R=R and C=C and p=p and X=X and cutoff=cutoff
        and potential=potential and root_weight=potential and n=n, OF
        radius_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable potential_lp potential_lp potential_outside
        cutoff_bound C_nonnegative]
    by simp
  show left_integrable:
      "integrable lborel (\<lambda>output. enn2real (?left output))"
  proof (unfold integrable_iff_bounded, intro conjI)
    show "(\<lambda>output. enn2real (?left output)) \<in>
        borel_measurable lborel"
      using left_measurable by measurable
    have "(\<integral>\<^sup>+ output.
          ennreal (Real_Vector_Spaces.norm (enn2real (?left output)))
          \<partial>lborel) \<le>
        (\<integral>\<^sup>+ output. ?left output \<partial>lborel)"
      by (rule nn_integral_mono) (simp add: ennreal_enn2real_if)
    then show "(\<integral>\<^sup>+ output.
        ennreal (Real_Vector_Spaces.norm (enn2real (?left output)))
        \<partial>lborel) < \<infinity>"
      by (rule le_less_trans[OF _ left_mass_finite])
  qed
  show right_integrable:
      "integrable lborel (\<lambda>output. enn2real (?right output))"
  proof (unfold integrable_iff_bounded, intro conjI)
    show "(\<lambda>output. enn2real (?right output)) \<in>
        borel_measurable lborel"
      using right_measurable by measurable
    have "(\<integral>\<^sup>+ output.
          ennreal (Real_Vector_Spaces.norm (enn2real (?right output)))
          \<partial>lborel) \<le>
        (\<integral>\<^sup>+ output. ?right output \<partial>lborel)"
      by (rule nn_integral_mono) (simp add: ennreal_enn2real_if)
    then show "(\<integral>\<^sup>+ output.
        ennreal (Real_Vector_Spaces.norm (enn2real (?right output)))
        \<partial>lborel) < \<infinity>"
      by (rule le_less_trans[OF _ right_mass_finite])
  qed
qed

end

end
