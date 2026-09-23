theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Absolute_Mass_Cauchy
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Density_Cauchy_Terminal_Mass_Finite"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Fiber_Mass_Domination"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cauchy_Measurable_Below_Two"
begin

section \<open>Global weighted absolute mass with actual Cauchy terminals\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_mixed_center_finite_weighted_absolute_mass_cauchy_finite:
  fixes left_dummy :: "'i::finite itself"
    and right_dummy :: "'j::finite itself"
    and B C D p :: real
    and X :: "slp_point set"
    and root_weight cutoff left_potential right_potential center_factor ::
      slp_scalar_field
    and left_orientation right_orientation :: slp_cauchy_orientation
  assumes B_nonnegative: "0 \<le> B"
    and C_nonnegative: "0 \<le> C"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and left_potential_lp: "aim_complex_lp_on_plane p left_potential"
    and right_potential_lp: "aim_complex_lp_on_plane p right_potential"
    and root_weight_lp: "aim_complex_lp_on_plane p root_weight"
    and root_weight_outside:
      "\<And>x. x \<notin> X \<Longrightarrow> root_weight x = 0"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and center_factor_bound: "\<And>x. cmod (center_factor x) \<le> D"
    and root_support:
      "\<And>x. root_weight x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and left_potential_support:
      "\<And>x. left_potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and right_potential_support:
      "\<And>x. right_potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
  shows
    "(\<integral>\<^sup>+ center.
      slp_mixed_center_finite_weighted_absolute_fiber_mass
        TYPE('i) TYPE('j) root_weight cutoff left_potential
        (slp_cauchy_transform left_orientation left_potential) cutoff
        right_potential
        (slp_cauchy_transform right_orientation right_potential)
        center_factor center \<partial>lborel) < top_class.top"
proof -
  let ?left_terminal =
    "slp_cauchy_transform left_orientation left_potential"
  let ?right_terminal =
    "slp_cauchy_transform right_orientation right_potential"
  let ?density =
    "slp_mixed_center_density (2 * B) cutoff left_potential right_potential
      (\<lambda>x. ennreal (cmod (?left_terminal x)))
      (\<lambda>x. ennreal (cmod (?right_terminal x)))
      CARD('i) CARD('j) root_weight"
  have root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    using root_weight_lp unfolding aim_complex_lp_on_plane_def by blast
  have left_potential_measurable:
      "left_potential \<in> borel_measurable lborel"
    using left_potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have right_potential_measurable:
      "right_potential \<in> borel_measurable lborel"
    using right_potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have left_terminal_measurable:
      "?left_terminal \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF
          p_lower p_upper left_potential_lp])
  have right_terminal_measurable:
      "?right_terminal \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF
          p_lower p_upper right_potential_lp])
  have left_terminal_weight_measurable:
      "(\<lambda>x. ennreal (cmod (?left_terminal x))) \<in>
        borel_measurable lborel"
    using left_terminal_measurable by measurable
  have right_terminal_weight_measurable:
      "(\<lambda>x. ennreal (cmod (?right_terminal x))) \<in>
        borel_measurable lborel"
    using right_terminal_measurable by measurable
  have density_measurable: "?density \<in> borel_measurable lborel"
    by (rule slp_mixed_center_density_measurable[OF cutoff_measurable
          left_potential_measurable right_potential_measurable
          left_terminal_weight_measurable right_terminal_weight_measurable
          root_weight_measurable])
  have fiber_bound:
      "slp_mixed_center_finite_weighted_absolute_fiber_mass
          TYPE('i) TYPE('j) root_weight cutoff left_potential ?left_terminal
          cutoff right_potential ?right_terminal center_factor center \<le>
        ennreal D * ?density center"
    for center
  proof -
    have raw_bound:
        "slp_mixed_center_finite_weighted_absolute_fiber_mass
            TYPE('i) TYPE('j) root_weight cutoff left_potential
            ?left_terminal cutoff right_potential ?right_terminal
            center_factor center \<le>
          ennreal (cmod (center_factor center)) * ?density center"
      by (rule
        slp_mixed_center_finite_weighted_absolute_fiber_mass_density_bound[OF
          B_nonnegative root_weight_measurable cutoff_measurable
          left_potential_measurable left_terminal_measurable
          right_potential_measurable right_terminal_measurable root_support
          cutoff_support left_potential_support right_potential_support])
    have factor_le:
        "ennreal (cmod (center_factor center)) \<le> ennreal D"
      by (rule ennreal_leI[OF center_factor_bound])
    have product_le:
        "ennreal (cmod (center_factor center)) * ?density center \<le>
          ennreal D * ?density center"
      by (rule mult_right_mono[OF factor_le]) simp
    show ?thesis
      using raw_bound product_le by (rule order_trans)
  qed
  have density_mass_finite:
      "(\<integral>\<^sup>+ center. ?density center \<partial>lborel) < top_class.top"
    by (rule
      slp_mixed_center_density_cauchy_terminal_all_orders_mass_finite[OF
        B_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable left_potential_lp right_potential_lp root_weight_lp
        root_weight_outside cutoff_bound C_nonnegative cutoff_support
        left_potential_support right_potential_support])
  have mass_le:
      "(\<integral>\<^sup>+ center.
        slp_mixed_center_finite_weighted_absolute_fiber_mass
          TYPE('i) TYPE('j) root_weight cutoff left_potential ?left_terminal
          cutoff right_potential ?right_terminal center_factor center
        \<partial>lborel) \<le>
        (\<integral>\<^sup>+ center. ennreal D * ?density center \<partial>lborel)"
    by (rule nn_integral_mono) (rule fiber_bound)
  have pull_constant:
      "(\<integral>\<^sup>+ center. ennreal D * ?density center \<partial>lborel) =
        ennreal D * (\<integral>\<^sup>+ center. ?density center \<partial>lborel)"
    by (rule nn_integral_cmult[OF density_measurable])
  have scaled_mass_finite:
      "ennreal D * (\<integral>\<^sup>+ center. ?density center \<partial>lborel) <
        top_class.top"
    using density_mass_finite by (simp add: ennreal_mult_less_top)
  show ?thesis
    by (rule le_less_trans[OF mass_le])
      (use pull_constant scaled_mass_finite in simp)
qed

end

end
