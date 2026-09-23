theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Absolute_Mass_One_Terminal
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Fiber_Mass_Domination"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Density_Cutoff_Terminal_Monotone"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Mixed_Center_Density_Membership_Clauses"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Positive_Ennreal_Lp_Domination"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Positive_Ennreal_Complex_Pairing"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cauchy_Cutoff_Terminal_Bound"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cauchy_Measurable_Below_Two"
begin

hide_const (open) Commutative_Ring.norm

section \<open>One-terminal weighted absolute mass\<close>

theorem slp_mixed_center_finite_weighted_absolute_mass_L2_finite:
  fixes left_dummy :: "'i::finite itself"
    and right_dummy :: "'j::finite itself"
    and B :: real
    and root_weight cutoff left_potential left_terminal_value
      right_potential right_terminal_value center_factor :: slp_scalar_field
  assumes B_nonnegative: "0 \<le> B"
    and root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    and cutoff_measurable:
      "cutoff \<in> borel_measurable lborel"
    and left_potential_measurable:
      "left_potential \<in> borel_measurable lborel"
    and left_terminal_measurable:
      "left_terminal_value \<in> borel_measurable lborel"
    and right_potential_measurable:
      "right_potential \<in> borel_measurable lborel"
    and right_terminal_measurable:
      "right_terminal_value \<in> borel_measurable lborel"
    and root_support:
      "\<And>x. root_weight x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and left_potential_support:
      "\<And>x. left_potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and right_potential_support:
      "\<And>x. right_potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and density_L2:
      "slp_positive_ennreal_lp_on_plane 2
        (slp_mixed_center_density (2 * B) cutoff left_potential
          right_potential
          (\<lambda>x. ennreal (cmod (left_terminal_value x)))
          (\<lambda>x. ennreal (cmod (right_terminal_value x)))
          CARD('i) CARD('j) root_weight)"
    and center_factor_L2:
      "aim_complex_lp_on_plane 2 center_factor"
  shows
    "(\<integral>\<^sup>+ center.
      slp_mixed_center_finite_weighted_absolute_fiber_mass
        TYPE('i) TYPE('j) root_weight cutoff left_potential
        left_terminal_value cutoff right_potential right_terminal_value
        center_factor center \<partial>lborel) < top_class.top"
proof -
  let ?density =
    "slp_mixed_center_density (2 * B) cutoff left_potential right_potential
      (\<lambda>x. ennreal (cmod (left_terminal_value x)))
      (\<lambda>x. ennreal (cmod (right_terminal_value x)))
      CARD('i) CARD('j) root_weight"
  have fiber_bound:
      "slp_mixed_center_finite_weighted_absolute_fiber_mass
          TYPE('i) TYPE('j) root_weight cutoff left_potential
          left_terminal_value cutoff right_potential right_terminal_value
          center_factor center \<le>
        ennreal (cmod (center_factor center)) * ?density center"
    for center
    by (rule
      slp_mixed_center_finite_weighted_absolute_fiber_mass_density_bound[OF
        B_nonnegative root_weight_measurable cutoff_measurable
        left_potential_measurable left_terminal_measurable
        right_potential_measurable right_terminal_measurable root_support
        cutoff_support left_potential_support right_potential_support])
  have pairing_finite:
      "(\<integral>\<^sup>+ center.
        ?density center * ennreal (norm (center_factor center))
        \<partial>lborel) < top_class.top"
    by (rule slp_positive_ennreal_lp_complex_pairing_lt_top[
          where q = 2 and r = 2, OF _ _ _ density_L2 center_factor_L2])
      simp_all
  have mass_le:
      "(\<integral>\<^sup>+ center.
        slp_mixed_center_finite_weighted_absolute_fiber_mass
          TYPE('i) TYPE('j) root_weight cutoff left_potential
          left_terminal_value cutoff right_potential right_terminal_value
          center_factor center \<partial>lborel) \<le>
        (\<integral>\<^sup>+ center.
          ?density center * ennreal (norm (center_factor center))
          \<partial>lborel)"
    apply (rule nn_integral_mono)
    using fiber_bound by (simp add: mult.commute)
  show ?thesis
    by (rule le_less_trans[OF mass_le pairing_finite])
qed

context aim_planar_riesz_hls_cauchy
begin

theorem slp_mixed_center_finite_weighted_absolute_mass_left_cauchy_unit_finite:
  fixes left_dummy :: "'i::finite itself"
    and right_dummy :: "'j::finite itself"
    and B C p :: real
    and X :: "slp_point set"
    and root_weight cutoff left_potential right_potential center_factor ::
      slp_scalar_field
    and left_orientation :: slp_cauchy_orientation
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
    and root_support:
      "\<And>x. root_weight x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and left_potential_support:
      "\<And>x. left_potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and right_potential_support:
      "\<And>x. right_potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and center_factor_L2:
      "aim_complex_lp_on_plane 2 center_factor"
  shows
    "(\<integral>\<^sup>+ center.
      slp_mixed_center_finite_weighted_absolute_fiber_mass
        TYPE('i) TYPE('j) root_weight cutoff left_potential
        (slp_cauchy_transform left_orientation left_potential) cutoff
        right_potential (\<lambda>_. 1) center_factor center \<partial>lborel) <
      top_class.top"
proof -
  let ?left_terminal =
    "slp_cauchy_transform left_orientation left_potential"
  let ?unit_terminal = "\<lambda>_ :: slp_point. 1 :: complex"
  let ?density =
    "slp_mixed_center_density (2 * B) cutoff left_potential right_potential
      (\<lambda>x. ennreal (cmod (?left_terminal x)))
      (\<lambda>x. ennreal (cmod (?unit_terminal x)))
      CARD('i) CARD('j) root_weight"
  let ?majorant =
    "slp_mixed_center_density (2 * B) cutoff left_potential right_potential
      (slp_positive_terminal_riesz_weight (2 * B) left_potential)
      (\<lambda>_. 1) CARD('i) CARD('j) root_weight"
  have radius_nonnegative: "0 \<le> 2 * B"
    using B_nonnegative by simp
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
  have unit_terminal_measurable:
      "?unit_terminal \<in> borel_measurable lborel"
    by measurable
  have left_terminal_weight_measurable:
      "(\<lambda>x. ennreal (cmod (?left_terminal x))) \<in>
        borel_measurable lborel"
    using left_terminal_measurable by measurable
  have unit_terminal_weight_measurable:
      "(\<lambda>x. ennreal (cmod (?unit_terminal x))) \<in>
        borel_measurable lborel"
    using unit_terminal_measurable by measurable
  have density_measurable: "?density \<in> borel_measurable lborel"
    by (rule slp_mixed_center_density_measurable[OF cutoff_measurable
          left_potential_measurable right_potential_measurable
          left_terminal_weight_measurable unit_terminal_weight_measurable
          root_weight_measurable])
  have support_radius:
      "\<And>x y :: slp_point.
        \<lbrakk>cutoff x \<noteq> 0; left_potential y \<noteq> 0\<rbrakk> \<Longrightarrow>
          norm (x - y) \<le> 2 * B"
    by (rule slp_norm_sub_le_two_radius[OF B_nonnegative
          cutoff_support left_potential_support])
  have left_terminal_le:
      "\<And>x. ennreal (cmod (cutoff x)) *
          ennreal (cmod (?left_terminal x)) \<le>
        ennreal (cmod (cutoff x)) *
          slp_positive_terminal_riesz_weight (2 * B) left_potential x"
    by (rule slp_cauchy_transform_cutoff_terminal_riesz_bound[OF
          support_radius])
  have density_le: "?density center \<le> ?majorant center" for center
    by (rule slp_mixed_center_density_cutoff_terminal_mono)
      (use left_terminal_le in simp_all)
  have majorant_L2:
      "slp_positive_ennreal_lp_on_plane 2 ?majorant"
    by (rule slp_mixed_center_density_all_orders_membership_clauses(4)[OF
          radius_nonnegative p_lower p_upper X_measurable X_bounded
          cutoff_measurable left_potential_lp right_potential_lp
          root_weight_lp root_weight_outside cutoff_bound C_nonnegative])
  have density_L2: "slp_positive_ennreal_lp_on_plane 2 ?density"
    by (rule slp_positive_ennreal_lp_mono_AE[OF _ majorant_L2
          density_measurable])
      (use density_le in simp_all)
  show ?thesis
    by (rule slp_mixed_center_finite_weighted_absolute_mass_L2_finite[OF
          B_nonnegative root_weight_measurable cutoff_measurable
          left_potential_measurable left_terminal_measurable
          right_potential_measurable unit_terminal_measurable root_support
          cutoff_support left_potential_support right_potential_support
          density_L2 center_factor_L2])
qed

theorem slp_mixed_center_finite_weighted_absolute_mass_unit_right_cauchy_finite:
  fixes left_dummy :: "'i::finite itself"
    and right_dummy :: "'j::finite itself"
    and B C p :: real
    and X :: "slp_point set"
    and root_weight cutoff left_potential right_potential center_factor ::
      slp_scalar_field
    and right_orientation :: slp_cauchy_orientation
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
    and root_support:
      "\<And>x. root_weight x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and left_potential_support:
      "\<And>x. left_potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and right_potential_support:
      "\<And>x. right_potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and center_factor_L2:
      "aim_complex_lp_on_plane 2 center_factor"
  shows
    "(\<integral>\<^sup>+ center.
      slp_mixed_center_finite_weighted_absolute_fiber_mass
        TYPE('i) TYPE('j) root_weight cutoff left_potential (\<lambda>_. 1)
        cutoff right_potential
        (slp_cauchy_transform right_orientation right_potential)
        center_factor center \<partial>lborel) < top_class.top"
proof -
  let ?unit_terminal = "\<lambda>_ :: slp_point. 1 :: complex"
  let ?right_terminal =
    "slp_cauchy_transform right_orientation right_potential"
  let ?density =
    "slp_mixed_center_density (2 * B) cutoff left_potential right_potential
      (\<lambda>x. ennreal (cmod (?unit_terminal x)))
      (\<lambda>x. ennreal (cmod (?right_terminal x)))
      CARD('i) CARD('j) root_weight"
  let ?majorant =
    "slp_mixed_center_density (2 * B) cutoff left_potential right_potential
      (\<lambda>_. 1)
      (slp_positive_terminal_riesz_weight (2 * B) right_potential)
      CARD('i) CARD('j) root_weight"
  have radius_nonnegative: "0 \<le> 2 * B"
    using B_nonnegative by simp
  have root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    using root_weight_lp unfolding aim_complex_lp_on_plane_def by blast
  have left_potential_measurable:
      "left_potential \<in> borel_measurable lborel"
    using left_potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have right_potential_measurable:
      "right_potential \<in> borel_measurable lborel"
    using right_potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have unit_terminal_measurable:
      "?unit_terminal \<in> borel_measurable lborel"
    by measurable
  have right_terminal_measurable:
      "?right_terminal \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF
          p_lower p_upper right_potential_lp])
  have unit_terminal_weight_measurable:
      "(\<lambda>x. ennreal (cmod (?unit_terminal x))) \<in>
        borel_measurable lborel"
    using unit_terminal_measurable by measurable
  have right_terminal_weight_measurable:
      "(\<lambda>x. ennreal (cmod (?right_terminal x))) \<in>
        borel_measurable lborel"
    using right_terminal_measurable by measurable
  have density_measurable: "?density \<in> borel_measurable lborel"
    by (rule slp_mixed_center_density_measurable[OF cutoff_measurable
          left_potential_measurable right_potential_measurable
          unit_terminal_weight_measurable right_terminal_weight_measurable
          root_weight_measurable])
  have support_radius:
      "\<And>x y :: slp_point.
        \<lbrakk>cutoff x \<noteq> 0; right_potential y \<noteq> 0\<rbrakk> \<Longrightarrow>
          norm (x - y) \<le> 2 * B"
    by (rule slp_norm_sub_le_two_radius[OF B_nonnegative
          cutoff_support right_potential_support])
  have right_terminal_le:
      "\<And>x. ennreal (cmod (cutoff x)) *
          ennreal (cmod (?right_terminal x)) \<le>
        ennreal (cmod (cutoff x)) *
          slp_positive_terminal_riesz_weight (2 * B) right_potential x"
    by (rule slp_cauchy_transform_cutoff_terminal_riesz_bound[OF
          support_radius])
  have density_le: "?density center \<le> ?majorant center" for center
    by (rule slp_mixed_center_density_cutoff_terminal_mono)
      (use right_terminal_le in simp_all)
  have majorant_L2:
      "slp_positive_ennreal_lp_on_plane 2 ?majorant"
    by (rule slp_mixed_center_density_all_orders_membership_clauses(5)[OF
          radius_nonnegative p_lower p_upper X_measurable X_bounded
          cutoff_measurable left_potential_lp right_potential_lp
          root_weight_lp root_weight_outside cutoff_bound C_nonnegative])
  have density_L2: "slp_positive_ennreal_lp_on_plane 2 ?density"
    by (rule slp_positive_ennreal_lp_mono_AE[OF _ majorant_L2
          density_measurable])
      (use density_le in simp_all)
  show ?thesis
    by (rule slp_mixed_center_finite_weighted_absolute_mass_L2_finite[OF
          B_nonnegative root_weight_measurable cutoff_measurable
          left_potential_measurable unit_terminal_measurable
          right_potential_measurable right_terminal_measurable root_support
          cutoff_support left_potential_support right_potential_support
          density_L2 center_factor_L2])
qed

end

end
