theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Absolute_Mass_Unit_Unit
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Absolute_Mass_Conjugate"
begin

hide_const (open) Commutative_Ring.norm

section \<open>The literal unit--unit weighted absolute mass\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_mixed_center_finite_weighted_absolute_mass_unit_unit_two_cauchy_finite:
  fixes left_dummy :: "'i::finite itself"
    and right_dummy :: "'j::finite itself"
    and B C p :: real
    and X :: "slp_point set"
    and phi root_weight cutoff left_potential right_potential ::
      slp_scalar_field
    and left_orientation right_orientation :: slp_cauchy_orientation
  assumes B_nonnegative: "0 \<le> B"
    and C_nonnegative: "0 \<le> C"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and phi_test: "slp_test_function_on UNIV phi"
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
  shows
    "(\<integral>\<^sup>+ center.
      slp_mixed_center_finite_weighted_absolute_fiber_mass
        TYPE('i) TYPE('j) root_weight cutoff left_potential (\<lambda>_. 1)
        cutoff right_potential (\<lambda>_. 1)
        (\<lambda>x. phi x *
          (slp_cauchy_transform left_orientation left_potential x *
            slp_cauchy_transform right_orientation right_potential x))
        center \<partial>lborel) < top_class.top"
proof -
  let ?r = "aim_hls_target_exponent p / 2"
  let ?q = "slp_holder_conjugate ?r"
  let ?unit_terminal = "\<lambda>_ :: slp_point. 1 :: complex"
  let ?center_factor = "\<lambda>x. phi x *
    (slp_cauchy_transform left_orientation left_potential x *
      slp_cauchy_transform right_orientation right_potential x)"
  have radius_nonnegative: "0 \<le> 2 * B"
    using B_nonnegative by simp
  have half_target_lower: "1 < ?r"
    using slp_hls_target_exponent_above_two[OF p_lower p_upper] by linarith
  have q_lower: "1 < ?q"
    and conjugate: "1 / ?q + 1 / ?r = 1"
    using slp_holder_conjugate_lower_and_pair[OF half_target_lower] by auto
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
  have density_Lq_raw:
      "slp_positive_ennreal_lp_on_plane ?q
        (slp_mixed_center_density (2 * B) cutoff left_potential
          right_potential (\<lambda>_. 1) (\<lambda>_. 1)
          CARD('i) CARD('j) root_weight)"
    by (rule
      slp_mixed_center_density_unit_terminal_all_orders_finite_target[OF
        radius_nonnegative p_lower p_upper q_lower X_measurable X_bounded
        cutoff_measurable left_potential_lp right_potential_lp root_weight_lp
        root_weight_outside cutoff_bound C_nonnegative])
  have density_Lq:
      "slp_positive_ennreal_lp_on_plane ?q
        (slp_mixed_center_density (2 * B) cutoff left_potential
          right_potential
          (\<lambda>x. ennreal (cmod (?unit_terminal x)))
          (\<lambda>x. ennreal (cmod (?unit_terminal x)))
          CARD('i) CARD('j) root_weight)"
    using density_Lq_raw by simp
  have center_factor_Lr:
      "aim_complex_lp_on_plane ?r ?center_factor"
    by (rule slp_test_two_cauchy_product_half_hls_target_lp[OF
          p_lower p_upper left_potential_lp right_potential_lp phi_test])
  show ?thesis
    by (rule
      slp_mixed_center_finite_weighted_absolute_mass_conjugate_finite[OF
        q_lower half_target_lower conjugate B_nonnegative
        root_weight_measurable cutoff_measurable left_potential_measurable
        unit_terminal_measurable right_potential_measurable
        unit_terminal_measurable root_support cutoff_support
        left_potential_support right_potential_support density_Lq
        center_factor_Lr])
qed

end

end
