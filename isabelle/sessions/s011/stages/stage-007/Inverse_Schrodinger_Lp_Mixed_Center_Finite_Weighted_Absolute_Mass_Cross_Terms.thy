theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Absolute_Mass_Cross_Terms
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Absolute_Mass_One_Terminal"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Test_Cauchy_Product_L2"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Signed one-terminal mixed cross terms\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_mixed_center_finite_weighted_absolute_mass_left_cross_finite:
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
        TYPE('i) TYPE('j) root_weight cutoff left_potential
        (slp_cauchy_transform left_orientation left_potential) cutoff
        right_potential (\<lambda>_. 1)
        (\<lambda>x. -(phi x *
          slp_cauchy_transform right_orientation right_potential x))
        center \<partial>lborel) < top_class.top"
proof -
  have product_L2:
      "aim_complex_lp_on_plane 2
        (\<lambda>x. phi x *
          slp_cauchy_transform right_orientation right_potential x)"
    by (rule slp_test_cauchy_product_l2[OF
          p_lower p_upper right_potential_lp phi_test])
  have signed_product_L2:
      "aim_complex_lp_on_plane 2
        (\<lambda>x. -(phi x *
          slp_cauchy_transform right_orientation right_potential x))"
    using product_L2 unfolding aim_complex_lp_on_plane_def by simp
  show ?thesis
    by (rule
      slp_mixed_center_finite_weighted_absolute_mass_left_cauchy_unit_finite[OF
        B_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable left_potential_lp right_potential_lp root_weight_lp
        root_weight_outside cutoff_bound root_support cutoff_support
        left_potential_support right_potential_support signed_product_L2])
qed

theorem slp_mixed_center_finite_weighted_absolute_mass_right_cross_finite:
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
        cutoff right_potential
        (slp_cauchy_transform right_orientation right_potential)
        (\<lambda>x. -(phi x *
          slp_cauchy_transform left_orientation left_potential x))
        center \<partial>lborel) < top_class.top"
proof -
  have product_L2:
      "aim_complex_lp_on_plane 2
        (\<lambda>x. phi x *
          slp_cauchy_transform left_orientation left_potential x)"
    by (rule slp_test_cauchy_product_l2[OF
          p_lower p_upper left_potential_lp phi_test])
  have signed_product_L2:
      "aim_complex_lp_on_plane 2
        (\<lambda>x. -(phi x *
          slp_cauchy_transform left_orientation left_potential x))"
    using product_L2 unfolding aim_complex_lp_on_plane_def by simp
  show ?thesis
    by (rule
      slp_mixed_center_finite_weighted_absolute_mass_unit_right_cauchy_finite[OF
        B_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable left_potential_lp right_potential_lp root_weight_lp
        root_weight_outside cutoff_bound root_support cutoff_support
        left_potential_support right_potential_support signed_product_L2])
qed

end

end
