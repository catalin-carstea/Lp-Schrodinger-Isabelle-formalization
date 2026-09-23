theory Inverse_Schrodinger_Lp_Mixed_Product_Rough_Smooth_Difference_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Mixed_Product_Rough_Pairing_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Mixed_Product_Smooth_Pairing_Decay"
begin

section \<open>Rough-minus-smooth literal product pairing\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_mixed_center_finite_oscillatory_kernel_rough_smooth_cauchy_product_difference_decay:
  fixes active_type ::
      "((unit + (((('i::finite) + 'i) + unit) + (('j::finite) + 'j)))
        \<times> bool) itself"
    and B C p :: real
    and X :: "slp_point set"
    and phi root_weight cutoff left_potential right_potential ::
      slp_scalar_field
    and left_orientation right_orientation :: slp_cauchy_orientation
  assumes stationary_phase:
      "hormander_quadratic_stationary_phase_decay_claim active_type"
    and density: "evans_compact_smooth_l1_density_claim active_type"
    and B_nonnegative: "0 \<le> B"
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
    "((\<lambda>frequency.
      integral\<^sup>L lborel
        (\<lambda>center.
          (slp_cauchy_transform left_orientation left_potential center *
            slp_cauchy_transform right_orientation right_potential center) *
          slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j)
            frequency root_weight cutoff left_potential cutoff
            right_potential center) -
      integral\<^sup>L lborel
        (\<lambda>center.
          (phi center *
            (slp_cauchy_transform left_orientation left_potential center *
              slp_cauchy_transform right_orientation right_potential center)) *
          slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j)
            frequency root_weight cutoff left_potential cutoff
            right_potential center))
      \<longlongrightarrow> 0) at_top"
proof -
  have rough_decay:
      "((\<lambda>frequency.
        integral\<^sup>L lborel
          (\<lambda>center.
            (slp_cauchy_transform left_orientation left_potential center *
              slp_cauchy_transform right_orientation right_potential center) *
            slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j)
              frequency root_weight cutoff left_potential cutoff
              right_potential center))
        \<longlongrightarrow> 0) at_top"
    by (rule
      slp_mixed_center_finite_oscillatory_kernel_rough_cauchy_product_pairing_decay[
        OF stationary_phase density B_nonnegative C_nonnegative p_lower
          p_upper X_measurable X_bounded cutoff_measurable left_potential_lp
          right_potential_lp root_weight_lp root_weight_outside cutoff_bound
          root_support cutoff_support left_potential_support
          right_potential_support])
  have smooth_decay:
      "((\<lambda>frequency.
        integral\<^sup>L lborel
          (\<lambda>center.
            (phi center *
              (slp_cauchy_transform left_orientation left_potential center *
                slp_cauchy_transform right_orientation right_potential
                  center)) *
            slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j)
              frequency root_weight cutoff left_potential cutoff
              right_potential center))
        \<longlongrightarrow> 0) at_top"
    by (rule
      slp_mixed_center_finite_oscillatory_kernel_smooth_cauchy_product_pairing_decay[
        OF stationary_phase density B_nonnegative C_nonnegative p_lower
          p_upper X_measurable X_bounded phi_test cutoff_measurable
          left_potential_lp right_potential_lp root_weight_lp
          root_weight_outside cutoff_bound root_support cutoff_support
          left_potential_support right_potential_support])
  show ?thesis
    using tendsto_diff[OF rough_decay smooth_decay] by simp
qed

end

end
