theory Inverse_Schrodinger_Lp_Mixed_Product_Rough_Pairing_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Mixed_Product_Duality_Density_Closure"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Mixed_Product_Pairing_Integrable"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Test_Two_Cauchy_Product_Half_HLS"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Mixed_Product_Pairing_Uniform_Holder_Bound"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Mixed_Product_Smooth_Pairing_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Smooth_Cutoff_Approximation"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Density closure for the rough Cauchy-product pairing\<close>

context aim_planar_riesz_hls_cauchy
begin

lemma slp_cauchy_product_mixed_exponent_lp:
  assumes p_lower: "1 < p"
    and p_upper: "p < 2"
    and left_potential_lp:
      "aim_complex_lp_on_plane p left_potential"
    and right_potential_lp:
      "aim_complex_lp_on_plane p right_potential"
  shows
    "aim_complex_lp_on_plane (slp_mixed_product_exponent p)
      (\<lambda>x.
        slp_cauchy_transform left_orientation left_potential x *
          slp_cauchy_transform right_orientation right_potential x)"
proof -
  let ?r = "aim_hls_target_exponent p"
  have target_above_two: "2 < ?r"
    by (rule slp_hls_target_exponent_above_two[OF p_lower p_upper])
  have half_target_positive: "0 < ?r / 2"
    using target_above_two by linarith
  have left_cauchy_lp:
      "aim_complex_lp_on_plane ?r
        (slp_cauchy_transform left_orientation left_potential)"
  proof (cases left_orientation)
    case SLP_Partial_Inverse
    then show ?thesis
      using slp_both_cauchy_hls p_lower p_upper left_potential_lp by blast
  next
    case SLP_Dbar_Inverse
    then show ?thesis
      using slp_both_cauchy_hls p_lower p_upper left_potential_lp by blast
  qed
  have right_cauchy_lp:
      "aim_complex_lp_on_plane ?r
        (slp_cauchy_transform right_orientation right_potential)"
  proof (cases right_orientation)
    case SLP_Partial_Inverse
    then show ?thesis
      using slp_both_cauchy_hls p_lower p_upper right_potential_lp by blast
  next
    case SLP_Dbar_Inverse
    then show ?thesis
      using slp_both_cauchy_hls p_lower p_upper right_potential_lp by blast
  qed
  have product_lp:
      "aim_complex_lp_on_plane (?r / 2)
        (\<lambda>x.
          slp_cauchy_transform left_orientation left_potential x *
            slp_cauchy_transform right_orientation right_potential x)"
    by (rule slp_aim_complex_lp_on_plane_product[
          where q = ?r and r = ?r, OF half_target_positive])
      (use target_above_two left_cauchy_lp right_cauchy_lp in simp_all)
  show ?thesis
    using product_lp by (simp only: slp_mixed_product_exponent_def)
qed

theorem slp_mixed_center_finite_oscillatory_kernel_rough_cauchy_product_pairing_decay:
  fixes active_type ::
      "((unit + (((('i::finite) + 'i) + unit) + (('j::finite) + 'j)))
        \<times> bool) itself"
    and B C p :: real
    and X :: "slp_point set"
    and root_weight cutoff left_potential right_potential :: slp_scalar_field
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
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and left_potential_lp: "aim_complex_lp_on_plane p left_potential"
    and right_potential_lp: "aim_complex_lp_on_plane p right_potential"
    and root_weight_lp: "aim_complex_lp_on_plane p root_weight"
    and root_weight_outside:
      "\<And>x. x \<notin> X \<Longrightarrow> root_weight x = 0"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and root_support:
      "\<And>x. root_weight x \<noteq> 0 \<Longrightarrow> norm_class.norm x \<le> B"
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm_class.norm x \<le> B"
    and left_potential_support:
      "\<And>x. left_potential x \<noteq> 0 \<Longrightarrow> norm_class.norm x \<le> B"
    and right_potential_support:
      "\<And>x. right_potential x \<noteq> 0 \<Longrightarrow> norm_class.norm x \<le> B"
  shows
    "((\<lambda>frequency.
      integral\<^sup>L lborel
        (\<lambda>center.
          (slp_cauchy_transform left_orientation left_potential center *
            slp_cauchy_transform right_orientation right_potential center) *
          slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j)
            frequency root_weight cutoff left_potential cutoff
            right_potential center))
      \<longlongrightarrow> 0) at_top"
proof -
  let ?q = "slp_mixed_product_exponent p"
  let ?r = "slp_mixed_product_dual_exponent p"
  let ?rough =
    "\<lambda>x. slp_cauchy_transform left_orientation left_potential x *
      slp_cauchy_transform right_orientation right_potential x"
  let ?kernel =
    "\<lambda>frequency.
      slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j)
        frequency root_weight cutoff left_potential cutoff right_potential"
  let ?pairing =
    "\<lambda>frequency F. integral\<^sup>L lborel
      (\<lambda>center. F center * ?kernel frequency center)"
  let ?size =
    "\<lambda>F. (integral\<^sup>L lborel
      (\<lambda>center. norm_class.norm (F center) powr ?q)) powr (1 / ?q)"
  let ?density =
    "slp_mixed_center_density (2 * B) cutoff left_potential right_potential
      (\<lambda>_. 1) (\<lambda>_. 1) CARD('i) CARD('j) root_weight"
  let ?D =
    "(integral\<^sup>L lborel
      (\<lambda>center. enn2real (?density center) powr ?r)) powr (1 / ?r)"
  let ?tests =
    "{u. \<exists>phi. slp_test_function_on UNIV phi \<and>
      u = (\<lambda>x. phi x * ?rough x)}"

  note exponents = slp_mixed_product_duality_exponents[OF p_lower p_upper]
  have q_positive: "0 < ?q"
    using exponents(2) by simp
  have rough_lp: "aim_complex_lp_on_plane ?q ?rough"
    by (rule slp_cauchy_product_mixed_exponent_lp[OF p_lower p_upper
          left_potential_lp right_potential_lp])
  have D_nonnegative: "0 \<le> ?D"
    by simp
  have K_positive: "0 < 1 + ?D"
    using D_nonnegative by linarith
  have size_nonnegative: "0 \<le> ?size F" for F
    by simp

  have approximation:
      "\<And>epsilon. 0 < epsilon \<Longrightarrow>
        \<exists>u\<in>?tests. ?size (?rough - u) < epsilon"
  proof -
    fix epsilon :: real
    assume epsilon_positive: "0 < epsilon"
    obtain phi where phi_test: "slp_test_function_on UNIV phi"
      and phi_close:
        "(integral\<^sup>L lborel
          (\<lambda>x. norm_class.norm (?rough x - phi x * ?rough x) powr ?q))
          powr (1 / ?q) < epsilon"
      using slp_aim_complex_lp_on_plane_smooth_cutoff_approximation[
        OF q_positive rough_lp epsilon_positive] by blast
    let ?u = "\<lambda>x. phi x * ?rough x"
    have u_test: "?u \<in> ?tests"
      using phi_test by blast
    have close: "?size (?rough - ?u) < epsilon"
      using phi_close by (simp add: fun_diff_def)
    show "\<exists>u\<in>?tests. ?size (?rough - u) < epsilon"
      using u_test close by blast
  qed

  have uniform_remainder:
      "\<And>frequency u. u \<in> ?tests \<Longrightarrow>
        norm_class.norm (?pairing frequency ?rough - ?pairing frequency u) \<le>
          (1 + ?D) * ?size (?rough - u)"
  proof -
    fix frequency :: real and u
    assume u_test: "u \<in> ?tests"
    obtain phi where phi_test: "slp_test_function_on UNIV phi"
      and u_def: "u = (\<lambda>x. phi x * ?rough x)"
      using u_test by blast
    have u_lp: "aim_complex_lp_on_plane ?q u"
      using slp_test_two_cauchy_product_half_hls_target_lp[
        OF p_lower p_upper left_potential_lp right_potential_lp phi_test]
      by (simp only: u_def slp_mixed_product_exponent_def)
    have difference_lp:
        "aim_complex_lp_on_plane ?q (\<lambda>x. ?rough x - u x)"
      by (rule aim_complex_lp_on_plane_diff[OF q_positive rough_lp u_lp])
    have rough_integrable:
        "integrable lborel
          (\<lambda>x. ?rough x * ?kernel frequency x)"
      by (rule
        slp_mixed_center_finite_oscillatory_kernel_product_pairing_integrable(1)[
          OF B_nonnegative p_lower p_upper rough_lp X_measurable X_bounded
            cutoff_measurable left_potential_lp right_potential_lp
            root_weight_lp root_weight_outside cutoff_bound C_nonnegative
            root_support cutoff_support left_potential_support
            right_potential_support])
    have u_integrable:
        "integrable lborel (\<lambda>x. u x * ?kernel frequency x)"
      by (rule
        slp_mixed_center_finite_oscillatory_kernel_product_pairing_integrable(1)[
          OF B_nonnegative p_lower p_upper u_lp X_measurable X_bounded
            cutoff_measurable left_potential_lp right_potential_lp
            root_weight_lp root_weight_outside cutoff_bound C_nonnegative
            root_support cutoff_support left_potential_support
            right_potential_support])
    have pairing_difference:
        "?pairing frequency ?rough - ?pairing frequency u =
          ?pairing frequency (\<lambda>x. ?rough x - u x)"
    proof -
      have integrand_difference:
          "(\<lambda>x. ?rough x * ?kernel frequency x -
            u x * ?kernel frequency x) =
           (\<lambda>x. (?rough x - u x) * ?kernel frequency x)"
        by (rule ext) (simp add: algebra_simps)
      have
          "?pairing frequency ?rough - ?pairing frequency u =
            integral\<^sup>L lborel
              (\<lambda>x. ?rough x * ?kernel frequency x -
                u x * ?kernel frequency x)"
        by (rule sym)
          (rule Bochner_Integration.integral_diff[OF rough_integrable
            u_integrable])
      also have "... = ?pairing frequency (\<lambda>x. ?rough x - u x)"
        by (simp only: integrand_difference)
      finally show ?thesis .
    qed
    have holder_bound:
        "norm_class.norm
            (?pairing frequency (\<lambda>x. ?rough x - u x)) \<le>
          ?size (\<lambda>x. ?rough x - u x) * ?D"
      by (rule
        slp_mixed_center_finite_oscillatory_kernel_product_pairing_uniform_holder_bound[
          OF B_nonnegative p_lower p_upper difference_lp X_measurable X_bounded
            cutoff_measurable left_potential_lp right_potential_lp
            root_weight_lp root_weight_outside cutoff_bound C_nonnegative
            root_support cutoff_support left_potential_support
            right_potential_support])
    have size_eq:
        "?size (\<lambda>x. ?rough x - u x) = ?size (?rough - u)"
      by (simp add: fun_diff_def)
    have scaled_bound:
        "?size (?rough - u) * ?D \<le> (1 + ?D) * ?size (?rough - u)"
    proof -
      have "?size (?rough - u) * ?D \<le>
          ?size (?rough - u) * (1 + ?D)"
        by (rule mult_left_mono) (use size_nonnegative in simp_all)
      then show ?thesis by (simp add: mult.commute)
    qed
    show
        "norm_class.norm (?pairing frequency ?rough - ?pairing frequency u) \<le>
          (1 + ?D) * ?size (?rough - u)"
      using holder_bound scaled_bound
      by (simp only: pairing_difference size_eq)
  qed

  have test_decay:
      "\<And>u. u \<in> ?tests \<Longrightarrow>
        ((\<lambda>frequency. ?pairing frequency u) \<longlongrightarrow> 0) at_top"
  proof -
    fix u
    assume u_test: "u \<in> ?tests"
    obtain phi where phi_test: "slp_test_function_on UNIV phi"
      and u_def: "u = (\<lambda>x. phi x * ?rough x)"
      using u_test by blast
    have decay:
        "((\<lambda>frequency.
          integral\<^sup>L lborel
            (\<lambda>center.
              (phi center * ?rough center) * ?kernel frequency center))
          \<longlongrightarrow> 0) at_top"
      by (rule
        slp_mixed_center_finite_oscillatory_kernel_smooth_cauchy_product_pairing_decay[
          OF stationary_phase density B_nonnegative C_nonnegative p_lower
            p_upper X_measurable X_bounded phi_test cutoff_measurable
            left_potential_lp right_potential_lp root_weight_lp
            root_weight_outside cutoff_bound root_support cutoff_support
            left_potential_support right_potential_support])
    show "((\<lambda>frequency. ?pairing frequency u) \<longlongrightarrow> 0) at_top"
      using decay by (simp only: u_def)
  qed

  have rough_decay:
      "((\<lambda>frequency. ?pairing frequency ?rough) \<longlongrightarrow> 0) at_top"
  proof (unfold tendsto_iff, intro allI impI)
    fix epsilon :: real
    assume epsilon_positive: "0 < epsilon"
    let ?delta = "epsilon / (2 * (1 + ?D))"
    have denominator_positive: "0 < 2 * (1 + ?D)"
      using K_positive by simp
    have delta_positive: "0 < ?delta"
      using epsilon_positive denominator_positive by (rule divide_pos_pos)
    obtain u where u_test: "u \<in> ?tests"
      and approximation_error: "?size (?rough - u) < ?delta"
      using approximation[OF delta_positive] by blast
    have u_decay:
        "((\<lambda>frequency. ?pairing frequency u) \<longlongrightarrow> 0) at_top"
      by (rule test_decay[OF u_test])
    have half_positive: "0 < epsilon / 2"
      using epsilon_positive by simp
    have eventually_u:
        "eventually
          (\<lambda>frequency. dist (?pairing frequency u) 0 < epsilon / 2)
          at_top"
      using u_decay half_positive unfolding tendsto_iff by blast
    show
        "eventually
          (\<lambda>frequency. dist (?pairing frequency ?rough) 0 < epsilon)
          at_top"
      using eventually_u
    proof eventually_elim
      fix frequency
      assume u_small: "dist (?pairing frequency u) 0 < epsilon / 2"
      have remainder_bound:
          "norm_class.norm
              (?pairing frequency ?rough - ?pairing frequency u) \<le>
            (1 + ?D) * ?size (?rough - u)"
        by (rule uniform_remainder[OF u_test])
      have scaled_error_small:
          "(1 + ?D) * ?size (?rough - u) < epsilon / 2"
      proof -
        have scaled_twice_less:
            "?size (?rough - u) * (2 * (1 + ?D)) < epsilon"
          using approximation_error
          by (simp only: pos_less_divide_eq[OF denominator_positive])
        show ?thesis
          apply (subst pos_less_divide_eq[OF zero_less_numeral])
          using scaled_twice_less
          by (simp add: algebra_simps)
      qed
      have remainder_small:
          "norm_class.norm
              (?pairing frequency ?rough - ?pairing frequency u) <
            epsilon / 2"
        using remainder_bound scaled_error_small by linarith
      have test_small:
          "norm_class.norm (?pairing frequency u) < epsilon / 2"
        using u_small by (simp add: dist_norm)
      have
          "norm_class.norm (?pairing frequency ?rough) \<le>
            norm_class.norm (?pairing frequency u) +
              norm_class.norm
                (?pairing frequency ?rough - ?pairing frequency u)"
        by (rule norm_triangle_sub)
      also have "... < epsilon / 2 + epsilon / 2"
        using test_small remainder_small by linarith
      also have "... = epsilon"
        by simp
      finally show "dist (?pairing frequency ?rough) 0 < epsilon"
        by (simp add: dist_norm)
    qed
  qed
  show ?thesis
    using rough_decay .
qed

end

end
