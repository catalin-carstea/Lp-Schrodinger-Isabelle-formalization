theory Inverse_Schrodinger_Lp_Mixed_Product_Smooth_Pairing_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Oscillatory_Unit_Unit_Global_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Unit_Kernel_Factorization"
begin

section \<open>Smooth Cauchy-product pairing decay for the literal kernel\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_mixed_center_finite_oscillatory_kernel_smooth_cauchy_product_pairing_decay:
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
          (phi center *
            (slp_cauchy_transform left_orientation left_potential center *
              slp_cauchy_transform right_orientation right_potential center)) *
          slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j)
            frequency root_weight cutoff left_potential cutoff
            right_potential center))
      \<longlongrightarrow> 0) at_top"
proof -
  let ?center_factor = "\<lambda>x. phi x *
    (slp_cauchy_transform left_orientation left_potential x *
      slp_cauchy_transform right_orientation right_potential x)"
  let ?weighted = "\<lambda>frequency.
    slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) frequency root_weight cutoff left_potential
      (\<lambda>_. 1) cutoff right_potential (\<lambda>_. 1) ?center_factor"
  let ?literal = "\<lambda>frequency.
    slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j) frequency
      root_weight cutoff left_potential cutoff right_potential"
  have weighted_decay:
      "((\<lambda>frequency. integral\<^sup>L lborel (?weighted frequency))
        \<longlongrightarrow> 0) at_top"
    by (rule
      slp_mixed_center_finite_weighted_oscillatory_unit_unit_global_decay[OF
        stationary_phase density B_nonnegative C_nonnegative p_lower p_upper
        X_measurable X_bounded phi_test cutoff_measurable left_potential_lp
        right_potential_lp root_weight_lp root_weight_outside cutoff_bound
        root_support cutoff_support left_potential_support
        right_potential_support])
  have transport:
      "(\<lambda>frequency. integral\<^sup>L lborel (?weighted frequency)) =
        (\<lambda>frequency. integral\<^sup>L lborel
          (\<lambda>center. ?center_factor center * ?literal frequency center))"
  proof (rule ext)
    fix frequency
    have integrand_eq:
        "?weighted frequency =
          (\<lambda>center. ?center_factor center * ?literal frequency center)"
    proof (rule ext)
      fix center
      show "?weighted frequency center =
          ?center_factor center * ?literal frequency center"
        by (simp only:
          slp_mixed_center_finite_weighted_oscillatory_kernel_unit_factorization
          mult.commute)
    qed
    show "integral\<^sup>L lborel (?weighted frequency) =
        integral\<^sup>L lborel
          (\<lambda>center. ?center_factor center * ?literal frequency center)"
      by (simp only: integrand_eq)
  qed
  show ?thesis
    using weighted_decay by (simp only: transport)
qed

end

end
