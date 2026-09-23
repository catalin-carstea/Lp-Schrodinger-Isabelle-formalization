theory Inverse_Schrodinger_Lp_Mixed_Product_Pairing_Integrable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Oscillatory_Kernel_Product_Dual_Lp"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Complex_Lp_Product_Closures"
begin

section \<open>Bochner integrability of the literal product pairing\<close>

context aim_planar_riesz_hls
begin

theorem slp_mixed_center_finite_oscillatory_kernel_product_pairing_integrable:
  fixes frequency B C p :: real
    and X :: "slp_point set"
    and F cutoff left_potential right_potential root_weight ::
      "slp_point \<Rightarrow> complex"
  assumes B_nonnegative: "0 \<le> B"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and F_lp: "aim_complex_lp_on_plane (slp_mixed_product_exponent p) F"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and left_potential_lp: "aim_complex_lp_on_plane p left_potential"
    and right_potential_lp: "aim_complex_lp_on_plane p right_potential"
    and root_weight_lp: "aim_complex_lp_on_plane p root_weight"
    and root_weight_outside: "\<And>x. x \<notin> X \<Longrightarrow> root_weight x = 0"
    and cutoff_bound:
      "\<And>x. Real_Vector_Spaces.norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and root_support:
      "\<And>x. root_weight x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> Real_Vector_Spaces.norm x \<le> B"
    and left_potential_support:
      "\<And>x. left_potential x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and right_potential_support:
      "\<And>x. right_potential x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
  shows
    "integrable lborel
      (\<lambda>center. F center *
        slp_mixed_center_finite_oscillatory_kernel TYPE('i::finite)
          TYPE('j::finite) frequency root_weight cutoff left_potential cutoff
          right_potential center)"
    and
    "norm_class.norm
        (integral\<^sup>L lborel
          (\<lambda>center. F center *
            slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j)
              frequency root_weight cutoff left_potential cutoff
              right_potential center)) \<le>
      integral\<^sup>L lborel
        (\<lambda>center. norm_class.norm
          (F center *
            slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j)
              frequency root_weight cutoff left_potential cutoff
              right_potential center))"
proof -
  let ?q = "slp_mixed_product_exponent p"
  let ?r = "slp_mixed_product_dual_exponent p"
  let ?kernel =
    "slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j) frequency
      root_weight cutoff left_potential cutoff right_potential"
  note exponents = slp_mixed_product_duality_exponents[OF p_lower p_upper]
  have kernel_lp: "aim_complex_lp_on_plane ?r ?kernel"
    by (rule
      slp_mixed_center_finite_oscillatory_kernel_product_dual_lp[
        OF B_nonnegative p_lower p_upper X_measurable X_bounded
          cutoff_measurable left_potential_lp right_potential_lp
          root_weight_lp root_weight_outside cutoff_bound C_nonnegative
          root_support cutoff_support left_potential_support
          right_potential_support])
  have product_lp:
      "aim_complex_lp_on_plane 1 (\<lambda>center. F center * ?kernel center)"
    by (rule slp_aim_complex_lp_on_plane_product[
          where a = 1 and q = ?q and r = ?r,
          OF zero_less_one _ _ _ F_lp kernel_lp])
      (use exponents in simp_all)
  have product_measurable:
      "(\<lambda>center. F center * ?kernel center)
        \<in> borel_measurable lborel"
    using product_lp unfolding aim_complex_lp_on_plane_def by blast
  have product_norm_integrable:
      "integrable lborel
        (\<lambda>center. norm_class.norm (F center * ?kernel center))"
    using product_lp unfolding aim_complex_lp_on_plane_def by simp
  have product_integrable:
      "integrable lborel (\<lambda>center. F center * ?kernel center)"
    using Bochner_Integration.integrable_norm_iff[OF product_measurable]
      product_norm_integrable by blast
  show "integrable lborel (\<lambda>center. F center * ?kernel center)"
    by (rule product_integrable)
  show
      "norm_class.norm
          (integral\<^sup>L lborel
            (\<lambda>center. F center * ?kernel center)) \<le>
        integral\<^sup>L lborel
          (\<lambda>center. norm_class.norm (F center * ?kernel center))"
    by (rule Bochner_Integration.integral_norm_bound)
qed

end

end
