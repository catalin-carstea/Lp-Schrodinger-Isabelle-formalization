theory Inverse_Schrodinger_Lp_Mixed_Product_Pairing_Uniform_Holder_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Mixed_Product_Pairing_Holder_Bound"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Oscillatory_Kernel_Product_Power_Integral_Bound"
begin

section \<open>Frequency-uniform quantitative bound for the literal pairing\<close>

context aim_planar_riesz_hls
begin

theorem slp_mixed_center_finite_oscillatory_kernel_product_pairing_uniform_holder_bound:
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
    "norm_class.norm
        (integral\<^sup>L lborel
          (\<lambda>center. F center *
            slp_mixed_center_finite_oscillatory_kernel TYPE('i::finite)
              TYPE('j::finite) frequency root_weight cutoff left_potential
              cutoff right_potential center)) \<le>
      (integral\<^sup>L lborel
        (\<lambda>center. norm_class.norm (F center) powr
          slp_mixed_product_exponent p)) powr
        (1 / slp_mixed_product_exponent p) *
      (integral\<^sup>L lborel
        (\<lambda>center.
          enn2real
            (slp_mixed_center_density (2 * B) cutoff left_potential
              right_potential (\<lambda>_. 1) (\<lambda>_. 1) CARD('i) CARD('j)
              root_weight center)
            powr slp_mixed_product_dual_exponent p)) powr
        (1 / slp_mixed_product_dual_exponent p)"
proof -
  let ?q = "slp_mixed_product_exponent p"
  let ?r = "slp_mixed_product_dual_exponent p"
  let ?kernel =
    "slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j) frequency
      root_weight cutoff left_potential cutoff right_potential"
  let ?density =
    "slp_mixed_center_density (2 * B) cutoff left_potential right_potential
      (\<lambda>_. 1) (\<lambda>_. 1) CARD('i) CARD('j) root_weight"
  let ?amplitude_power =
    "integral\<^sup>L lborel
      (\<lambda>center. norm_class.norm (F center) powr ?q)"
  let ?kernel_power =
    "integral\<^sup>L lborel
      (\<lambda>center. norm_class.norm (?kernel center) powr ?r)"
  let ?density_power =
    "integral\<^sup>L lborel
      (\<lambda>center. enn2real (?density center) powr ?r)"
  note exponents = slp_mixed_product_duality_exponents[OF p_lower p_upper]
  have pairing_bound:
      "norm_class.norm
          (integral\<^sup>L lborel (\<lambda>center. F center * ?kernel center)) \<le>
        ?amplitude_power powr (1 / ?q) *
          ?kernel_power powr (1 / ?r)"
    by (rule
      slp_mixed_center_finite_oscillatory_kernel_product_pairing_holder_bound[
        OF B_nonnegative p_lower p_upper F_lp X_measurable X_bounded
          cutoff_measurable left_potential_lp right_potential_lp
          root_weight_lp root_weight_outside cutoff_bound C_nonnegative
          root_support cutoff_support left_potential_support
          right_potential_support])
  have kernel_power_bound: "?kernel_power \<le> ?density_power"
    by (rule
      slp_mixed_center_finite_oscillatory_kernel_product_power_integral_bound[
        OF B_nonnegative p_lower p_upper X_measurable X_bounded
          cutoff_measurable left_potential_lp right_potential_lp
          root_weight_lp root_weight_outside cutoff_bound C_nonnegative
          root_support cutoff_support left_potential_support
          right_potential_support])
  have reciprocal_nonnegative: "0 \<le> 1 / ?r"
    using exponents(3) by simp
  have kernel_power_nonnegative: "0 \<le> ?kernel_power"
    by (rule integral_nonneg_AE) simp
  have powered_kernel_bound:
      "?kernel_power powr (1 / ?r) \<le>
        ?density_power powr (1 / ?r)"
    by (rule powr_mono2[OF reciprocal_nonnegative kernel_power_nonnegative
          kernel_power_bound])
  have product_bound:
      "?amplitude_power powr (1 / ?q) *
          ?kernel_power powr (1 / ?r) \<le>
        ?amplitude_power powr (1 / ?q) *
          ?density_power powr (1 / ?r)"
    by (rule mult_left_mono[OF powered_kernel_bound]) simp
  show ?thesis
    by (rule order_trans[OF pairing_bound product_bound])
qed

end

end
