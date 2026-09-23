theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Oscillatory_Kernel
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Fiber_Integral_Integrable"
begin

section \<open>Finite-type mixed oscillatory center kernel\<close>

definition slp_mixed_center_finite_oscillatory_kernel ::
    "('i::finite) itself \<Rightarrow> ('j::finite) itself \<Rightarrow> real \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      slp_point \<Rightarrow> complex"
where
  "slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j) frequency
      root_weight left_cutoff left_potential right_cutoff right_potential
      center =
    slp_mixed_center_finite_fiber_integral TYPE('i) TYPE('j) frequency
      root_weight left_cutoff left_potential right_cutoff right_potential
      center"

context aim_planar_riesz_hls
begin

theorem slp_mixed_center_finite_oscillatory_kernel_properties:
  fixes frequency B C p :: real
    and cutoff left_potential right_potential root_weight ::
      "slp_point \<Rightarrow> complex"
  assumes B_nonnegative: "0 \<le> B"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and left_potential_lp:
      "aim_complex_lp_on_plane p left_potential"
    and right_potential_lp:
      "aim_complex_lp_on_plane p right_potential"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and root_weight_integrable: "integrable lborel root_weight"
    and root_support:
      "\<And>x. root_weight x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and left_potential_support:
      "\<And>x. left_potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and right_potential_support:
      "\<And>x. right_potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
  shows
    "(slp_mixed_center_finite_oscillatory_kernel TYPE('i::finite)
        TYPE('j::finite) frequency root_weight cutoff left_potential cutoff
        right_potential) \<in> borel_measurable lborel"
    and
    "AE center in lborel.
      ennreal (norm_class.norm
        (slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j)
          frequency root_weight cutoff left_potential cutoff right_potential
          center)) \<le>
      slp_mixed_center_finite_positive_fiber_mass TYPE('i) TYPE('j) (2 * B)
        root_weight cutoff left_potential cutoff right_potential center"
    and
    "integrable lborel
      (slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j)
        frequency root_weight cutoff left_potential cutoff right_potential)"
proof -
  note measurable_and_bound =
    slp_mixed_center_finite_fiber_integral_measurable_and_positive_bound[OF
      B_nonnegative p_lower p_upper cutoff_measurable left_potential_lp
      right_potential_lp cutoff_bound C_nonnegative root_weight_integrable
      root_support cutoff_support left_potential_support
      right_potential_support, where frequency = frequency]
  have fiber_integrable:
      "integrable lborel
        (\<lambda>center :: slp_point.
          slp_mixed_center_finite_fiber_integral TYPE('i) TYPE('j) frequency
            root_weight cutoff left_potential cutoff right_potential center ::
            complex)"
    by (rule slp_mixed_center_finite_fiber_integral_integrable[OF
          B_nonnegative p_lower p_upper cutoff_measurable left_potential_lp
          right_potential_lp cutoff_bound C_nonnegative
          root_weight_integrable root_support cutoff_support
          left_potential_support right_potential_support])
  show
      "(slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j)
        frequency root_weight cutoff left_potential cutoff right_potential)
        \<in> borel_measurable lborel"
    using measurable_and_bound(1)
    unfolding slp_mixed_center_finite_oscillatory_kernel_def .
  show
      "AE center in lborel.
        ennreal (norm_class.norm
          (slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j)
            frequency root_weight cutoff left_potential cutoff right_potential
            center)) \<le>
        slp_mixed_center_finite_positive_fiber_mass TYPE('i) TYPE('j) (2 * B)
          root_weight cutoff left_potential cutoff right_potential center"
    using measurable_and_bound(2)
    unfolding slp_mixed_center_finite_oscillatory_kernel_def .
  show
      "integrable lborel
        (slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j)
          frequency root_weight cutoff left_potential cutoff right_potential)"
    using fiber_integrable
    unfolding slp_mixed_center_finite_oscillatory_kernel_def .
qed

end

end
