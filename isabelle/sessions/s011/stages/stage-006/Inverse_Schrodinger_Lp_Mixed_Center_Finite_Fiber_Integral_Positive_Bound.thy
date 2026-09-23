theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Fiber_Integral_Positive_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Amplitude_Fiber_Integrable"
begin

section \<open>Measurable finite mixed fiber integral and positive bound\<close>

context aim_planar_riesz_hls
begin

theorem slp_mixed_center_finite_fiber_integral_measurable_and_positive_bound:
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
    "(\<lambda>center :: slp_point.
      slp_mixed_center_finite_fiber_integral TYPE('i::finite)
        TYPE('j::finite) frequency root_weight cutoff left_potential cutoff
        right_potential center :: complex) \<in> borel_measurable lborel"
    and
    "AE center in lborel.
      ennreal (norm_class.norm
        (slp_mixed_center_finite_fiber_integral TYPE('i) TYPE('j) frequency
          root_weight cutoff left_potential cutoff right_potential center)) \<le>
      slp_mixed_center_finite_positive_fiber_mass TYPE('i) TYPE('j) (2 * B)
        root_weight cutoff left_potential cutoff right_potential center"
proof -
  have left_potential_measurable[measurable]:
      "left_potential \<in> borel_measurable lborel"
    using left_potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have right_potential_measurable[measurable]:
      "right_potential \<in> borel_measurable lborel"
    using right_potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have root_weight_measurable[measurable]:
      "root_weight \<in> borel_measurable lborel"
    using root_weight_integrable unfolding integrable_iff_bounded by blast
  have amplitude_integrable:
      "AE center in lborel.
        integrable lborel
          (slp_mixed_center_finite_complex_amplitude root_weight cutoff
            left_potential cutoff right_potential center ::
            ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    by (rule slp_mixed_center_finite_complex_amplitude_fiber_integrable[OF
          B_nonnegative p_lower p_upper cutoff_measurable left_potential_lp
          right_potential_lp cutoff_bound C_nonnegative
          root_weight_integrable root_support cutoff_support
          left_potential_support right_potential_support])
  note generic =
    slp_mixed_center_finite_fiber_integral_measurable_and_bound[OF
      root_weight_measurable cutoff_measurable left_potential_measurable
      cutoff_measurable right_potential_measurable amplitude_integrable,
      where frequency = frequency]
  show
      "(\<lambda>center :: slp_point.
        slp_mixed_center_finite_fiber_integral TYPE('i) TYPE('j) frequency
          root_weight cutoff left_potential cutoff right_potential center ::
          complex) \<in> borel_measurable lborel"
    by (rule generic(1))
  from generic(2) show
      "AE center in lborel.
        ennreal (norm_class.norm
          (slp_mixed_center_finite_fiber_integral TYPE('i) TYPE('j) frequency
            root_weight cutoff left_potential cutoff right_potential center)) \<le>
        slp_mixed_center_finite_positive_fiber_mass TYPE('i) TYPE('j) (2 * B)
          root_weight cutoff left_potential cutoff right_potential center"
  proof eventually_elim
    fix center
    assume integral_le_absolute:
      "ennreal (norm_class.norm
          (slp_mixed_center_finite_fiber_integral TYPE('i) TYPE('j) frequency
            root_weight cutoff left_potential cutoff right_potential center)) \<le>
        slp_mixed_center_finite_absolute_fiber_mass TYPE('i) TYPE('j)
          root_weight cutoff left_potential cutoff right_potential center"
    have absolute_le_positive:
      "slp_mixed_center_finite_absolute_fiber_mass TYPE('i) TYPE('j)
          root_weight cutoff left_potential cutoff right_potential center \<le>
        slp_mixed_center_finite_positive_fiber_mass TYPE('i) TYPE('j) (2 * B)
          root_weight cutoff left_potential cutoff right_potential center"
      by (rule slp_mixed_center_finite_absolute_fiber_mass_le_positive[OF
            B_nonnegative root_support cutoff_support left_potential_support
            cutoff_support right_potential_support])
    show
      "ennreal (norm_class.norm
          (slp_mixed_center_finite_fiber_integral TYPE('i) TYPE('j) frequency
            root_weight cutoff left_potential cutoff right_potential center)) \<le>
        slp_mixed_center_finite_positive_fiber_mass TYPE('i) TYPE('j) (2 * B)
          root_weight cutoff left_potential cutoff right_potential center"
      by (rule order_trans[OF integral_le_absolute absolute_le_positive])
  qed
qed

end

end
