theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Amplitude_Fiber_Integrable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Positive_Fiber_Mass_Measurable"
begin

section \<open>A.e. integrability of the finite mixed amplitude fiber\<close>

context aim_planar_riesz_hls
begin

theorem slp_mixed_center_finite_complex_amplitude_fiber_integrable:
  fixes B C p :: real
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
    "AE center in lborel.
      integrable lborel
        (slp_mixed_center_finite_complex_amplitude root_weight cutoff
          left_potential cutoff right_potential center ::
          ('i::finite, 'j::finite) slp_mixed_center_finite_coordinates
            \<Rightarrow> complex)"
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
  have positive_mass_measurable:
      "(\<lambda>center.
        slp_mixed_center_finite_positive_fiber_mass TYPE('i) TYPE('j)
          (2 * B) root_weight cutoff left_potential cutoff right_potential
          center) \<in> borel_measurable lborel"
    by (rule slp_mixed_center_finite_positive_fiber_mass_measurable[OF
          root_weight_measurable cutoff_measurable left_potential_measurable
          cutoff_measurable right_potential_measurable])
  have positive_mass_integral_finite:
      "nn_integral lborel (\<lambda>center.
        slp_mixed_center_finite_positive_fiber_mass TYPE('i) TYPE('j)
          (2 * B) root_weight cutoff left_potential cutoff right_potential
          center) < top_class.top"
    by (rule slp_mixed_center_finite_positive_mass_finite[OF _ p_lower
          p_upper cutoff_measurable left_potential_lp right_potential_lp
          cutoff_bound C_nonnegative root_weight_integrable])
       (use B_nonnegative in linarith)
  have positive_mass_finite:
      "AE center in lborel.
        slp_mixed_center_finite_positive_fiber_mass TYPE('i) TYPE('j)
          (2 * B) root_weight cutoff left_potential cutoff right_potential
          center \<noteq> top_class.top"
  proof -
    have integral_not_infinity:
        "nn_integral lborel (\<lambda>center.
          slp_mixed_center_finite_positive_fiber_mass TYPE('i) TYPE('j)
            (2 * B) root_weight cutoff left_potential cutoff right_potential
            center) \<noteq> \<infinity>"
      using positive_mass_integral_finite by simp
    note raw = nn_integral_PInf_AE[
      where M = lborel and
        f = "slp_mixed_center_finite_positive_fiber_mass TYPE('i) TYPE('j)
          (2 * B) root_weight cutoff left_potential cutoff right_potential"]
    have raw_ae:
        "AE center in lborel.
          slp_mixed_center_finite_positive_fiber_mass TYPE('i) TYPE('j)
            (2 * B) root_weight cutoff left_potential cutoff right_potential
            center \<noteq> \<infinity>"
      by (rule raw[OF positive_mass_measurable integral_not_infinity])
    show ?thesis
      using raw_ae by simp
  qed
  have amplitude_lborel_measurable:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_mixed_center_finite_complex_amplitude root_weight cutoff
          left_potential cutoff right_potential (fst z) (snd z)))
        \<in> borel_measurable lborel"
    by (rule slp_mixed_center_finite_complex_amplitude_measurable[OF
          root_weight_measurable cutoff_measurable left_potential_measurable
          cutoff_measurable right_potential_measurable])
  have amplitude_measurable:
      "case_prod (slp_mixed_center_finite_complex_amplitude root_weight
          cutoff left_potential cutoff right_potential ::
        slp_point \<Rightarrow>
          ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using amplitude_lborel_measurable
    by (simp only: lborel_prod split_beta')
  have amplitude_section_measurable:
      "(slp_mixed_center_finite_complex_amplitude root_weight cutoff
          left_potential cutoff right_potential center ::
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)
        \<in> borel_measurable lborel"
    for center
  proof -
    have center_space: "center \<in> space (lborel :: slp_point measure)"
      by simp
    note raw = measurable_compose_Pair1[OF center_space amplitude_measurable]
    show ?thesis
      using raw by simp
  qed
  show ?thesis
    using positive_mass_finite
  proof eventually_elim
    fix center
    assume mass_finite:
      "slp_mixed_center_finite_positive_fiber_mass TYPE('i) TYPE('j)
        (2 * B) root_weight cutoff left_potential cutoff right_potential
        center \<noteq> top_class.top"
    have absolute_le:
        "slp_mixed_center_finite_absolute_fiber_mass TYPE('i) TYPE('j)
            root_weight cutoff left_potential cutoff right_potential center \<le>
          slp_mixed_center_finite_positive_fiber_mass TYPE('i) TYPE('j)
            (2 * B) root_weight cutoff left_potential cutoff right_potential
            center"
      by (rule slp_mixed_center_finite_absolute_fiber_mass_le_positive[OF
            B_nonnegative root_support cutoff_support left_potential_support
            cutoff_support right_potential_support])
    have absolute_finite:
        "slp_mixed_center_finite_absolute_fiber_mass TYPE('i) TYPE('j)
          root_weight cutoff left_potential cutoff right_potential center <
          top_class.top"
      using absolute_le mass_finite by (simp add: less_top)
    show
      "integrable lborel
        (slp_mixed_center_finite_complex_amplitude root_weight cutoff
          left_potential cutoff right_potential center ::
          ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
      unfolding integrable_iff_bounded
      using amplitude_section_measurable[of center] absolute_finite
      unfolding slp_mixed_center_finite_absolute_fiber_mass_def
        slp_parameterized_complex_absolute_fiber_mass_def
      by simp
  qed
qed

end

end
