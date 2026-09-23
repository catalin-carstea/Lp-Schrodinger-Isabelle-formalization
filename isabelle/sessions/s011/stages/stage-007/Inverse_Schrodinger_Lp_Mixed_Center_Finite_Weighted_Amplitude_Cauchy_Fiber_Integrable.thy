theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Amplitude_Cauchy_Fiber_Integrable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Absolute_Mass_Cauchy"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Complex_Amplitude_Measurable"
begin

section \<open>A.e. integrability of the weighted finite mixed amplitude\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_mixed_center_finite_weighted_amplitude_cauchy_fiber_integrable:
  fixes left_dummy :: "'i::finite itself"
    and right_dummy :: "'j::finite itself"
    and B C D p :: real
    and X :: "slp_point set"
    and root_weight cutoff left_potential right_potential center_factor ::
      slp_scalar_field
    and left_orientation right_orientation :: slp_cauchy_orientation
  assumes B_nonnegative: "0 \<le> B"
    and C_nonnegative: "0 \<le> C"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and center_factor_measurable:
      "center_factor \<in> borel_measurable lborel"
    and left_potential_lp: "aim_complex_lp_on_plane p left_potential"
    and right_potential_lp: "aim_complex_lp_on_plane p right_potential"
    and root_weight_lp: "aim_complex_lp_on_plane p root_weight"
    and root_weight_outside:
      "\<And>x. x \<notin> X \<Longrightarrow> root_weight x = 0"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and center_factor_bound: "\<And>x. cmod (center_factor x) \<le> D"
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
        (slp_mixed_center_finite_weighted_complex_amplitude root_weight
          cutoff left_potential
          (slp_cauchy_transform left_orientation left_potential) cutoff
          right_potential
          (slp_cauchy_transform right_orientation right_potential)
          center_factor center ::
          ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
proof -
  let ?left_terminal =
    "slp_cauchy_transform left_orientation left_potential"
  let ?right_terminal =
    "slp_cauchy_transform right_orientation right_potential"
  let ?amplitude =
    "slp_mixed_center_finite_weighted_complex_amplitude root_weight cutoff
      left_potential ?left_terminal cutoff right_potential ?right_terminal
      center_factor :: slp_point \<Rightarrow>
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex"
  let ?mass =
    "slp_mixed_center_finite_weighted_absolute_fiber_mass TYPE('i) TYPE('j)
      root_weight cutoff left_potential ?left_terminal cutoff right_potential
      ?right_terminal center_factor"
  have root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    using root_weight_lp unfolding aim_complex_lp_on_plane_def by blast
  have left_potential_measurable:
      "left_potential \<in> borel_measurable lborel"
    using left_potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have right_potential_measurable:
      "right_potential \<in> borel_measurable lborel"
    using right_potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have left_terminal_measurable:
      "?left_terminal \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF
          p_lower p_upper left_potential_lp])
  have right_terminal_measurable:
      "?right_terminal \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF
          p_lower p_upper right_potential_lp])
  have amplitude_lborel_measurable:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        ?amplitude (fst z) (snd z))) \<in> borel_measurable lborel"
    by (rule
      slp_mixed_center_finite_weighted_complex_amplitude_measurable[OF
        root_weight_measurable cutoff_measurable left_potential_measurable
        left_terminal_measurable cutoff_measurable
        right_potential_measurable right_terminal_measurable
        center_factor_measurable])
  have amplitude_measurable:
      "case_prod ?amplitude \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using amplitude_lborel_measurable
    by (simp only: lborel_prod split_beta')
  have amplitude_section_measurable:
      "?amplitude center \<in> borel_measurable lborel"
    for center
  proof -
    have center_space: "center \<in> space (lborel :: slp_point measure)"
      by simp
    note raw = measurable_compose_Pair1[OF center_space amplitude_measurable]
    show ?thesis
      using raw by simp
  qed
  have absolute_integrand_measurable:
      "case_prod (\<lambda>(center :: slp_point)
          (coordinates :: ('i, 'j) slp_mixed_center_finite_coordinates).
        ennreal (cmod (?amplitude center coordinates))) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using amplitude_measurable by measurable
  have mass_measurable: "?mass \<in> borel_measurable lborel"
  proof -
    note raw = lborel.borel_measurable_nn_integral[
      OF absolute_integrand_measurable]
    show ?thesis
      using raw
      unfolding slp_mixed_center_finite_weighted_absolute_fiber_mass_def
      by (simp only: split_beta')
  qed
  have mass_integral_finite:
      "nn_integral lborel ?mass < top_class.top"
    by (rule
      slp_mixed_center_finite_weighted_absolute_mass_cauchy_finite[OF
        B_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable left_potential_lp right_potential_lp root_weight_lp
        root_weight_outside cutoff_bound center_factor_bound root_support
        cutoff_support left_potential_support right_potential_support])
  have mass_finite: "AE center in lborel. ?mass center \<noteq> top_class.top"
  proof -
    have mass_integral_not_infinity:
        "nn_integral lborel ?mass \<noteq> \<infinity>"
      using mass_integral_finite by simp
    note raw = nn_integral_PInf_AE[where M = lborel and f = ?mass]
    show ?thesis
      using raw[OF mass_measurable mass_integral_not_infinity] by simp
  qed
  show ?thesis
    using mass_finite
  proof eventually_elim
    fix center
    assume finite: "?mass center \<noteq> top_class.top"
    show "integrable lborel (?amplitude center)"
      unfolding integrable_iff_bounded
      using amplitude_section_measurable[of center] finite
      unfolding slp_mixed_center_finite_weighted_absolute_fiber_mass_def
      by (simp add: less_top)
  qed
qed

end

end
