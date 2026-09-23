theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Amplitude_From_Mass
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Active_Amplitude_Cauchy"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Oscillatory_Cauchy_Kernel"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Absolute_Mass_Cross_Terms"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Weighted amplitude integrability from global absolute mass\<close>

theorem slp_mixed_center_finite_weighted_amplitude_fiber_integrable_from_mass:
  fixes left_dummy :: "'i::finite itself"
    and right_dummy :: "'j::finite itself"
    and root_weight left_cutoff left_potential left_terminal_value
      right_cutoff right_potential right_terminal_value center_factor ::
      slp_scalar_field
  assumes root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    and left_cutoff_measurable:
      "left_cutoff \<in> borel_measurable lborel"
    and left_potential_measurable:
      "left_potential \<in> borel_measurable lborel"
    and left_terminal_measurable:
      "left_terminal_value \<in> borel_measurable lborel"
    and right_cutoff_measurable:
      "right_cutoff \<in> borel_measurable lborel"
    and right_potential_measurable:
      "right_potential \<in> borel_measurable lborel"
    and right_terminal_measurable:
      "right_terminal_value \<in> borel_measurable lborel"
    and center_factor_measurable:
      "center_factor \<in> borel_measurable lborel"
    and mass_integral_finite:
      "(\<integral>\<^sup>+ center.
        slp_mixed_center_finite_weighted_absolute_fiber_mass
          TYPE('i) TYPE('j) root_weight left_cutoff left_potential
          left_terminal_value right_cutoff right_potential
          right_terminal_value center_factor center \<partial>lborel) <
        top_class.top"
  shows
    "AE center in lborel.
      integrable lborel
        (slp_mixed_center_finite_weighted_complex_amplitude root_weight
          left_cutoff left_potential left_terminal_value right_cutoff
          right_potential right_terminal_value center_factor center ::
          ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
proof -
  let ?amplitude =
    "slp_mixed_center_finite_weighted_complex_amplitude root_weight
      left_cutoff left_potential left_terminal_value right_cutoff
      right_potential right_terminal_value center_factor ::
      slp_point \<Rightarrow>
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex"
  let ?mass =
    "slp_mixed_center_finite_weighted_absolute_fiber_mass
      TYPE('i) TYPE('j) root_weight left_cutoff left_potential
      left_terminal_value right_cutoff right_potential right_terminal_value
      center_factor"
  have amplitude_lborel_measurable:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        ?amplitude (fst z) (snd z))) \<in> borel_measurable lborel"
    by (rule
      slp_mixed_center_finite_weighted_complex_amplitude_measurable[OF
        root_weight_measurable left_cutoff_measurable
        left_potential_measurable left_terminal_measurable
        right_cutoff_measurable right_potential_measurable
        right_terminal_measurable center_factor_measurable])
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
  have mass_measurable: "?mass \<in> borel_measurable lborel"
    by (rule
      slp_mixed_center_finite_weighted_absolute_fiber_mass_measurable[OF
        root_weight_measurable left_cutoff_measurable
        left_potential_measurable left_terminal_measurable
        right_cutoff_measurable right_potential_measurable
        right_terminal_measurable center_factor_measurable])
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

theorem slp_mixed_center_finite_weighted_active_amplitude_integrable_from_mass:
  fixes left_dummy :: "'i::finite itself"
    and right_dummy :: "'j::finite itself"
    and root_weight left_cutoff left_potential left_terminal_value
      right_cutoff right_potential right_terminal_value center_factor ::
      slp_scalar_field
  assumes root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    and left_cutoff_measurable:
      "left_cutoff \<in> borel_measurable lborel"
    and left_potential_measurable:
      "left_potential \<in> borel_measurable lborel"
    and left_terminal_measurable:
      "left_terminal_value \<in> borel_measurable lborel"
    and right_cutoff_measurable:
      "right_cutoff \<in> borel_measurable lborel"
    and right_potential_measurable:
      "right_potential \<in> borel_measurable lborel"
    and right_terminal_measurable:
      "right_terminal_value \<in> borel_measurable lborel"
    and center_factor_measurable:
      "center_factor \<in> borel_measurable lborel"
    and mass_integral_finite:
      "(\<integral>\<^sup>+ center.
        slp_mixed_center_finite_weighted_absolute_fiber_mass
          TYPE('i) TYPE('j) root_weight left_cutoff left_potential
          left_terminal_value right_cutoff right_potential
          right_terminal_value center_factor center \<partial>lborel) <
        top_class.top"
  shows
    "AE center in lborel.
      integrable lborel
        (slp_mixed_center_finite_weighted_active_complex_amplitude root_weight
          left_cutoff left_potential left_terminal_value right_cutoff
          right_potential right_terminal_value center_factor center ::
          real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
            \<Rightarrow> complex)"
proof -
  have finite_integrable:
      "AE center in lborel.
        integrable lborel
          (slp_mixed_center_finite_weighted_complex_amplitude root_weight
            left_cutoff left_potential left_terminal_value right_cutoff
            right_potential right_terminal_value center_factor center ::
            ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    by (rule
      slp_mixed_center_finite_weighted_amplitude_fiber_integrable_from_mass[OF
        root_weight_measurable left_cutoff_measurable
        left_potential_measurable left_terminal_measurable
        right_cutoff_measurable right_potential_measurable
        right_terminal_measurable center_factor_measurable
        mass_integral_finite])
  show ?thesis
    using finite_integrable
  proof eventually_elim
    fix center
    assume finite:
      "integrable lborel
        (slp_mixed_center_finite_weighted_complex_amplitude root_weight
          left_cutoff left_potential left_terminal_value right_cutoff
          right_potential right_terminal_value center_factor center ::
          ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    have active_measurable:
        "(slp_mixed_center_finite_weighted_active_complex_amplitude root_weight
            left_cutoff left_potential left_terminal_value right_cutoff
            right_potential right_terminal_value center_factor center ::
          real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
            \<Rightarrow> complex) \<in> borel_measurable lborel"
      by (rule
        slp_mixed_center_finite_weighted_active_complex_amplitude_measurable[OF
          root_weight_measurable left_cutoff_measurable
          left_potential_measurable left_terminal_measurable
          right_cutoff_measurable right_potential_measurable
          right_terminal_measurable center_factor_measurable])
    note transport = slp_mixed_center_finite_active_integrable_iff[OF
      active_measurable]
    show
      "integrable lborel
        (slp_mixed_center_finite_weighted_active_complex_amplitude root_weight
          left_cutoff left_potential left_terminal_value right_cutoff
          right_potential right_terminal_value center_factor center ::
          real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
            \<Rightarrow> complex)"
      using transport finite
      by (simp only:
        slp_mixed_center_finite_weighted_active_complex_amplitude_pack)
  qed
qed

context aim_planar_riesz_hls_cauchy
begin

theorem slp_mixed_center_finite_weighted_active_amplitude_cross_integrable:
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
  shows left:
    "AE center in lborel.
      integrable lborel
        (slp_mixed_center_finite_weighted_active_complex_amplitude root_weight
          cutoff left_potential
          (slp_cauchy_transform left_orientation left_potential) cutoff
          right_potential (\<lambda>_. 1)
          (\<lambda>x. -(phi x *
            slp_cauchy_transform right_orientation right_potential x))
          center ::
          real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
            \<Rightarrow> complex)"
    and right:
    "AE center in lborel.
      integrable lborel
        (slp_mixed_center_finite_weighted_active_complex_amplitude root_weight
          cutoff left_potential (\<lambda>_. 1) cutoff right_potential
          (slp_cauchy_transform right_orientation right_potential)
          (\<lambda>x. -(phi x *
            slp_cauchy_transform left_orientation left_potential x))
          center ::
          real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
            \<Rightarrow> complex)"
proof -
  let ?left_terminal =
    "slp_cauchy_transform left_orientation left_potential"
  let ?right_terminal =
    "slp_cauchy_transform right_orientation right_potential"
  let ?left_center = "\<lambda>x. -(phi x * ?right_terminal x)"
  let ?right_center = "\<lambda>x. -(phi x * ?left_terminal x)"
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
  have phi_integrable: "integrable lborel phi"
    by (rule slp_test_function_integrable_bounded(1)[OF phi_test])
  have phi_measurable: "phi \<in> borel_measurable lborel"
    using phi_integrable unfolding integrable_iff_bounded by blast
  have unit_measurable:
      "(\<lambda>_ :: slp_point. (1 :: complex)) \<in> borel_measurable lborel"
    by measurable
  have left_center_measurable:
      "?left_center \<in> borel_measurable lborel"
    using phi_measurable right_terminal_measurable by measurable
  have right_center_measurable:
      "?right_center \<in> borel_measurable lborel"
    using phi_measurable left_terminal_measurable by measurable
  have left_mass:
      "(\<integral>\<^sup>+ center.
        slp_mixed_center_finite_weighted_absolute_fiber_mass
          TYPE('i) TYPE('j) root_weight cutoff left_potential ?left_terminal
          cutoff right_potential (\<lambda>_. 1) ?left_center center
          \<partial>lborel) < top_class.top"
    by (rule
      slp_mixed_center_finite_weighted_absolute_mass_left_cross_finite[OF
        B_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
        phi_test cutoff_measurable left_potential_lp right_potential_lp
        root_weight_lp root_weight_outside cutoff_bound root_support
        cutoff_support left_potential_support right_potential_support])
  have right_mass:
      "(\<integral>\<^sup>+ center.
        slp_mixed_center_finite_weighted_absolute_fiber_mass
          TYPE('i) TYPE('j) root_weight cutoff left_potential (\<lambda>_. 1)
          cutoff right_potential ?right_terminal ?right_center center
          \<partial>lborel) < top_class.top"
    by (rule
      slp_mixed_center_finite_weighted_absolute_mass_right_cross_finite[OF
        B_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
        phi_test cutoff_measurable left_potential_lp right_potential_lp
        root_weight_lp root_weight_outside cutoff_bound root_support
        cutoff_support left_potential_support right_potential_support])
  show
    "AE center in lborel.
      integrable lborel
        (slp_mixed_center_finite_weighted_active_complex_amplitude root_weight
          cutoff left_potential ?left_terminal cutoff right_potential
          (\<lambda>_. 1) ?left_center center ::
          real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
            \<Rightarrow> complex)"
    by (rule
      slp_mixed_center_finite_weighted_active_amplitude_integrable_from_mass[OF
        root_weight_measurable cutoff_measurable left_potential_measurable
        left_terminal_measurable cutoff_measurable right_potential_measurable
        unit_measurable left_center_measurable left_mass])
  show
    "AE center in lborel.
      integrable lborel
        (slp_mixed_center_finite_weighted_active_complex_amplitude root_weight
          cutoff left_potential (\<lambda>_. 1) cutoff right_potential
          ?right_terminal ?right_center center ::
          real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
            \<Rightarrow> complex)"
    by (rule
      slp_mixed_center_finite_weighted_active_amplitude_integrable_from_mass[OF
        root_weight_measurable cutoff_measurable left_potential_measurable
        unit_measurable cutoff_measurable right_potential_measurable
        right_terminal_measurable right_center_measurable right_mass])
qed

end

end
