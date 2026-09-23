theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Active_Amplitude_Cauchy
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Amplitude_Cauchy_Fiber_Integrable"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Active_Integral_Transport"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Weighted amplitude on active Cartesian coordinates\<close>

definition slp_mixed_center_finite_weighted_active_complex_amplitude ::
    "(slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      slp_point \<Rightarrow>
      real^((unit + ((('i::finite + 'i) + unit) + ('j::finite + 'j)))
        \<times> bool) \<Rightarrow> complex"
where
  "slp_mixed_center_finite_weighted_active_complex_amplitude root_weight
      left_cutoff left_potential left_terminal_value right_cutoff
      right_potential right_terminal_value center_factor center x =
    slp_mixed_center_finite_weighted_complex_amplitude root_weight
      left_cutoff left_potential left_terminal_value right_cutoff
      right_potential right_terminal_value center_factor center
      (slp_mixed_center_finite_active_unpack x)"

theorem slp_mixed_center_finite_weighted_active_complex_amplitude_pack:
  fixes coordinates ::
    "('i::finite, 'j::finite) slp_mixed_center_finite_coordinates"
  shows
    "slp_mixed_center_finite_weighted_active_complex_amplitude root_weight
        left_cutoff left_potential left_terminal_value right_cutoff
        right_potential right_terminal_value center_factor center
        (slp_mixed_center_finite_active_pack coordinates) =
      slp_mixed_center_finite_weighted_complex_amplitude root_weight
        left_cutoff left_potential left_terminal_value right_cutoff
        right_potential right_terminal_value center_factor center coordinates"
  unfolding slp_mixed_center_finite_weighted_active_complex_amplitude_def
  by (simp only: slp_mixed_center_finite_active_unpack_pack)

theorem slp_mixed_center_finite_weighted_active_complex_amplitude_measurable:
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
  shows
    "(slp_mixed_center_finite_weighted_active_complex_amplitude root_weight
        left_cutoff left_potential left_terminal_value right_cutoff
        right_potential right_terminal_value center_factor center ::
      real^((unit + ((('i::finite + 'i) + unit) + ('j::finite + 'j)))
        \<times> bool) \<Rightarrow> complex) \<in> borel_measurable lborel"
proof -
  let ?finite_amplitude =
    "slp_mixed_center_finite_weighted_complex_amplitude root_weight
      left_cutoff left_potential left_terminal_value right_cutoff
      right_potential right_terminal_value center_factor ::
      slp_point \<Rightarrow>
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex"
  have joint_lborel_measurable:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        ?finite_amplitude (fst z) (snd z))) \<in> borel_measurable lborel"
    by (rule
      slp_mixed_center_finite_weighted_complex_amplitude_measurable[OF
        root_weight_measurable left_cutoff_measurable
        left_potential_measurable left_terminal_measurable
        right_cutoff_measurable right_potential_measurable
        right_terminal_measurable center_factor_measurable])
  have joint_measurable:
      "case_prod ?finite_amplitude \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using joint_lborel_measurable
    by (simp only: lborel_prod split_beta')
  have finite_section_measurable:
      "?finite_amplitude center \<in> borel_measurable lborel"
  proof -
    have center_space: "center \<in> space (lborel :: slp_point measure)"
      by simp
    note raw = measurable_compose_Pair1[OF center_space joint_measurable]
    show ?thesis
      using raw by simp
  qed
  have composed:
      "(?finite_amplitude center \<circ>
        (slp_mixed_center_finite_active_unpack ::
          real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool) \<Rightarrow>
            ('i, 'j) slp_mixed_center_finite_coordinates)) \<in>
        borel_measurable lborel"
    by (rule measurable_comp[OF
          slp_mixed_center_finite_active_unpack_measurable
          finite_section_measurable])
  show ?thesis
    using composed
    unfolding slp_mixed_center_finite_weighted_active_complex_amplitude_def
      comp_def .
qed

context aim_planar_riesz_hls_cauchy
begin

theorem slp_mixed_center_finite_weighted_active_amplitude_cauchy_integrable:
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
        (slp_mixed_center_finite_weighted_active_complex_amplitude root_weight
          cutoff left_potential
          (slp_cauchy_transform left_orientation left_potential) cutoff
          right_potential
          (slp_cauchy_transform right_orientation right_potential)
          center_factor center ::
          real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
            \<Rightarrow> complex)"
proof -
  let ?left_terminal =
    "slp_cauchy_transform left_orientation left_potential"
  let ?right_terminal =
    "slp_cauchy_transform right_orientation right_potential"
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
  have finite_integrable:
      "AE center in lborel.
        integrable lborel
          (slp_mixed_center_finite_weighted_complex_amplitude root_weight
            cutoff left_potential ?left_terminal cutoff right_potential
            ?right_terminal center_factor center ::
            ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    by (rule
      slp_mixed_center_finite_weighted_amplitude_cauchy_fiber_integrable[OF
        B_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable center_factor_measurable left_potential_lp
        right_potential_lp root_weight_lp root_weight_outside cutoff_bound
        center_factor_bound root_support cutoff_support left_potential_support
        right_potential_support])
  show ?thesis
    using finite_integrable
  proof eventually_elim
    fix center
    assume finite:
      "integrable lborel
        (slp_mixed_center_finite_weighted_complex_amplitude root_weight cutoff
          left_potential ?left_terminal cutoff right_potential ?right_terminal
          center_factor center ::
          ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    have active_measurable:
        "(slp_mixed_center_finite_weighted_active_complex_amplitude root_weight
            cutoff left_potential ?left_terminal cutoff right_potential
            ?right_terminal center_factor center ::
          real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
            \<Rightarrow> complex) \<in> borel_measurable lborel"
      by (rule
        slp_mixed_center_finite_weighted_active_complex_amplitude_measurable[OF
          root_weight_measurable cutoff_measurable
          left_potential_measurable left_terminal_measurable
          cutoff_measurable right_potential_measurable
          right_terminal_measurable center_factor_measurable])
    note transport = slp_mixed_center_finite_active_integrable_iff[
      OF active_measurable]
    show
      "integrable lborel
        (slp_mixed_center_finite_weighted_active_complex_amplitude root_weight
          cutoff left_potential ?left_terminal cutoff right_potential
          ?right_terminal center_factor center ::
          real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
            \<Rightarrow> complex)"
      using transport finite
      by (simp only:
        slp_mixed_center_finite_weighted_active_complex_amplitude_pack)
  qed
qed

end

end
