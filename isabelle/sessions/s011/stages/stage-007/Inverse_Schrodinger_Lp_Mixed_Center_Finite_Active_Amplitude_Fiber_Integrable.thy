theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Active_Amplitude_Fiber_Integrable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Active_Integral_Transport"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Amplitude_Fiber_Integrable"
begin

hide_const (open) Commutative_Ring.norm

section \<open>A.e. integrability of the active finite mixed amplitude\<close>

context aim_planar_riesz_hls
begin

theorem slp_mixed_center_finite_active_complex_amplitude_fiber_integrable:
  fixes B C p :: real
    and cutoff left_potential right_potential root_weight ::
      "slp_point \<Rightarrow> complex"
  assumes B_nonnegative: "0 \<le> B"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and left_potential_lp: "aim_complex_lp_on_plane p left_potential"
    and right_potential_lp: "aim_complex_lp_on_plane p right_potential"
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
        (slp_mixed_center_finite_active_complex_amplitude root_weight cutoff
          left_potential cutoff right_potential center ::
          real^((unit + ((('i::finite + 'i) + unit) + ('j::finite + 'j)))
            \<times> bool) \<Rightarrow> complex)"
proof -
  have left_potential_measurable:
      "left_potential \<in> borel_measurable lborel"
    using left_potential_lp
    unfolding aim_complex_lp_on_plane_def by blast
  have right_potential_measurable:
      "right_potential \<in> borel_measurable lborel"
    using right_potential_lp
    unfolding aim_complex_lp_on_plane_def by blast
  have root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    using root_weight_integrable
    unfolding integrable_iff_bounded by blast
  have active_measurable:
      "(slp_mixed_center_finite_active_complex_amplitude root_weight cutoff
          left_potential cutoff right_potential center ::
        real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
          \<Rightarrow> complex) \<in>
        borel_measurable lborel"
    for center
    by (rule
          slp_mixed_center_finite_active_complex_amplitude_measurable[OF
            root_weight_measurable cutoff_measurable
            left_potential_measurable cutoff_measurable
            right_potential_measurable])
  have finite_integrable:
      "AE center in lborel.
        integrable lborel
          (slp_mixed_center_finite_complex_amplitude root_weight cutoff
            left_potential cutoff right_potential center ::
            ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow>
              complex)"
    by (rule slp_mixed_center_finite_complex_amplitude_fiber_integrable[OF
          B_nonnegative p_lower p_upper cutoff_measurable
          left_potential_lp right_potential_lp cutoff_bound C_nonnegative
          root_weight_integrable root_support cutoff_support
          left_potential_support right_potential_support])
  show ?thesis
    using finite_integrable
  proof eventually_elim
    fix center
    assume finite:
      "integrable lborel
        (slp_mixed_center_finite_complex_amplitude root_weight cutoff
          left_potential cutoff right_potential center ::
          ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    have transport:
        "integrable lborel
            (slp_mixed_center_finite_active_complex_amplitude root_weight
              cutoff left_potential cutoff right_potential center ::
              real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
                \<Rightarrow> complex) \<longleftrightarrow>
          integrable lborel
            (slp_mixed_center_finite_complex_amplitude root_weight cutoff
              left_potential cutoff right_potential center ::
              ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow>
                complex)"
    proof -
      note raw = slp_mixed_center_finite_active_integrable_iff[
        OF active_measurable[of center]]
      show ?thesis
        using raw
        by (simp only:
              slp_mixed_center_finite_active_complex_amplitude_pack)
    qed
    show
      "integrable lborel
        (slp_mixed_center_finite_active_complex_amplitude root_weight cutoff
          left_potential cutoff right_potential center ::
          real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
            \<Rightarrow> complex)"
      using transport finite by blast
  qed
qed

end

end
