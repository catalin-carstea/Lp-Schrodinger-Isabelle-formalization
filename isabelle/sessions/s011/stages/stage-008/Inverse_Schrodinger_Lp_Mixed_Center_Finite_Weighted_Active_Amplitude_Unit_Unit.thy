theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Active_Amplitude_Unit_Unit
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Absolute_Mass_Unit_Unit"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Amplitude_From_Mass"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Active integrability of the literal unit--unit amplitude\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_mixed_center_finite_weighted_active_amplitude_unit_unit_integrable:
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
  shows
    "AE center in lborel.
      integrable lborel
        (slp_mixed_center_finite_weighted_active_complex_amplitude root_weight
          cutoff left_potential (\<lambda>_. 1) cutoff right_potential
          (\<lambda>_. 1)
          (\<lambda>x. phi x *
            (slp_cauchy_transform left_orientation left_potential x *
              slp_cauchy_transform right_orientation right_potential x))
          center ::
          real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
            \<Rightarrow> complex)"
proof -
  let ?unit_terminal = "\<lambda>_ :: slp_point. 1 :: complex"
  let ?left_cauchy =
    "slp_cauchy_transform left_orientation left_potential"
  let ?right_cauchy =
    "slp_cauchy_transform right_orientation right_potential"
  let ?center_factor = "\<lambda>x. phi x * (?left_cauchy x * ?right_cauchy x)"
  have root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    using root_weight_lp unfolding aim_complex_lp_on_plane_def by blast
  have left_potential_measurable:
      "left_potential \<in> borel_measurable lborel"
    using left_potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have right_potential_measurable:
      "right_potential \<in> borel_measurable lborel"
    using right_potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have unit_terminal_measurable:
      "?unit_terminal \<in> borel_measurable lborel"
    by measurable
  have left_cauchy_measurable:
      "?left_cauchy \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF
          p_lower p_upper left_potential_lp])
  have right_cauchy_measurable:
      "?right_cauchy \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF
          p_lower p_upper right_potential_lp])
  have phi_integrable: "integrable lborel phi"
    by (rule slp_test_function_integrable_bounded(1)[OF phi_test])
  have phi_measurable: "phi \<in> borel_measurable lborel"
    using phi_integrable by measurable
  have center_factor_measurable:
      "?center_factor \<in> borel_measurable lborel"
    using phi_measurable left_cauchy_measurable right_cauchy_measurable
    by measurable
  have mass_integral_finite:
      "(\<integral>\<^sup>+ center.
        slp_mixed_center_finite_weighted_absolute_fiber_mass
          TYPE('i) TYPE('j) root_weight cutoff left_potential ?unit_terminal
          cutoff right_potential ?unit_terminal ?center_factor center
          \<partial>lborel) < top_class.top"
    by (rule
      slp_mixed_center_finite_weighted_absolute_mass_unit_unit_two_cauchy_finite[OF
        B_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
        phi_test cutoff_measurable left_potential_lp right_potential_lp
        root_weight_lp root_weight_outside cutoff_bound root_support
        cutoff_support left_potential_support right_potential_support])
  show ?thesis
    by (rule
      slp_mixed_center_finite_weighted_active_amplitude_integrable_from_mass[OF
        root_weight_measurable cutoff_measurable left_potential_measurable
        unit_terminal_measurable cutoff_measurable right_potential_measurable
        unit_terminal_measurable center_factor_measurable
        mass_integral_finite])
qed

end

end
