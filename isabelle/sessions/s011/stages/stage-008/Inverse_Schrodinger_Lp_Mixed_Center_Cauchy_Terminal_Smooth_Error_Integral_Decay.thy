theory Inverse_Schrodinger_Lp_Mixed_Center_Cauchy_Terminal_Smooth_Error_Integral_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Ennreal_Majorant_Complex_Integral_Decay"
begin

section \<open>The literal mixed smooth-error integral\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_mixed_center_finite_weighted_cauchy_terminal_smooth_error_integral_decay:
  fixes B C p :: real
    and X :: "slp_point set"
    and cutoff left_potential right_potential root_weight phi ::
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
    and uniform_convergence:
      "uniform_limit UNIV (\<lambda>tau. slp_center_average tau phi) phi
        at_top"
  shows
    "((\<lambda>tau. integral\<^sup>L lborel
      (slp_mixed_center_finite_weighted_oscillatory_kernel
        TYPE('i::finite) TYPE('j::finite) tau root_weight cutoff
        left_potential
        (slp_cauchy_transform left_orientation left_potential) cutoff
        right_potential
        (slp_cauchy_transform right_orientation right_potential)
        (\<lambda>center. slp_center_average tau phi center - phi center)))
      \<longlongrightarrow> 0) at_top"
proof -
  let ?left_terminal =
    "slp_cauchy_transform left_orientation left_potential"
  let ?right_terminal =
    "slp_cauchy_transform right_orientation right_potential"
  let ?error =
    "\<lambda>tau center. slp_center_average tau phi center - phi center"
  let ?density =
    "slp_mixed_center_density (2 * B) cutoff left_potential right_potential
      (\<lambda>x. ennreal (cmod (?left_terminal x)))
      (\<lambda>x. ennreal (cmod (?right_terminal x)))
      CARD('i) CARD('j) root_weight"
  let ?majorant =
    "\<lambda>tau center. ?density center * ennreal (norm (?error tau center))"
  let ?kernel =
    "\<lambda>tau.
      slp_mixed_center_finite_weighted_oscillatory_kernel
        TYPE('i) TYPE('j) tau root_weight cutoff left_potential
        ?left_terminal cutoff right_potential ?right_terminal (?error tau)"
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
  note phi_data = slp_test_function_integrable_bounded[OF phi_test]
  have phi_integrable: "integrable lborel phi"
    by (rule phi_data(1))
  have phi_measurable: "phi \<in> borel_measurable lborel"
    using phi_integrable by measurable
  obtain K where phi_bound: "\<And>x. norm (phi x) \<le> K"
    using phi_data(2) unfolding bounded_iff by blast
  have error_measurable:
      "\<And>tau. ?error tau \<in> borel_measurable lborel"
    using slp_center_average_measurable[OF phi_integrable] phi_measurable
    by measurable
  have error_bound:
      "\<And>tau x. norm (?error tau x) \<le>
        norm (of_real (tau / pi) :: complex) *
          integral\<^sup>L lborel (\<lambda>z. norm (phi z)) + K"
  proof -
    fix tau x
    have center_bound:
        "norm (slp_center_average tau phi x) \<le>
          norm (of_real (tau / pi) :: complex) *
            integral\<^sup>L lborel (\<lambda>z. norm (phi z))"
      by (rule slp_center_average_fixed_tau_bound)
    have triangle:
        "norm (?error tau x) \<le>
          norm (slp_center_average tau phi x) + norm (phi x)"
      by (rule norm_triangle_ineq4)
    show "norm (?error tau x) \<le>
        norm (of_real (tau / pi) :: complex) *
          integral\<^sup>L lborel (\<lambda>z. norm (phi z)) + K"
      by (rule order_trans[OF triangle])
        (rule add_mono[OF center_bound phi_bound])
  qed
  have kernel_measurable:
      "\<And>tau. ?kernel tau \<in> borel_measurable lborel"
  proof -
    fix tau
    show "?kernel tau \<in> borel_measurable lborel"
      by (rule
        slp_mixed_center_finite_weighted_oscillatory_cauchy_kernel_properties(1)[
          where B = B and C = C and p = p and X = X
            and D = "norm (of_real (tau / pi) :: complex) *
              integral\<^sup>L lborel (\<lambda>z. norm (phi z)) + K",
          OF B_nonnegative C_nonnegative p_lower p_upper X_measurable
            X_bounded cutoff_measurable error_measurable left_potential_lp
            right_potential_lp root_weight_lp root_weight_outside cutoff_bound
            error_bound root_support cutoff_support left_potential_support
            right_potential_support])
  qed
  have kernel_absolute_bound:
      "\<And>tau. AE center in lborel.
        ennreal (norm (?kernel tau center)) \<le>
        slp_mixed_center_finite_weighted_absolute_fiber_mass
          TYPE('i) TYPE('j) root_weight cutoff left_potential ?left_terminal
          cutoff right_potential ?right_terminal (?error tau) center"
  proof -
    fix tau
    show "AE center in lborel.
        ennreal (norm (?kernel tau center)) \<le>
        slp_mixed_center_finite_weighted_absolute_fiber_mass
          TYPE('i) TYPE('j) root_weight cutoff left_potential ?left_terminal
          cutoff right_potential ?right_terminal (?error tau) center"
      by (rule
        slp_mixed_center_finite_weighted_oscillatory_cauchy_kernel_properties(2)[
          where B = B and C = C and p = p and X = X
            and D = "norm (of_real (tau / pi) :: complex) *
              integral\<^sup>L lborel (\<lambda>z. norm (phi z)) + K",
          OF B_nonnegative C_nonnegative p_lower p_upper X_measurable
            X_bounded cutoff_measurable error_measurable left_potential_lp
            right_potential_lp root_weight_lp root_weight_outside cutoff_bound
            error_bound root_support cutoff_support left_potential_support
            right_potential_support])
  qed
  have fiber_mass_bound:
      "\<And>tau center.
        slp_mixed_center_finite_weighted_absolute_fiber_mass
          TYPE('i) TYPE('j) root_weight cutoff left_potential ?left_terminal
          cutoff right_potential ?right_terminal (?error tau) center \<le>
        ?majorant tau center"
  proof -
    fix tau center
    have raw_bound:
        "slp_mixed_center_finite_weighted_absolute_fiber_mass
            TYPE('i) TYPE('j) root_weight cutoff left_potential
            ?left_terminal cutoff right_potential ?right_terminal
            (?error tau) center \<le>
          ennreal (norm (?error tau center)) * ?density center"
      by (rule
        slp_mixed_center_finite_weighted_absolute_fiber_mass_density_bound[OF
          B_nonnegative root_weight_measurable cutoff_measurable
          left_potential_measurable left_terminal_measurable
          right_potential_measurable right_terminal_measurable root_support
          cutoff_support left_potential_support right_potential_support])
    show "slp_mixed_center_finite_weighted_absolute_fiber_mass
          TYPE('i) TYPE('j) root_weight cutoff left_potential ?left_terminal
          cutoff right_potential ?right_terminal (?error tau) center \<le>
        ?majorant tau center"
      using raw_bound by (simp only: mult.commute)
  qed
  have kernel_bound:
      "\<And>tau. AE center in lborel.
        ennreal (norm (?kernel tau center)) \<le> ?majorant tau center"
    using kernel_absolute_bound
  proof eventually_elim
    fix tau center
    assume absolute_bound:
        "ennreal (norm (?kernel tau center)) \<le>
          slp_mixed_center_finite_weighted_absolute_fiber_mass
            TYPE('i) TYPE('j) root_weight cutoff left_potential
            ?left_terminal cutoff right_potential ?right_terminal
            (?error tau) center"
    show "ennreal (norm (?kernel tau center)) \<le> ?majorant tau center"
      by (rule order_trans[OF absolute_bound fiber_mass_bound])
  qed
  have majorant_decay:
      "((\<lambda>tau. \<integral>\<^sup>+ center. ?majorant tau center \<partial>lborel)
        \<longlongrightarrow> 0) at_top"
    by (rule
      slp_mixed_center_density_cauchy_terminal_smooth_error_mass_decay[OF
        B_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable left_potential_lp right_potential_lp root_weight_lp
        root_weight_outside cutoff_bound C_nonnegative cutoff_support
        left_potential_support right_potential_support phi_integrable
        uniform_convergence])
  show ?thesis
    by (rule
      slp_complex_kernel_integral_tendsto_zero_from_ennreal_majorant[OF
        kernel_measurable kernel_bound majorant_decay])
qed

end

end
