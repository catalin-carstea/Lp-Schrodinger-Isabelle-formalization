theory Inverse_Schrodinger_Lp_Mixed_Center_Left_Unit_Right_Cauchy_Error_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Graph_Finite_Center_Cauchy_Evaluated"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Absolute_Mass_One_Terminal"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Amplitude_From_Mass"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Center_Error_L2_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Ennreal_Majorant_Complex_Integral_Decay"
begin

hide_const (open) Commutative_Ring.norm

section \<open>The symmetric literal one-factor mixed center error\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_mixed_center_finite_left_unit_right_cauchy_error_integral_decay:
  fixes B C p :: real
    and X :: "slp_point set"
    and cutoff left_potential right_potential root_weight phi ::
      slp_scalar_field
    and left_orientation right_orientation :: slp_cauchy_orientation
  assumes fourier_plancherel:
      "hormander_euclidean_l2_fourier_plancherel_claim"
    and B_nonnegative: "0 \<le> B"
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
    "((\<lambda>tau. integral\<^sup>L lborel
      (slp_mixed_center_finite_weighted_oscillatory_kernel
        TYPE('i::finite) TYPE('j::finite) tau root_weight cutoff
        left_potential (\<lambda>_. 1) cutoff
        right_potential
        (slp_cauchy_transform right_orientation right_potential)
        (\<lambda>center.
          slp_center_average tau
              (\<lambda>x. phi x *
                slp_cauchy_transform left_orientation left_potential x)
              center -
            phi center *
              slp_cauchy_transform left_orientation left_potential center)))
      \<longlongrightarrow> 0) at_top"
proof -
  interpret hf: hormander_euclidean_l2_fourier_plancherel
    by standard (rule fourier_plancherel)
  let ?left_terminal =
    "slp_cauchy_transform left_orientation left_potential"
  let ?right_terminal =
    "slp_cauchy_transform right_orientation right_potential"
  let ?source = "\<lambda>x. phi x * ?left_terminal x"
  let ?actual_error =
    "\<lambda>tau center. slp_center_average tau ?source center - ?source center"
  let ?aux_error =
    "\<lambda>tau. if 0 < tau then ?actual_error tau else (\<lambda>_. 0)"
  let ?density =
    "slp_mixed_center_density (2 * B) cutoff left_potential right_potential
      (\<lambda>_. 1) (\<lambda>x. ennreal (cmod (?right_terminal x)))
      CARD('i) CARD('j) root_weight"
  let ?major_density =
    "slp_mixed_center_density (2 * B) cutoff left_potential right_potential
      (\<lambda>_. 1)
      (slp_positive_terminal_riesz_weight (2 * B) right_potential)
      CARD('i) CARD('j) root_weight"
  let ?majorant =
    "\<lambda>tau center.
      ennreal (norm (?aux_error tau center)) * ?major_density center"
  let ?kernel =
    "\<lambda>tau.
      slp_mixed_center_finite_weighted_oscillatory_kernel
        TYPE('i) TYPE('j) tau root_weight cutoff left_potential (\<lambda>_. 1) cutoff right_potential ?right_terminal (?aux_error tau)"
  let ?actual_kernel =
    "\<lambda>tau.
      slp_mixed_center_finite_weighted_oscillatory_kernel
        TYPE('i) TYPE('j) tau root_weight cutoff left_potential (\<lambda>_. 1) cutoff right_potential ?right_terminal
        (?actual_error tau)"
  have source_integrable: "integrable lborel ?source"
    by (rule slp_test_cauchy_product_integrable[OF
          p_lower p_upper left_potential_lp phi_test])
  have source_l2: "aim_complex_lp_on_plane 2 ?source"
    by (rule slp_test_cauchy_product_l2[OF
          p_lower p_upper left_potential_lp phi_test])
  have aux_error_l2:
      "aim_complex_lp_on_plane 2 (?aux_error tau)" for tau
  proof (cases "0 < tau")
    case True
    have actual_l2:
        "aim_complex_lp_on_plane 2 (?actual_error tau)"
      by (rule hf.slp_center_average_error_l2_l1_l2[OF
            True source_integrable source_l2])
    show ?thesis
      using True actual_l2 by simp
  next
    case False
    show ?thesis
      using False unfolding aim_complex_lp_on_plane_def by simp
  qed
  have actual_error_square_decay:
      "((\<lambda>tau. \<integral>\<^sup>+x.
          ennreal (norm (?actual_error tau x)) ^ 2 \<partial>lborel)
        \<longlongrightarrow> 0) at_top"
    by (rule
      hf.slp_center_average_error_square_nn_integral_tendsto_zero[OF
        source_integrable source_l2])
  have eventually_aux_mass_eq:
      "eventually (\<lambda>tau.
        (\<integral>\<^sup>+x. ennreal (norm (?aux_error tau x)) ^ 2
          \<partial>lborel) =
        (\<integral>\<^sup>+x. ennreal (norm (?actual_error tau x)) ^ 2
          \<partial>lborel)) at_top"
  proof -
    have positive: "eventually (\<lambda>tau :: real. 0 < tau) at_top"
      by simp
    show ?thesis
      using positive by eventually_elim simp
  qed
  have aux_error_square_decay:
      "((\<lambda>tau. \<integral>\<^sup>+x.
          ennreal (norm (?aux_error tau x)) ^ 2 \<partial>lborel)
        \<longlongrightarrow> 0) at_top"
    by (rule tendsto_cong[OF eventually_aux_mass_eq, THEN iffD2])
      (rule actual_error_square_decay)
  have radius_nonnegative: "0 \<le> 2 * B"
    using B_nonnegative by simp
  have major_density_l2:
      "slp_positive_ennreal_lp_on_plane 2 ?major_density"
    by (rule slp_mixed_center_density_all_orders_membership_clauses(5)[OF
          radius_nonnegative p_lower p_upper X_measurable X_bounded
          cutoff_measurable left_potential_lp right_potential_lp
          root_weight_lp root_weight_outside cutoff_bound C_nonnegative])
  have majorant_decay:
      "((\<lambda>tau. \<integral>\<^sup>+center. ?majorant tau center \<partial>lborel)
        \<longlongrightarrow> 0) at_top"
  proof -
    have pairing_decay:
        "((\<lambda>tau. \<integral>\<^sup>+center.
            ?major_density center *
              ennreal (norm (?aux_error tau center)) \<partial>lborel)
          \<longlongrightarrow> 0) at_top"
      by (rule slp_positive_ennreal_complex_l2_pairing_tendsto_zero[OF
            major_density_l2 aux_error_l2 aux_error_square_decay])
    show ?thesis
      using pairing_decay by (simp only: mult.commute)
  qed
  have root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    using root_weight_lp unfolding aim_complex_lp_on_plane_def by blast
  have left_potential_measurable:
      "left_potential \<in> borel_measurable lborel"
    using left_potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have right_potential_measurable:
      "right_potential \<in> borel_measurable lborel"
    using right_potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have unit_measurable:
      "(\<lambda>_ :: slp_point. (1 :: complex)) \<in> borel_measurable lborel"
    by measurable
  have right_terminal_measurable:
      "?right_terminal \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF
          p_lower p_upper right_potential_lp])
  have aux_error_measurable:
      "?aux_error tau \<in> borel_measurable lborel" for tau
    using aux_error_l2[of tau]
    unfolding aim_complex_lp_on_plane_def by blast
  have support_radius:
      "\<And>x y :: slp_point.
        \<lbrakk>cutoff x \<noteq> 0; right_potential y \<noteq> 0\<rbrakk> \<Longrightarrow>
          norm (x - y) \<le> 2 * B"
    by (rule slp_norm_sub_le_two_radius[OF B_nonnegative
          cutoff_support right_potential_support])
  have right_terminal_le:
      "\<And>x. ennreal (cmod (cutoff x)) *
          ennreal (cmod (?right_terminal x)) \<le>
        ennreal (cmod (cutoff x)) *
          slp_positive_terminal_riesz_weight (2 * B) right_potential x"
    by (rule slp_cauchy_transform_cutoff_terminal_riesz_bound[OF
          support_radius])
  have density_le: "?density center \<le> ?major_density center" for center
    by (rule slp_mixed_center_density_cutoff_terminal_mono)
      (use right_terminal_le in simp_all)
  have mass_finite:
      "nn_integral lborel
        (slp_mixed_center_finite_weighted_absolute_fiber_mass
          TYPE('i) TYPE('j) root_weight cutoff left_potential (\<lambda>_. 1) cutoff right_potential ?right_terminal (?aux_error tau)) <
        top_class.top" for tau
    by (rule
      slp_mixed_center_finite_weighted_absolute_mass_unit_right_cauchy_finite[OF
        B_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable left_potential_lp right_potential_lp root_weight_lp
        root_weight_outside cutoff_bound root_support cutoff_support
        left_potential_support right_potential_support aux_error_l2])
  have amplitude_integrable:
      "AE center in lborel.
        integrable lborel
          (slp_mixed_center_finite_weighted_complex_amplitude root_weight
            cutoff left_potential (\<lambda>_. 1) cutoff right_potential ?right_terminal (?aux_error tau) center ::
            ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    for tau
    by (rule
      slp_mixed_center_finite_weighted_amplitude_fiber_integrable_from_mass[OF
        root_weight_measurable cutoff_measurable left_potential_measurable
        unit_measurable cutoff_measurable right_potential_measurable
        right_terminal_measurable aux_error_measurable mass_finite])
  have kernel_measurable:
      "?kernel tau \<in> borel_measurable lborel" for tau
    by (rule
      slp_mixed_center_finite_weighted_oscillatory_kernel_properties(1)[OF
        root_weight_measurable cutoff_measurable left_potential_measurable
        unit_measurable cutoff_measurable right_potential_measurable
        right_terminal_measurable aux_error_measurable amplitude_integrable])
  have kernel_absolute_bound:
      "AE center in lborel.
        ennreal (norm (?kernel tau center)) \<le>
        slp_mixed_center_finite_weighted_absolute_fiber_mass
          TYPE('i) TYPE('j) root_weight cutoff left_potential (\<lambda>_. 1) cutoff right_potential ?right_terminal (?aux_error tau) center"
    for tau
    by (rule
      slp_mixed_center_finite_weighted_oscillatory_kernel_properties(2)[OF
        root_weight_measurable cutoff_measurable left_potential_measurable
        unit_measurable cutoff_measurable right_potential_measurable
        right_terminal_measurable aux_error_measurable amplitude_integrable])
  have fiber_mass_bound:
      "slp_mixed_center_finite_weighted_absolute_fiber_mass
          TYPE('i) TYPE('j) root_weight cutoff left_potential (\<lambda>_. 1) cutoff right_potential ?right_terminal (?aux_error tau) center \<le>
        ?majorant tau center"
    for tau center
  proof -
    have raw_native:
        "slp_mixed_center_finite_weighted_absolute_fiber_mass
            TYPE('i) TYPE('j) root_weight cutoff left_potential (\<lambda>_. 1) cutoff right_potential ?right_terminal (?aux_error tau) center \<le>
          ennreal (cmod (?aux_error tau center)) *
            slp_mixed_center_density (2 * B) cutoff left_potential
              right_potential
              (\<lambda>x. ennreal (cmod ((\<lambda>_. 1) x)))
              (\<lambda>x. ennreal (cmod (?right_terminal x)))
              CARD('i) CARD('j) root_weight center"
      by (rule
        slp_mixed_center_finite_weighted_absolute_fiber_mass_density_bound[OF
          B_nonnegative root_weight_measurable cutoff_measurable
          left_potential_measurable unit_measurable
          right_potential_measurable right_terminal_measurable root_support
          cutoff_support left_potential_support right_potential_support])
    have raw:
        "slp_mixed_center_finite_weighted_absolute_fiber_mass
            TYPE('i) TYPE('j) root_weight cutoff left_potential (\<lambda>_. 1) cutoff right_potential ?right_terminal (?aux_error tau) center \<le>
          ennreal (norm (?aux_error tau center)) * ?density center"
      using raw_native by simp
    have density_step:
        "ennreal (norm (?aux_error tau center)) * ?density center \<le>
          ennreal (norm (?aux_error tau center)) * ?major_density center"
      by (rule mult_left_mono[OF density_le]) simp
    show ?thesis
      by (rule order_trans[OF raw density_step])
  qed
  have kernel_bound:
      "AE center in lborel.
        ennreal (norm (?kernel tau center)) \<le> ?majorant tau center"
    for tau
    using kernel_absolute_bound[of tau]
  proof eventually_elim
    fix center
    assume absolute_bound:
        "ennreal (norm (?kernel tau center)) \<le>
          slp_mixed_center_finite_weighted_absolute_fiber_mass
            TYPE('i) TYPE('j) root_weight cutoff left_potential (\<lambda>_. 1) cutoff right_potential ?right_terminal (?aux_error tau) center"
    show "ennreal (norm (?kernel tau center)) \<le> ?majorant tau center"
      by (rule order_trans[OF absolute_bound fiber_mass_bound])
  qed
  have aux_kernel_decay:
      "((\<lambda>tau. integral\<^sup>L lborel (?kernel tau)) \<longlongrightarrow> 0) at_top"
    by (rule
      slp_complex_kernel_integral_tendsto_zero_from_ennreal_majorant[OF
        kernel_measurable kernel_bound majorant_decay])
  have eventual_kernel_eq:
      "eventually (\<lambda>tau.
        integral\<^sup>L lborel (?actual_kernel tau) =
          integral\<^sup>L lborel (?kernel tau)) at_top"
  proof -
    have positive: "eventually (\<lambda>tau :: real. 0 < tau) at_top"
      by simp
    show ?thesis
      using positive by eventually_elim simp
  qed
  from aux_kernel_decay show ?thesis
    by (rule tendsto_cong[OF eventual_kernel_eq, THEN iffD2])
qed

end

end

