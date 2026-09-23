theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Joint_Fubini
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Transpose_Pointwise"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Fiber_Integral_Integrable"
begin

section \<open>Joint integrability and Fubini for the finite mixed center fiber\<close>

context aim_planar_riesz_hls
begin

theorem slp_mixed_center_finite_center_kernel_joint_integrable:
  fixes tau B C p :: real
    and target :: slp_point
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
    "integrable
      ((lborel :: slp_point measure) \<Otimes>\<^sub>M
        (lborel :: ('i::finite, 'j::finite)
          slp_mixed_center_finite_coordinates measure))
      (case_prod (\<lambda>center coordinates.
        slp_center_kernel tau target center *
          slp_mixed_center_finite_oscillatory_integrand tau root_weight cutoff
            left_potential cutoff right_potential center coordinates))"
proof -
  let ?J =
    "case_prod (\<lambda>center (coordinates ::
        ('i, 'j) slp_mixed_center_finite_coordinates).
      slp_center_kernel tau target center *
        slp_mixed_center_finite_oscillatory_integrand tau root_weight cutoff
          left_potential cutoff right_potential center coordinates)"
  have left_potential_measurable[measurable]:
      "left_potential \<in> borel_measurable lborel"
    using left_potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have right_potential_measurable[measurable]:
      "right_potential \<in> borel_measurable lborel"
    using right_potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have root_weight_measurable[measurable]:
      "root_weight \<in> borel_measurable lborel"
    using root_weight_integrable unfolding integrable_iff_bounded by blast
  have oscillatory_measurable:
      "case_prod (slp_mixed_center_finite_oscillatory_integrand tau
          root_weight cutoff left_potential cutoff right_potential ::
        slp_point \<Rightarrow>
          ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_mixed_center_finite_oscillatory_integrand_measurable)
      measurable
  have center_kernel_measurable:
      "(\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_center_kernel tau target (fst z)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using slp_center_kernel_measurable[of tau target]
    by measurable
  have J_measurable:
      "?J \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using center_kernel_measurable oscillatory_measurable by measurable
  have J_norm_measurable:
      "(\<lambda>z. ennreal (norm (?J z))) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using J_measurable by measurable
  have norm_mass:
      "nn_integral (lborel \<Otimes>\<^sub>M lborel)
          (\<lambda>z. ennreal (norm (?J z))) =
        nn_integral lborel (\<lambda>center.
          slp_mixed_center_finite_absolute_fiber_mass TYPE('i) TYPE('j)
            root_weight cutoff left_potential cutoff right_potential center)"
  proof -
    note raw = lborel.nn_integral_fst[OF J_norm_measurable]
    show ?thesis
      using raw[symmetric]
      unfolding slp_mixed_center_finite_absolute_fiber_mass_def
        slp_parameterized_complex_absolute_fiber_mass_def
      by (simp only: norm_mult slp_center_kernel_norm mult_1
          slp_mixed_center_finite_oscillatory_integrand_norm split_beta'
          fst_conv snd_conv)
  qed
  have absolute_le_positive:
      "slp_mixed_center_finite_absolute_fiber_mass TYPE('i) TYPE('j)
          root_weight cutoff left_potential cutoff right_potential center \<le>
        slp_mixed_center_finite_positive_fiber_mass TYPE('i) TYPE('j)
          (2 * B) root_weight cutoff left_potential cutoff right_potential
          center"
    for center
    by (rule slp_mixed_center_finite_absolute_fiber_mass_le_positive[OF
          B_nonnegative root_support cutoff_support left_potential_support
          cutoff_support right_potential_support])
  have positive_mass_finite:
      "nn_integral lborel (\<lambda>center.
          slp_mixed_center_finite_positive_fiber_mass TYPE('i) TYPE('j)
            (2 * B) root_weight cutoff left_potential cutoff right_potential
            center) < \<infinity>"
  proof -
    have radius_nonnegative: "0 \<le> 2 * B"
      using B_nonnegative by simp
    note finite = slp_mixed_center_finite_positive_mass_finite[OF
      radius_nonnegative p_lower p_upper cutoff_measurable left_potential_lp
      right_potential_lp cutoff_bound C_nonnegative root_weight_integrable,
      where 'i='i and 'j='j]
    show ?thesis
      using finite by simp
  qed
  have absolute_mass_finite:
      "nn_integral lborel (\<lambda>center.
          slp_mixed_center_finite_absolute_fiber_mass TYPE('i) TYPE('j)
            root_weight cutoff left_potential cutoff right_potential center) <
        \<infinity>"
    by (rule le_less_trans[OF nn_integral_mono[OF absolute_le_positive]
          positive_mass_finite])
  show ?thesis
    unfolding integrable_iff_bounded
    using J_measurable norm_mass absolute_mass_finite by simp
qed

theorem slp_mixed_center_finite_center_kernel_fubini:
  fixes tau B C p :: real
    and target :: slp_point
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
    "(\<integral>center. slp_center_kernel tau target center *
        slp_mixed_center_finite_fiber_integral TYPE('i::finite)
          TYPE('j::finite) tau root_weight cutoff left_potential cutoff
          right_potential center \<partial>lborel) =
      (\<integral>(coordinates ::
          ('i, 'j) slp_mixed_center_finite_coordinates). \<integral>center.
        slp_center_kernel tau target center *
          slp_mixed_center_finite_oscillatory_integrand tau root_weight cutoff
            left_potential cutoff right_potential center coordinates
        \<partial>lborel \<partial>lborel)"
proof -
  have joint_integrable:
      "integrable
        ((lborel :: slp_point measure) \<Otimes>\<^sub>M
          (lborel :: ('i, 'j) slp_mixed_center_finite_coordinates measure))
        (case_prod (\<lambda>center coordinates.
          slp_center_kernel tau target center *
            slp_mixed_center_finite_oscillatory_integrand tau root_weight
              cutoff left_potential cutoff right_potential center
              coordinates))"
    by (rule
      slp_mixed_center_finite_center_kernel_joint_integrable[OF
        B_nonnegative p_lower p_upper cutoff_measurable left_potential_lp
        right_potential_lp cutoff_bound C_nonnegative root_weight_integrable
        root_support cutoff_support left_potential_support
        right_potential_support])
  define J ::
      "slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates
        \<Rightarrow> complex"
    where
      "J = case_prod (\<lambda>center coordinates.
        slp_center_kernel tau target center *
          slp_mixed_center_finite_oscillatory_integrand tau root_weight cutoff
            left_potential cutoff right_potential center coordinates)"
  have J_integrable:
      "integrable
        ((lborel :: slp_point measure) \<Otimes>\<^sub>M
          (lborel :: ('i, 'j) slp_mixed_center_finite_coordinates measure)) J"
    using joint_integrable unfolding J_def .
  have interchange:
      "(\<integral>center. \<integral>coordinates.
          J (center, coordinates)
          \<partial>lborel \<partial>lborel) =
        (\<integral>coordinates. \<integral>center.
          J (center, coordinates)
          \<partial>lborel \<partial>lborel)"
  proof (rule sym)
    show
      "(\<integral>coordinates. \<integral>center.
          J (center, coordinates)
          \<partial>lborel \<partial>lborel) =
        (\<integral>center. \<integral>coordinates.
          J (center, coordinates)
          \<partial>lborel \<partial>lborel)"
      apply (rule lborel_pair.Fubini_integral)
      using J_integrable by simp
  qed
  have fiber_identity:
      "slp_center_kernel tau target center *
          slp_mixed_center_finite_fiber_integral TYPE('i) TYPE('j) tau
            root_weight cutoff left_potential cutoff right_potential center =
        (\<integral>coordinates.
          J (center, coordinates)
          \<partial>lborel)"
    for center
    unfolding slp_mixed_center_finite_fiber_integral_def
      slp_parameterized_real_phase_fiber_integral_def
      slp_parameterized_complex_fiber_integral_def
      slp_mixed_center_finite_oscillatory_integrand_def
    by (simp only: J_def
        slp_mixed_center_finite_oscillatory_integrand_def
        Bochner_Integration.integral_mult_right_zero split_beta'
        fst_conv snd_conv)
  have center_as_iterated:
      "(\<integral>center. slp_center_kernel tau target center *
          slp_mixed_center_finite_fiber_integral TYPE('i) TYPE('j) tau
            root_weight cutoff left_potential cutoff right_potential center
          \<partial>lborel) =
        (\<integral>center. \<integral>coordinates.
          J (center, coordinates)
          \<partial>lborel \<partial>lborel)"
    by (rule Bochner_Integration.integral_cong[OF refl])
      (rule fiber_identity)
  have J_pointwise:
      "J (center, coordinates) =
        slp_center_kernel tau target center *
          slp_mixed_center_finite_oscillatory_integrand tau root_weight cutoff
            left_potential cutoff right_potential center coordinates"
    for center coordinates
    by (simp only: J_def split_beta' fst_conv snd_conv)
  have inner_rewrite:
      "(\<integral>center. J (center, coordinates) \<partial>lborel) =
        (\<integral>center.
          slp_center_kernel tau target center *
            slp_mixed_center_finite_oscillatory_integrand tau root_weight
              cutoff left_potential cutoff right_potential center coordinates
          \<partial>lborel)"
    for coordinates
    by (rule Bochner_Integration.integral_cong[OF refl])
      (rule J_pointwise)
  have outer_functions:
      "(\<lambda>(coordinates ::
          ('i, 'j) slp_mixed_center_finite_coordinates).
          \<integral>center. J (center, coordinates) \<partial>lborel) =
        (\<lambda>(coordinates ::
          ('i, 'j) slp_mixed_center_finite_coordinates).
          \<integral>center.
            slp_center_kernel tau target center *
              slp_mixed_center_finite_oscillatory_integrand tau root_weight
                cutoff left_potential cutoff right_potential center coordinates
            \<partial>lborel)"
    by (rule ext) (rule inner_rewrite)
  have coordinate_rewrite:
      "(\<integral>(coordinates ::
          ('i, 'j) slp_mixed_center_finite_coordinates). \<integral>center.
          J (center, coordinates) \<partial>lborel \<partial>lborel) =
        (\<integral>(coordinates ::
          ('i, 'j) slp_mixed_center_finite_coordinates). \<integral>center.
          slp_center_kernel tau target center *
            slp_mixed_center_finite_oscillatory_integrand tau root_weight
              cutoff left_potential cutoff right_potential center coordinates
          \<partial>lborel \<partial>lborel)"
    by (simp only: outer_functions)
  have assembled:
      "(\<integral>center. slp_center_kernel tau target center *
          slp_mixed_center_finite_fiber_integral TYPE('i) TYPE('j) tau
            root_weight cutoff left_potential cutoff right_potential center
          \<partial>lborel) =
        (\<integral>coordinates. \<integral>center.
          J (center, coordinates) \<partial>lborel \<partial>lborel)"
    by (rule trans[OF center_as_iterated interchange])
  show ?thesis
    by (rule trans[OF assembled coordinate_rewrite])
qed

end

end
