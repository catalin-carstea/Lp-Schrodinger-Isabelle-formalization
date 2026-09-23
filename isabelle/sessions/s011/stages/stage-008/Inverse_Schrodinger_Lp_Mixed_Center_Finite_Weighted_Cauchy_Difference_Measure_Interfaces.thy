theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Cauchy_Difference_Measure_Interfaces
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Cauchy_Difference_Integral_Expansion"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Measure interfaces for the center-dependent primitive differences\<close>

theorem slp_mixed_center_finite_weighted_oscillatory_integrand_joint_measurable:
  assumes root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    and left_cutoff_measurable:
      "left_cutoff \<in> borel_measurable lborel"
    and left_potential_measurable:
      "left_potential \<in> borel_measurable lborel"
    and left_terminal_measurable:
      "left_terminal \<in> borel_measurable lborel"
    and right_cutoff_measurable:
      "right_cutoff \<in> borel_measurable lborel"
    and right_potential_measurable:
      "right_potential \<in> borel_measurable lborel"
    and right_terminal_measurable:
      "right_terminal \<in> borel_measurable lborel"
    and center_factor_measurable:
      "center_factor \<in> borel_measurable lborel"
  shows
    "case_prod
      (slp_mixed_center_finite_weighted_oscillatory_integrand frequency
        root_weight left_cutoff left_potential left_terminal right_cutoff
        right_potential right_terminal center_factor ::
        slp_point \<Rightarrow>
          ('i::finite, 'j::finite)
            slp_mixed_center_finite_coordinates \<Rightarrow> complex)
      \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
proof -
  have phase_measurable:
      "case_prod (slp_mixed_center_finite_residual ::
        slp_point \<Rightarrow>
          ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> real)
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_mixed_center_finite_residual_measurable)
  have amplitude_lborel_measurable:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_mixed_center_finite_weighted_complex_amplitude root_weight
          left_cutoff left_potential left_terminal right_cutoff
          right_potential right_terminal center_factor
          (fst z) (snd z))) \<in> borel_measurable lborel"
    by (rule
      slp_mixed_center_finite_weighted_complex_amplitude_measurable[OF
        root_weight_measurable left_cutoff_measurable
        left_potential_measurable left_terminal_measurable
        right_cutoff_measurable right_potential_measurable
        right_terminal_measurable center_factor_measurable])
  have amplitude_measurable:
      "case_prod
        (slp_mixed_center_finite_weighted_complex_amplitude root_weight
          left_cutoff left_potential left_terminal right_cutoff
          right_potential right_terminal center_factor ::
          slp_point \<Rightarrow>
            ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using amplitude_lborel_measurable
    by (simp only: lborel_prod split_beta')
  show ?thesis
    unfolding slp_mixed_center_finite_weighted_oscillatory_integrand_def
      slp_parameterized_real_phase_integrand_def
    using phase_measurable amplitude_measurable by measurable
qed

theorem
    slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_integrand_joint_measurable:
  assumes root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    and left_cutoff_measurable:
      "left_cutoff \<in> borel_measurable lborel"
    and left_potential_measurable:
      "left_potential \<in> borel_measurable lborel"
    and left_terminal_measurable:
      "left_terminal \<in> borel_measurable lborel"
    and right_cutoff_measurable:
      "right_cutoff \<in> borel_measurable lborel"
    and right_potential_measurable:
      "right_potential \<in> borel_measurable lborel"
    and right_terminal_measurable:
      "right_terminal \<in> borel_measurable lborel"
    and center_factor_measurable:
      "center_factor \<in> borel_measurable lborel"
  shows
    "case_prod
      (\<lambda>center coordinates.
        slp_mixed_center_finite_weighted_oscillatory_integrand frequency
          root_weight left_cutoff left_potential
          (\<lambda>x. left_terminal x - left_terminal center)
          right_cutoff right_potential
          (\<lambda>x. right_terminal x - right_terminal center)
          center_factor center coordinates :: complex)
      \<in> borel_measurable
        (lborel \<Otimes>\<^sub>M
          (lborel :: ('i::finite, 'j::finite)
            slp_mixed_center_finite_coordinates measure))"
proof -
  let ?terminal_terminal =
    "slp_mixed_center_finite_weighted_oscillatory_integrand frequency
      root_weight left_cutoff left_potential left_terminal right_cutoff
      right_potential right_terminal center_factor ::
      slp_point \<Rightarrow>
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex"
  let ?left_cross =
    "slp_mixed_center_finite_weighted_oscillatory_integrand frequency
      root_weight left_cutoff left_potential left_terminal right_cutoff
      right_potential (\<lambda>_. 1)
      (\<lambda>x. -(center_factor x * right_terminal x)) ::
      slp_point \<Rightarrow>
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex"
  let ?right_cross =
    "slp_mixed_center_finite_weighted_oscillatory_integrand frequency
      root_weight left_cutoff left_potential (\<lambda>_. 1) right_cutoff
      right_potential right_terminal
      (\<lambda>x. -(center_factor x * left_terminal x)) ::
      slp_point \<Rightarrow>
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex"
  let ?unit_unit =
    "slp_mixed_center_finite_weighted_oscillatory_integrand frequency
      root_weight left_cutoff left_potential (\<lambda>_. 1) right_cutoff
      right_potential (\<lambda>_. 1)
      (\<lambda>x. center_factor x *
        (left_terminal x * right_terminal x)) ::
      slp_point \<Rightarrow>
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex"
  have unit_measurable:
      "(\<lambda>_ :: slp_point. (1 :: complex))
        \<in> borel_measurable lborel"
    by measurable
  have left_center_measurable:
      "(\<lambda>x. -(center_factor x * right_terminal x))
        \<in> borel_measurable lborel"
    using center_factor_measurable right_terminal_measurable by measurable
  have right_center_measurable:
      "(\<lambda>x. -(center_factor x * left_terminal x))
        \<in> borel_measurable lborel"
    using center_factor_measurable left_terminal_measurable by measurable
  have unit_center_measurable:
      "(\<lambda>x. center_factor x *
        (left_terminal x * right_terminal x))
        \<in> borel_measurable lborel"
    using center_factor_measurable left_terminal_measurable
      right_terminal_measurable by measurable
  have terminal_terminal_measurable:
      "case_prod ?terminal_terminal
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule
      slp_mixed_center_finite_weighted_oscillatory_integrand_joint_measurable[OF
        root_weight_measurable left_cutoff_measurable
        left_potential_measurable left_terminal_measurable
        right_cutoff_measurable right_potential_measurable
        right_terminal_measurable center_factor_measurable])
  have left_cross_measurable:
      "case_prod ?left_cross
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule
      slp_mixed_center_finite_weighted_oscillatory_integrand_joint_measurable[OF
        root_weight_measurable left_cutoff_measurable
        left_potential_measurable left_terminal_measurable
        right_cutoff_measurable right_potential_measurable unit_measurable
        left_center_measurable])
  have right_cross_measurable:
      "case_prod ?right_cross
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule
      slp_mixed_center_finite_weighted_oscillatory_integrand_joint_measurable[OF
        root_weight_measurable left_cutoff_measurable
        left_potential_measurable unit_measurable right_cutoff_measurable
        right_potential_measurable right_terminal_measurable
        right_center_measurable])
  have unit_unit_measurable:
      "case_prod ?unit_unit
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule
      slp_mixed_center_finite_weighted_oscillatory_integrand_joint_measurable[OF
        root_weight_measurable left_cutoff_measurable
        left_potential_measurable unit_measurable right_cutoff_measurable
        right_potential_measurable unit_measurable unit_center_measurable])
  have sum_measurable:
      "case_prod (\<lambda>center coordinates.
        (?terminal_terminal center coordinates +
          ?left_cross center coordinates) +
        ?right_cross center coordinates + ?unit_unit center coordinates)
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using terminal_terminal_measurable left_cross_measurable
      right_cross_measurable unit_unit_measurable by measurable
  have integrand_expansion:
      "case_prod
          (\<lambda>center coordinates.
            slp_mixed_center_finite_weighted_oscillatory_integrand frequency
              root_weight left_cutoff left_potential
              (\<lambda>x. left_terminal x - left_terminal center)
              right_cutoff right_potential
              (\<lambda>x. right_terminal x - right_terminal center)
              center_factor center coordinates :: complex) =
        case_prod (\<lambda>center coordinates.
          (?terminal_terminal center coordinates +
            ?left_cross center coordinates) +
          ?right_cross center coordinates + ?unit_unit center coordinates)"
    by (rule ext)
      (simp only: split_beta'
        slp_mixed_center_finite_weighted_oscillatory_integrand_cauchy_center_diff_expansion)
  show ?thesis
    using sum_measurable unfolding integrand_expansion .
qed

theorem
    slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_kernel_measurable:
  fixes left_dummy :: "'i::finite itself"
    and right_dummy :: "'j::finite itself"
  assumes root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    and left_cutoff_measurable:
      "left_cutoff \<in> borel_measurable lborel"
    and left_potential_measurable:
      "left_potential \<in> borel_measurable lborel"
    and left_terminal_measurable:
      "left_terminal \<in> borel_measurable lborel"
    and right_cutoff_measurable:
      "right_cutoff \<in> borel_measurable lborel"
    and right_potential_measurable:
      "right_potential \<in> borel_measurable lborel"
    and right_terminal_measurable:
      "right_terminal \<in> borel_measurable lborel"
    and center_factor_measurable:
      "center_factor \<in> borel_measurable lborel"
  shows
    "slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_kernel
      TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
      left_terminal right_cutoff right_potential right_terminal center_factor
      \<in> borel_measurable lborel"
  unfolding
    slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_kernel_def
  apply (rule lborel.borel_measurable_lebesgue_integral)
  by (rule
    slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_integrand_joint_measurable[OF
      root_weight_measurable left_cutoff_measurable
      left_potential_measurable left_terminal_measurable
      right_cutoff_measurable right_potential_measurable
      right_terminal_measurable center_factor_measurable])

theorem slp_integrable_from_ennreal_mass_bound:
  fixes mass :: "'a::euclidean_space \<Rightarrow> ennreal"
    and f :: "'a \<Rightarrow> complex"
  assumes mass_measurable: "mass \<in> borel_measurable lborel"
    and mass_integral_finite:
      "nn_integral lborel mass < top_class.top"
    and f_measurable: "f \<in> borel_measurable lborel"
    and f_bound:
      "AE x in lborel.
        ennreal (norm_class.norm (f x)) \<le> mass x"
  shows "integrable lborel f"
proof -
  let ?majorant = "\<lambda>x. enn2real (mass x)"
  have mass_finite: "AE x in lborel. mass x < top_class.top"
  proof -
    have integral_not_infinity: "nn_integral lborel mass \<noteq> \<infinity>"
      using mass_integral_finite by simp
    have raw_ae: "AE x in lborel. mass x \<noteq> \<infinity>"
      by (rule nn_integral_PInf_AE[OF mass_measurable
            integral_not_infinity])
    show ?thesis
      using raw_ae by (simp add: less_top)
  qed
  have majorant_measurable:
      "?majorant \<in> borel_measurable lborel"
    using mass_measurable by measurable
  have majorant_nn_integral:
      "nn_integral lborel ?majorant = nn_integral lborel mass"
    by (rule nn_integral_cong_AE)
      (use mass_finite in \<open>eventually_elim, simp\<close>)
  have majorant_integrable: "integrable lborel ?majorant"
  proof (rule integrableI_nonneg)
    show "?majorant \<in> borel_measurable lborel"
      by (rule majorant_measurable)
    show "AE x in lborel. 0 \<le> ?majorant x"
      by simp
    show "nn_integral lborel ?majorant < \<infinity>"
      using majorant_nn_integral mass_integral_finite by simp
  qed
  have bound_real:
      "AE x in lborel. norm_class.norm (f x) \<le> ?majorant x"
    using f_bound mass_finite
  proof eventually_elim
    fix x
    assume bound:
        "ennreal (norm_class.norm (f x)) \<le> mass x"
      and finite: "mass x < top_class.top"
    have
      "enn2real (ennreal (norm_class.norm (f x))) \<le>
        enn2real (mass x)"
      by (rule enn2real_mono[OF bound finite])
    then show "norm_class.norm (f x) \<le> ?majorant x"
      by simp
  qed
  show ?thesis
  proof (rule Bochner_Integration.integrable_bound[OF majorant_integrable
        f_measurable])
    show "AE x in lborel.
        norm_class.norm (f x) \<le> norm_class.norm (?majorant x)"
      using bound_real by eventually_elim simp
  qed
qed

end
