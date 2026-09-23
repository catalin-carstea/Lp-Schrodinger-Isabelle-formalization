theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Cauchy_Difference_Integral_Expansion
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Cauchy_Difference_Expansion"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Exact integral expansion of the center-dependent primitive differences\<close>

definition
    slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_kernel ::
    "('i::finite) itself \<Rightarrow> ('j::finite) itself \<Rightarrow> real \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      slp_point \<Rightarrow> complex"
where
  "slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_kernel
      TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
      left_terminal right_cutoff right_potential right_terminal center_factor
      center =
    integral\<^sup>L lborel
      (slp_mixed_center_finite_weighted_oscillatory_integrand frequency
        root_weight left_cutoff left_potential
        (\<lambda>x. left_terminal x - left_terminal center)
        right_cutoff right_potential
        (\<lambda>x. right_terminal x - right_terminal center)
        center_factor center ::
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"

theorem
    slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_kernel_expansion:
  fixes center :: slp_point
  assumes terminal_terminal_integrable:
      "integrable lborel
        (slp_mixed_center_finite_weighted_oscillatory_integrand frequency
          root_weight left_cutoff left_potential left_terminal right_cutoff
          right_potential right_terminal center_factor center ::
          ('i::finite, 'j::finite)
            slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    and left_cross_integrable:
      "integrable lborel
        (slp_mixed_center_finite_weighted_oscillatory_integrand frequency
          root_weight left_cutoff left_potential left_terminal right_cutoff
          right_potential (\<lambda>_. 1)
          (\<lambda>x. -(center_factor x * right_terminal x)) center ::
          ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    and right_cross_integrable:
      "integrable lborel
        (slp_mixed_center_finite_weighted_oscillatory_integrand frequency
          root_weight left_cutoff left_potential (\<lambda>_. 1) right_cutoff
          right_potential right_terminal
          (\<lambda>x. -(center_factor x * left_terminal x)) center ::
          ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    and unit_unit_integrable:
      "integrable lborel
        (slp_mixed_center_finite_weighted_oscillatory_integrand frequency
          root_weight left_cutoff left_potential (\<lambda>_. 1) right_cutoff
          right_potential (\<lambda>_. 1)
          (\<lambda>x. center_factor x *
            (left_terminal x * right_terminal x)) center ::
          ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
  shows
    "slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_kernel
        TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
        left_terminal right_cutoff right_potential right_terminal center_factor
        center =
      slp_mixed_center_finite_weighted_oscillatory_kernel
          TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
          left_terminal right_cutoff right_potential right_terminal
          center_factor center +
      slp_mixed_center_finite_weighted_oscillatory_kernel
          TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
          left_terminal right_cutoff right_potential (\<lambda>_. 1)
          (\<lambda>x. -(center_factor x * right_terminal x)) center +
      slp_mixed_center_finite_weighted_oscillatory_kernel
          TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
          (\<lambda>_. 1) right_cutoff right_potential right_terminal
          (\<lambda>x. -(center_factor x * left_terminal x)) center +
      slp_mixed_center_finite_weighted_oscillatory_kernel
          TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
          (\<lambda>_. 1) right_cutoff right_potential (\<lambda>_. 1)
          (\<lambda>x. center_factor x *
            (left_terminal x * right_terminal x)) center"
proof -
  let ?terminal_terminal =
    "slp_mixed_center_finite_weighted_oscillatory_integrand frequency
      root_weight left_cutoff left_potential left_terminal right_cutoff
      right_potential right_terminal center_factor center ::
      ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex"
  let ?left_cross =
    "slp_mixed_center_finite_weighted_oscillatory_integrand frequency
      root_weight left_cutoff left_potential left_terminal right_cutoff
      right_potential (\<lambda>_. 1)
      (\<lambda>x. -(center_factor x * right_terminal x)) center ::
      ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex"
  let ?right_cross =
    "slp_mixed_center_finite_weighted_oscillatory_integrand frequency
      root_weight left_cutoff left_potential (\<lambda>_. 1) right_cutoff
      right_potential right_terminal
      (\<lambda>x. -(center_factor x * left_terminal x)) center ::
      ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex"
  let ?unit_unit =
    "slp_mixed_center_finite_weighted_oscillatory_integrand frequency
      root_weight left_cutoff left_potential (\<lambda>_. 1) right_cutoff
      right_potential (\<lambda>_. 1)
      (\<lambda>x. center_factor x *
        (left_terminal x * right_terminal x)) center ::
      ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex"
  have first_sum_integrable:
      "integrable lborel (\<lambda>coordinates.
        ?terminal_terminal coordinates + ?left_cross coordinates)"
    by (rule Bochner_Integration.integrable_add[OF
          terminal_terminal_integrable left_cross_integrable])
  have second_sum_integrable:
      "integrable lborel (\<lambda>coordinates.
        (?terminal_terminal coordinates + ?left_cross coordinates) +
          ?right_cross coordinates)"
    by (rule Bochner_Integration.integrable_add[OF
          first_sum_integrable right_cross_integrable])
  have integrand_expansion:
      "(slp_mixed_center_finite_weighted_oscillatory_integrand frequency
          root_weight left_cutoff left_potential
          (\<lambda>x. left_terminal x - left_terminal center)
          right_cutoff right_potential
          (\<lambda>x. right_terminal x - right_terminal center)
          center_factor center ::
          ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex) =
        (\<lambda>coordinates.
          (?terminal_terminal coordinates + ?left_cross coordinates) +
            ?right_cross coordinates + ?unit_unit coordinates)"
    by (rule ext, rule
      slp_mixed_center_finite_weighted_oscillatory_integrand_cauchy_center_diff_expansion)
  show ?thesis
    unfolding
      slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_kernel_def
      slp_mixed_center_finite_weighted_oscillatory_kernel_def
    apply (simp only: integrand_expansion)
    apply (subst Bochner_Integration.integral_add[OF second_sum_integrable
          unit_unit_integrable])
    apply (subst Bochner_Integration.integral_add[OF first_sum_integrable
          right_cross_integrable])
    apply (subst Bochner_Integration.integral_add[OF
          terminal_terminal_integrable left_cross_integrable])
    by simp
qed

theorem
    slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_global_expansion:
  assumes fiber_integrable:
      "AE center in lborel.
        integrable lborel
          (slp_mixed_center_finite_weighted_oscillatory_integrand frequency
            root_weight left_cutoff left_potential left_terminal right_cutoff
            right_potential right_terminal center_factor center ::
            ('i::finite, 'j::finite)
              slp_mixed_center_finite_coordinates \<Rightarrow> complex) \<and>
        integrable lborel
          (slp_mixed_center_finite_weighted_oscillatory_integrand frequency
            root_weight left_cutoff left_potential left_terminal right_cutoff
            right_potential (\<lambda>_. 1)
            (\<lambda>x. -(center_factor x * right_terminal x)) center ::
            ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex) \<and>
        integrable lborel
          (slp_mixed_center_finite_weighted_oscillatory_integrand frequency
            root_weight left_cutoff left_potential (\<lambda>_. 1) right_cutoff
            right_potential right_terminal
            (\<lambda>x. -(center_factor x * left_terminal x)) center ::
            ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex) \<and>
        integrable lborel
          (slp_mixed_center_finite_weighted_oscillatory_integrand frequency
            root_weight left_cutoff left_potential (\<lambda>_. 1) right_cutoff
            right_potential (\<lambda>_. 1)
            (\<lambda>x. center_factor x *
              (left_terminal x * right_terminal x)) center ::
            ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    and terminal_center_diff_measurable:
      "(slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_kernel
        TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
        left_terminal right_cutoff right_potential right_terminal
        center_factor) \<in> borel_measurable lborel"
    and terminal_terminal_integrable:
      "integrable lborel
        (slp_mixed_center_finite_weighted_oscillatory_kernel
          TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
          left_terminal right_cutoff right_potential right_terminal
          center_factor)"
    and left_cross_integrable:
      "integrable lborel
        (slp_mixed_center_finite_weighted_oscillatory_kernel
          TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
          left_terminal right_cutoff right_potential (\<lambda>_. 1)
          (\<lambda>x. -(center_factor x * right_terminal x)))"
    and right_cross_integrable:
      "integrable lborel
        (slp_mixed_center_finite_weighted_oscillatory_kernel
          TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
          (\<lambda>_. 1) right_cutoff right_potential right_terminal
          (\<lambda>x. -(center_factor x * left_terminal x)))"
    and unit_unit_integrable:
      "integrable lborel
        (slp_mixed_center_finite_weighted_oscillatory_kernel
          TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
          (\<lambda>_. 1) right_cutoff right_potential (\<lambda>_. 1)
          (\<lambda>x. center_factor x *
            (left_terminal x * right_terminal x)))"
  shows
    "integral\<^sup>L lborel
        (slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_kernel
          TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
          left_terminal right_cutoff right_potential right_terminal
          center_factor) =
      integral\<^sup>L lborel
          (slp_mixed_center_finite_weighted_oscillatory_kernel
            TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
            left_terminal right_cutoff right_potential right_terminal
            center_factor) +
      integral\<^sup>L lborel
          (slp_mixed_center_finite_weighted_oscillatory_kernel
            TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
            left_terminal right_cutoff right_potential (\<lambda>_. 1)
            (\<lambda>x. -(center_factor x * right_terminal x))) +
      integral\<^sup>L lborel
          (slp_mixed_center_finite_weighted_oscillatory_kernel
            TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
            (\<lambda>_. 1) right_cutoff right_potential right_terminal
            (\<lambda>x. -(center_factor x * left_terminal x))) +
      integral\<^sup>L lborel
          (slp_mixed_center_finite_weighted_oscillatory_kernel
            TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
            (\<lambda>_. 1) right_cutoff right_potential (\<lambda>_. 1)
            (\<lambda>x. center_factor x *
              (left_terminal x * right_terminal x)))"
proof -
  let ?terminal_terminal =
    "slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
      left_terminal right_cutoff right_potential right_terminal center_factor"
  let ?left_cross =
    "slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
      left_terminal right_cutoff right_potential (\<lambda>_. 1)
      (\<lambda>x. -(center_factor x * right_terminal x))"
  let ?right_cross =
    "slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
      (\<lambda>_. 1) right_cutoff right_potential right_terminal
      (\<lambda>x. -(center_factor x * left_terminal x))"
  let ?unit_unit =
    "slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
      (\<lambda>_. 1) right_cutoff right_potential (\<lambda>_. 1)
      (\<lambda>x. center_factor x *
        (left_terminal x * right_terminal x))"
  have first_sum_integrable:
      "integrable lborel (\<lambda>center.
        ?terminal_terminal center + ?left_cross center)"
    by (rule Bochner_Integration.integrable_add[OF
          terminal_terminal_integrable left_cross_integrable])
  have second_sum_integrable:
      "integrable lborel (\<lambda>center.
        (?terminal_terminal center + ?left_cross center) +
          ?right_cross center)"
    by (rule Bochner_Integration.integrable_add[OF
          first_sum_integrable right_cross_integrable])
  have sum_measurable:
      "(\<lambda>center.
        (?terminal_terminal center + ?left_cross center) +
          ?right_cross center + ?unit_unit center)
        \<in> borel_measurable lborel"
    using terminal_terminal_integrable left_cross_integrable
      right_cross_integrable unit_unit_integrable
    by measurable
  have kernel_expansion:
      "AE center in lborel.
        slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_kernel
            TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
            left_terminal right_cutoff right_potential right_terminal
            center_factor center =
          (?terminal_terminal center + ?left_cross center) +
            ?right_cross center + ?unit_unit center"
    using fiber_integrable
  proof eventually_elim
    fix center
    assume integrable:
      "integrable lborel
          (slp_mixed_center_finite_weighted_oscillatory_integrand frequency
            root_weight left_cutoff left_potential left_terminal right_cutoff
            right_potential right_terminal center_factor center ::
            ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex) \<and>
        integrable lborel
          (slp_mixed_center_finite_weighted_oscillatory_integrand frequency
            root_weight left_cutoff left_potential left_terminal right_cutoff
            right_potential (\<lambda>_. 1)
            (\<lambda>x. -(center_factor x * right_terminal x)) center ::
            ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex) \<and>
        integrable lborel
          (slp_mixed_center_finite_weighted_oscillatory_integrand frequency
            root_weight left_cutoff left_potential (\<lambda>_. 1) right_cutoff
            right_potential right_terminal
            (\<lambda>x. -(center_factor x * left_terminal x)) center ::
            ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex) \<and>
        integrable lborel
          (slp_mixed_center_finite_weighted_oscillatory_integrand frequency
            root_weight left_cutoff left_potential (\<lambda>_. 1) right_cutoff
            right_potential (\<lambda>_. 1)
            (\<lambda>x. center_factor x *
              (left_terminal x * right_terminal x)) center ::
            ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    show
      "slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_kernel
          TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
          left_terminal right_cutoff right_potential right_terminal
          center_factor center =
        (?terminal_terminal center + ?left_cross center) +
          ?right_cross center + ?unit_unit center"
      by (rule
        slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_kernel_expansion)
        (use integrable in blast)+
  qed
  show ?thesis
    apply (subst integral_cong_AE[OF terminal_center_diff_measurable
          sum_measurable kernel_expansion])
    apply (subst Bochner_Integration.integral_add[OF second_sum_integrable
          unit_unit_integrable])
    apply (subst Bochner_Integration.integral_add[OF first_sum_integrable
          right_cross_integrable])
    apply (subst Bochner_Integration.integral_add[OF
          terminal_terminal_integrable left_cross_integrable])
    by simp
qed

end
