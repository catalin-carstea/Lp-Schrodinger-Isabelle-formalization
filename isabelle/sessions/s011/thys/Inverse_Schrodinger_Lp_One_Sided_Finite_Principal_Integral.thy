theory Inverse_Schrodinger_Lp_One_Sided_Finite_Principal_Integral
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_Principal_Decay"
begin

section \<open>The single-integral positive-order principal bracket\<close>

lemma slp_unit_modulus_real_phase_integrable:
  assumes F_integrable: "integrable M F"
    and phase_measurable: "phase \<in> borel_measurable M"
  shows
    "integrable M
      (\<lambda>x. exp (\<i> * of_real (phase x)) * (F x :: complex))"
proof (rule Bochner_Integration.integrable_bound[OF F_integrable])
  have F_measurable: "F \<in> borel_measurable M"
    using F_integrable by measurable
  show
    "(\<lambda>x. exp (\<i> * of_real (phase x)) * F x)
      \<in> borel_measurable M"
    using phase_measurable F_measurable by measurable
  show
    "AE x in M.
      norm (exp (\<i> * of_real (phase x)) * F x) \<le> norm (F x)"
    by (simp only: norm_mult norm_exp_i_times mult_1_left order_refl
        eventually_True)
qed

lemma slp_left_branch_finite_list_residual_measurable:
  "(\<lambda>(coordinates :: 'i::finite slp_left_branch_finite_coordinates).
      slp_left_branch_residual
        (slp_finite_branch_pair_list
          (\<lambda>i. fst (fst (snd coordinates)) $ i)
          (\<lambda>i. snd (fst (snd coordinates)) $ i))
        (snd (snd coordinates))) \<in> borel_measurable lborel"
proof -
  have branch_coordinates_lborel:
      "(\<lambda>coordinates :: 'i slp_left_branch_finite_coordinates.
        snd (slp_one_sided_finite_to_packed_coordinates coordinates))
        \<in> measurable lborel lborel"
    using measurable_compose[
      OF slp_one_sided_finite_to_packed_coordinates_measurable measurable_snd]
    by (simp only: comp_def)
  have finite_residual_measurable:
      "(slp_one_sided_finite_residual ::
        'i slp_left_branch_finite_coordinates \<Rightarrow> real)
        \<in> borel_measurable lborel"
    unfolding slp_one_sided_finite_residual_def
    using measurable_compose[
      OF branch_coordinates_lborel slp_one_sided_packed_residual_measurable]
    by (simp only: comp_def)
  have list_function:
      "(\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
        slp_left_branch_residual
          (slp_finite_branch_pair_list
            (\<lambda>i. fst (fst (snd coordinates)) $ i)
            (\<lambda>i. snd (fst (snd coordinates)) $ i))
          (snd (snd coordinates))) =
        slp_one_sided_finite_residual"
    by (rule ext)
      (rule slp_one_sided_finite_residual_eq_left_branch[symmetric])
  show ?thesis
    using finite_residual_measurable by (simp only: list_function)
qed

definition slp_left_branch_principal_finite_bracket ::
    "(slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      'i::finite slp_left_branch_finite_coordinates \<Rightarrow> complex"
where
  "slp_left_branch_principal_finite_bracket root_weight cutoff potential
      terminal_value test coordinates =
    slp_left_branch_complex_amplitude_finite root_weight cutoff potential
      terminal_value test coordinates -
    slp_left_branch_complex_amplitude_finite root_weight cutoff potential
      (\<lambda>_. 1) (\<lambda>u. test u * terminal_value u) coordinates"

definition slp_left_branch_principal_finite_integral ::
    "'i::finite itself \<Rightarrow> real \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow> complex"
where
  "slp_left_branch_principal_finite_integral dimension_type omega
      root_weight cutoff potential terminal_value test =
    integral\<^sup>L lborel
      (\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
        exp (\<i> * of_real
          (omega * slp_left_branch_residual
            (slp_finite_branch_pair_list
              (\<lambda>i. fst (fst (snd coordinates)) $ i)
              (\<lambda>i. snd (fst (snd coordinates)) $ i))
            (snd (snd coordinates)))) *
        slp_left_branch_principal_finite_bracket root_weight cutoff potential
          terminal_value test coordinates)"

theorem slp_left_branch_principal_finite_integral_eq_functional:
  fixes branch_dummy :: "'i::finite itself"
  assumes B_nonnegative: "0 \<le> B"
    and root_support: "\<And>x. root_weight x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and potential_support: "\<And>x. potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and root_weight_measurable[measurable]:
      "root_weight \<in> borel_measurable lborel"
    and cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_value_measurable[measurable]:
      "terminal_value \<in> borel_measurable lborel"
    and test_measurable[measurable]:
      "test \<in> borel_measurable lborel"
    and terminal_majorant_finite:
      "(\<integral>\<^sup>+ coordinates.
        case_prod (slp_left_branch_positive_amplitude_packed (2 * B)
          root_weight cutoff potential terminal_value test)
          coordinates \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
            (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) <
        \<infinity>"
    and output_majorant_finite:
      "(\<integral>\<^sup>+ coordinates.
        case_prod (slp_left_branch_positive_amplitude_packed (2 * B)
          root_weight cutoff potential (\<lambda>_. 1)
          (\<lambda>u. test u * terminal_value u))
          coordinates \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
            (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) <
        \<infinity>"
  shows
    "slp_left_branch_principal_finite_integral TYPE('i) omega root_weight
        cutoff potential terminal_value test =
      slp_left_branch_principal_finite_functional TYPE('i) omega root_weight
        cutoff potential terminal_value test"
proof -
  let ?terminal_amplitude =
    "(slp_left_branch_complex_amplitude_finite root_weight cutoff potential
      terminal_value test ::
        'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
  let ?output_amplitude =
    "(slp_left_branch_complex_amplitude_finite root_weight cutoff potential
      (\<lambda>_. 1) (\<lambda>u. test u * terminal_value u) ::
        'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
  let ?residual =
    "(\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
      slp_left_branch_residual
        (slp_finite_branch_pair_list
          (\<lambda>i. fst (fst (snd coordinates)) $ i)
          (\<lambda>i. snd (fst (snd coordinates)) $ i))
        (snd (snd coordinates)))"
  have terminal_integrable: "integrable lborel ?terminal_amplitude"
    by (rule slp_left_branch_complex_amplitude_finite_integrable[
          where B = B, OF B_nonnegative root_support cutoff_support
            potential_support root_weight_measurable cutoff_measurable
            potential_measurable terminal_value_measurable test_measurable
            terminal_majorant_finite])
  have output_integrable: "integrable lborel ?output_amplitude"
    by (rule slp_left_branch_complex_amplitude_finite_integrable[
          where B = B, OF B_nonnegative root_support cutoff_support
            potential_support root_weight_measurable cutoff_measurable
            potential_measurable _ _ output_majorant_finite])
      measurable
  have residual_measurable: "?residual \<in> borel_measurable lborel"
    by (rule slp_left_branch_finite_list_residual_measurable)
  have scaled_residual_measurable:
      "(\<lambda>x. omega * ?residual x) \<in> borel_measurable lborel"
    using residual_measurable by measurable
  have terminal_oscillatory_integrable:
      "integrable lborel
        (\<lambda>x. exp (\<i> * of_real (omega * ?residual x)) *
          ?terminal_amplitude x)"
    by (rule slp_unit_modulus_real_phase_integrable[
          OF terminal_integrable scaled_residual_measurable])
  have output_oscillatory_integrable:
      "integrable lborel
        (\<lambda>x. exp (\<i> * of_real (omega * ?residual x)) *
          ?output_amplitude x)"
    by (rule slp_unit_modulus_real_phase_integrable[
          OF output_integrable scaled_residual_measurable])
  have integral_difference:
      "integral\<^sup>L lborel
          (\<lambda>x. exp (\<i> * of_real (omega * ?residual x)) *
              ?terminal_amplitude x -
            exp (\<i> * of_real (omega * ?residual x)) *
              ?output_amplitude x) =
        integral\<^sup>L lborel
            (\<lambda>x. exp (\<i> * of_real (omega * ?residual x)) *
              ?terminal_amplitude x) -
          integral\<^sup>L lborel
            (\<lambda>x. exp (\<i> * of_real (omega * ?residual x)) *
              ?output_amplitude x)"
    by (rule Bochner_Integration.integral_diff[
          OF terminal_oscillatory_integrable output_oscillatory_integrable])
  have bracket_integrand:
      "(\<lambda>x. exp (\<i> * of_real (omega * ?residual x)) *
          slp_left_branch_principal_finite_bracket root_weight cutoff potential
            terminal_value test x) =
        (\<lambda>x. exp (\<i> * of_real (omega * ?residual x)) *
            ?terminal_amplitude x -
          exp (\<i> * of_real (omega * ?residual x)) *
            ?output_amplitude x)"
    unfolding slp_left_branch_principal_finite_bracket_def
    by (rule ext) (simp only: right_diff_distrib)
  show ?thesis
    unfolding slp_left_branch_principal_finite_integral_def
      slp_left_branch_principal_finite_functional_def
    by (subst bracket_integrand, rule integral_difference)
qed

theorem slp_left_branch_principal_finite_integral_decay:
  fixes branch_dummy :: "'i::finite itself"
  assumes stationary_phase:
      "hormander_quadratic_stationary_phase_decay_claim
        TYPE(('i + 'i) \<times> bool)"
    and density:
      "evans_compact_smooth_l1_density_claim TYPE(('i + 'i) \<times> bool)"
    and B_nonnegative: "0 \<le> B"
    and root_support: "\<And>x. root_weight x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and potential_support: "\<And>x. potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and root_weight_measurable[measurable]:
      "root_weight \<in> borel_measurable lborel"
    and cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_value_measurable[measurable]:
      "terminal_value \<in> borel_measurable lborel"
    and test_measurable[measurable]:
      "test \<in> borel_measurable lborel"
    and terminal_majorant_finite:
      "(\<integral>\<^sup>+ coordinates.
        case_prod (slp_left_branch_positive_amplitude_packed (2 * B)
          root_weight cutoff potential terminal_value test)
          coordinates \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
            (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) <
        \<infinity>"
    and output_majorant_finite:
      "(\<integral>\<^sup>+ coordinates.
        case_prod (slp_left_branch_positive_amplitude_packed (2 * B)
          root_weight cutoff potential (\<lambda>_. 1)
          (\<lambda>u. test u * terminal_value u))
          coordinates \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
            (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) <
        \<infinity>"
  shows
    "((\<lambda>omega. slp_left_branch_principal_finite_integral TYPE('i)
        omega root_weight cutoff potential terminal_value test)
      \<longlongrightarrow> 0) at_top"
proof -
  have split_decay:
      "((\<lambda>omega. slp_left_branch_principal_finite_functional TYPE('i)
          omega root_weight cutoff potential terminal_value test)
        \<longlongrightarrow> 0) at_top"
    by (rule slp_left_branch_principal_finite_functional_decay[
          where B = B, OF stationary_phase density B_nonnegative root_support
            cutoff_support potential_support root_weight_measurable
            cutoff_measurable potential_measurable terminal_value_measurable
            test_measurable terminal_majorant_finite output_majorant_finite])
  have eventual_identity:
      "eventually
        (\<lambda>omega.
          slp_left_branch_principal_finite_integral TYPE('i) omega root_weight
              cutoff potential terminal_value test =
            slp_left_branch_principal_finite_functional TYPE('i) omega
              root_weight cutoff potential terminal_value test) at_top"
    by (rule always_eventually, rule allI,
        rule slp_left_branch_principal_finite_integral_eq_functional[
          where B = B, OF B_nonnegative root_support cutoff_support
            potential_support root_weight_measurable cutoff_measurable
            potential_measurable terminal_value_measurable test_measurable
            terminal_majorant_finite output_majorant_finite])
  have target_iff:
      "((\<lambda>omega. slp_left_branch_principal_finite_integral TYPE('i)
          omega root_weight cutoff potential terminal_value test)
          \<longlongrightarrow> 0) at_top \<longleftrightarrow>
        ((\<lambda>omega. slp_left_branch_principal_finite_functional TYPE('i)
          omega root_weight cutoff potential terminal_value test)
          \<longlongrightarrow> 0) at_top"
    by (rule tendsto_cong[OF eventual_identity])
  show ?thesis
    using split_decay by (subst target_iff)
qed

end
