theory Inverse_Schrodinger_Lp_One_Sided_Finite_Cancellation_Algebra
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Born_Finite_Center_Cauchy_Evaluated"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_One_Sided_Finite_Cancellation_V2"
begin

section \<open>Exact finite oscillatory-pair cancellation algebra\<close>

lemma slp_left_branch_complex_amplitude_finite_output_diff:
  fixes coordinates :: "'i::finite slp_left_branch_finite_coordinates"
  shows
    "slp_left_branch_complex_amplitude_finite root_weight cutoff potential
        terminal_value (\<lambda>x. first x - second x) coordinates =
      slp_left_branch_complex_amplitude_finite root_weight cutoff potential
          terminal_value first coordinates -
        slp_left_branch_complex_amplitude_finite root_weight cutoff potential
          terminal_value second coordinates"
  unfolding slp_left_branch_complex_amplitude_finite_def
  by (simp add: algebra_simps)

theorem slp_left_branch_finite_oscillatory_integral_output_diff:
  fixes branch_dummy :: "'i::finite itself"
    and first second :: "slp_point \<Rightarrow> complex"
  assumes first_amplitude_integrable:
      "integrable lborel
        (slp_left_branch_complex_amplitude_finite root_weight cutoff potential
          terminal_value first ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    and second_amplitude_integrable:
      "integrable lborel
        (slp_left_branch_complex_amplitude_finite root_weight cutoff potential
          terminal_value second ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
  shows
    "slp_left_branch_finite_oscillatory_integral TYPE('i) tau root_weight
        cutoff potential terminal_value (\<lambda>x. first x - second x) =
      slp_left_branch_finite_oscillatory_integral TYPE('i) tau root_weight
          cutoff potential terminal_value first -
        slp_left_branch_finite_oscillatory_integral TYPE('i) tau root_weight
          cutoff potential terminal_value second"
proof -
  let ?phase =
    "\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
      tau * slp_one_sided_finite_residual coordinates"
  let ?first_amplitude =
    "slp_left_branch_complex_amplitude_finite root_weight cutoff potential
      terminal_value first ::
      'i slp_left_branch_finite_coordinates \<Rightarrow> complex"
  let ?second_amplitude =
    "slp_left_branch_complex_amplitude_finite root_weight cutoff potential
      terminal_value second ::
      'i slp_left_branch_finite_coordinates \<Rightarrow> complex"
  have residual_measurable:
      "(slp_one_sided_finite_residual ::
        'i slp_left_branch_finite_coordinates \<Rightarrow> real) \<in>
        borel_measurable lborel"
    unfolding slp_one_sided_finite_residual_def
    using measurable_compose[
      OF measurable_compose[
        OF slp_one_sided_finite_to_packed_coordinates_measurable measurable_snd]
        slp_one_sided_packed_residual_measurable]
    by (simp only: comp_def)
  have phase_measurable: "?phase \<in> borel_measurable lborel"
    using residual_measurable by measurable
  have first_integrand_integrable:
      "integrable lborel
        (\<lambda>coordinates. exp (\<i> * of_real (?phase coordinates)) *
          ?first_amplitude coordinates)"
    by (rule slp_unit_modulus_real_phase_integrable[OF
          first_amplitude_integrable phase_measurable])
  have second_integrand_integrable:
      "integrable lborel
        (\<lambda>coordinates. exp (\<i> * of_real (?phase coordinates)) *
          ?second_amplitude coordinates)"
    by (rule slp_unit_modulus_real_phase_integrable[OF
          second_amplitude_integrable phase_measurable])
  have integrand_diff:
      "(\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
          exp (\<i> * of_real (?phase coordinates)) *
            slp_left_branch_complex_amplitude_finite root_weight cutoff
              potential terminal_value (\<lambda>x. first x - second x)
              coordinates) =
        (\<lambda>coordinates.
          exp (\<i> * of_real (?phase coordinates)) *
              ?first_amplitude coordinates -
            exp (\<i> * of_real (?phase coordinates)) *
              ?second_amplitude coordinates)"
    by (rule ext)
      (simp only: slp_left_branch_complex_amplitude_finite_output_diff
        right_diff_distrib)
  show ?thesis
    unfolding slp_left_branch_finite_oscillatory_integral_def
    apply (subst integrand_diff)
    by (rule Bochner_Integration.integral_diff[OF
          first_integrand_integrable second_integrand_integrable])
qed

theorem slp_left_branch_principal_finite_integral_eq_base_pair:
  fixes branch_dummy :: "'i::finite itself"
  assumes terminal_test_amplitude_integrable:
      "integrable lborel
        (slp_left_branch_complex_amplitude_finite root_weight cutoff potential
          terminal_value test ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    and unit_source_amplitude_integrable:
      "integrable lborel
        (slp_left_branch_complex_amplitude_finite root_weight cutoff potential
          (\<lambda>_. 1) (\<lambda>u. test u * terminal_value u) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
  shows
    "slp_left_branch_principal_finite_integral TYPE('i) tau root_weight
        cutoff potential terminal_value test =
      slp_left_branch_finite_oscillatory_integral TYPE('i) tau root_weight
          cutoff potential terminal_value test -
        slp_left_branch_finite_oscillatory_integral TYPE('i) tau root_weight
          cutoff potential (\<lambda>_. 1)
            (\<lambda>u. test u * terminal_value u)"
proof -
  let ?phase =
    "\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
      tau * slp_one_sided_finite_residual coordinates"
  let ?terminal_amplitude =
    "slp_left_branch_complex_amplitude_finite root_weight cutoff potential
      terminal_value test ::
      'i slp_left_branch_finite_coordinates \<Rightarrow> complex"
  let ?unit_amplitude =
    "slp_left_branch_complex_amplitude_finite root_weight cutoff potential
      (\<lambda>_. 1) (\<lambda>u. test u * terminal_value u) ::
      'i slp_left_branch_finite_coordinates \<Rightarrow> complex"
  have residual_measurable:
      "(slp_one_sided_finite_residual ::
        'i slp_left_branch_finite_coordinates \<Rightarrow> real) \<in>
        borel_measurable lborel"
    unfolding slp_one_sided_finite_residual_def
    using measurable_compose[
      OF measurable_compose[
        OF slp_one_sided_finite_to_packed_coordinates_measurable measurable_snd]
        slp_one_sided_packed_residual_measurable]
    by (simp only: comp_def)
  have phase_measurable: "?phase \<in> borel_measurable lborel"
    using residual_measurable by measurable
  have terminal_integrand_integrable:
      "integrable lborel
        (\<lambda>coordinates. exp (\<i> * of_real (?phase coordinates)) *
          ?terminal_amplitude coordinates)"
    by (rule slp_unit_modulus_real_phase_integrable[OF
          terminal_test_amplitude_integrable phase_measurable])
  have unit_integrand_integrable:
      "integrable lborel
        (\<lambda>coordinates. exp (\<i> * of_real (?phase coordinates)) *
          ?unit_amplitude coordinates)"
    by (rule slp_unit_modulus_real_phase_integrable[OF
          unit_source_amplitude_integrable phase_measurable])
  have terminal_integrand_integrable_raw:
      "integrable lborel
        (\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
          exp (\<i> * of_real
            (tau * slp_left_branch_residual
              (slp_finite_branch_pair_list
                (\<lambda>i. fst (fst (snd coordinates)) $ i)
                (\<lambda>i. snd (fst (snd coordinates)) $ i))
              (snd (snd coordinates)))) *
          ?terminal_amplitude coordinates)"
    using terminal_integrand_integrable
    by (simp only: slp_one_sided_finite_residual_eq_left_branch)
  have unit_integrand_integrable_raw:
      "integrable lborel
        (\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
          exp (\<i> * of_real
            (tau * slp_left_branch_residual
              (slp_finite_branch_pair_list
                (\<lambda>i. fst (fst (snd coordinates)) $ i)
                (\<lambda>i. snd (fst (snd coordinates)) $ i))
              (snd (snd coordinates)))) *
          ?unit_amplitude coordinates)"
    using unit_integrand_integrable
    by (simp only: slp_one_sided_finite_residual_eq_left_branch)
  show ?thesis
    unfolding slp_left_branch_principal_finite_integral_def
      slp_left_branch_principal_finite_bracket_def
      slp_left_branch_finite_oscillatory_integral_def
    apply (simp only: slp_one_sided_finite_residual_eq_left_branch
      right_diff_distrib)
    by (rule Bochner_Integration.integral_diff[OF
          terminal_integrand_integrable_raw unit_integrand_integrable_raw])
qed

theorem slp_left_branch_finite_cancellation_model_v2_eq_evaluated_pair:
  fixes branch_dummy :: "'i::finite itself"
    and center_field terminal_value root_weight cutoff potential ::
      "slp_point \<Rightarrow> complex"
  assumes terminal_center_amplitude_integrable:
      "integrable lborel
        (slp_left_branch_complex_amplitude_finite root_weight cutoff potential
          terminal_value (slp_center_average tau center_field) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    and terminal_base_amplitude_integrable:
      "integrable lborel
        (slp_left_branch_complex_amplitude_finite root_weight cutoff potential
          terminal_value center_field ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    and unit_center_source_amplitude_integrable:
      "integrable lborel
        (slp_left_branch_complex_amplitude_finite root_weight cutoff potential
          (\<lambda>_. 1)
            (slp_center_average tau
              (\<lambda>u. center_field u * terminal_value u)) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    and unit_base_source_amplitude_integrable:
      "integrable lborel
        (slp_left_branch_complex_amplitude_finite root_weight cutoff potential
          (\<lambda>_. 1) (\<lambda>u. center_field u * terminal_value u) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
  shows
    "slp_left_branch_finite_cancellation_model_v2 TYPE('i) tau root_weight
        cutoff potential terminal_value center_field =
      slp_left_branch_finite_oscillatory_integral TYPE('i) tau root_weight
          cutoff potential terminal_value
            (slp_center_average tau center_field) -
        slp_left_branch_finite_oscillatory_integral TYPE('i) tau root_weight
          cutoff potential (\<lambda>_. 1)
            (slp_center_average tau
              (\<lambda>u. center_field u * terminal_value u))"
proof -
  have principal:
      "slp_left_branch_principal_finite_integral TYPE('i) tau root_weight
          cutoff potential terminal_value center_field =
        slp_left_branch_finite_oscillatory_integral TYPE('i) tau root_weight
            cutoff potential terminal_value center_field -
          slp_left_branch_finite_oscillatory_integral TYPE('i) tau root_weight
            cutoff potential (\<lambda>_. 1)
              (\<lambda>u. center_field u * terminal_value u)"
    by (rule slp_left_branch_principal_finite_integral_eq_base_pair[OF
          terminal_base_amplitude_integrable
          unit_base_source_amplitude_integrable])
  have terminal_error:
      "slp_left_branch_finite_oscillatory_integral TYPE('i) tau root_weight
          cutoff potential terminal_value
            (\<lambda>output.
              slp_center_average tau center_field output -
                center_field output) =
        slp_left_branch_finite_oscillatory_integral TYPE('i) tau root_weight
            cutoff potential terminal_value
              (slp_center_average tau center_field) -
          slp_left_branch_finite_oscillatory_integral TYPE('i) tau root_weight
            cutoff potential terminal_value center_field"
    by (rule slp_left_branch_finite_oscillatory_integral_output_diff[OF
          terminal_center_amplitude_integrable
          terminal_base_amplitude_integrable])
  have unit_error:
      "slp_left_branch_finite_oscillatory_integral TYPE('i) tau root_weight
          cutoff potential (\<lambda>_. 1)
            (\<lambda>output.
              slp_center_average tau
                  (\<lambda>u. center_field u * terminal_value u) output -
                center_field output * terminal_value output) =
        slp_left_branch_finite_oscillatory_integral TYPE('i) tau root_weight
            cutoff potential (\<lambda>_. 1)
              (slp_center_average tau
                (\<lambda>u. center_field u * terminal_value u)) -
          slp_left_branch_finite_oscillatory_integral TYPE('i) tau root_weight
            cutoff potential (\<lambda>_. 1)
              (\<lambda>u. center_field u * terminal_value u)"
    by (rule slp_left_branch_finite_oscillatory_integral_output_diff[OF
          unit_center_source_amplitude_integrable
          unit_base_source_amplitude_integrable])
  show ?thesis
    unfolding slp_left_branch_finite_cancellation_model_v2_def
    apply (subst principal)
    apply (subst terminal_error)
    apply (subst unit_error)
    by (simp add: algebra_simps)
qed


end
