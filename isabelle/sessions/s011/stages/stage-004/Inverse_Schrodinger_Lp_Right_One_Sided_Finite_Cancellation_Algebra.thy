theory Inverse_Schrodinger_Lp_Right_One_Sided_Finite_Cancellation_Algebra
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Right_One_Sided_Finite_Principal_Integral"
begin

section \<open>Exact direct right finite cancellation algebra\<close>

definition slp_right_branch_finite_cancellation_model ::
    "'i::finite itself \<Rightarrow> real \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow> complex"
where
  "slp_right_branch_finite_cancellation_model dimension_type tau root_weight
      cutoff potential terminal_value phi =
    slp_right_branch_principal_finite_integral dimension_type tau root_weight
        cutoff potential terminal_value phi +
      slp_right_branch_finite_oscillatory_integral dimension_type tau
        root_weight cutoff potential terminal_value
          (\<lambda>output. slp_center_average tau phi output - phi output) -
      slp_right_branch_finite_oscillatory_integral dimension_type tau
        root_weight cutoff potential (\<lambda>_. 1)
          (\<lambda>output.
            slp_center_average tau
                (\<lambda>u. phi u * terminal_value u) output -
              phi output * terminal_value output)"

theorem slp_right_branch_finite_oscillatory_integral_output_diff:
  fixes branch_dummy :: "'i::finite itself"
    and first second :: "slp_point \<Rightarrow> complex"
  assumes first_amplitude_integrable:
      "integrable lborel
        (slp_right_branch_complex_amplitude_finite root_weight cutoff potential
          terminal_value first ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    and second_amplitude_integrable:
      "integrable lborel
        (slp_right_branch_complex_amplitude_finite root_weight cutoff potential
          terminal_value second ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
  shows
    "slp_right_branch_finite_oscillatory_integral TYPE('i) tau root_weight
        cutoff potential terminal_value (\<lambda>x. first x - second x) =
      slp_right_branch_finite_oscillatory_integral TYPE('i) tau root_weight
          cutoff potential terminal_value first -
        slp_right_branch_finite_oscillatory_integral TYPE('i) tau root_weight
          cutoff potential terminal_value second"
proof -
  let ?phase =
    "\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
      tau * slp_one_sided_finite_residual coordinates"
  let ?first_amplitude =
    "slp_right_branch_complex_amplitude_finite root_weight cutoff potential
      terminal_value first ::
      'i slp_left_branch_finite_coordinates \<Rightarrow> complex"
  let ?second_amplitude =
    "slp_right_branch_complex_amplitude_finite root_weight cutoff potential
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
  have amplitude_diff:
      "slp_right_branch_complex_amplitude_finite root_weight cutoff potential
          terminal_value (\<lambda>x. first x - second x) coordinates =
        ?first_amplitude coordinates - ?second_amplitude coordinates"
    for coordinates :: "'i slp_left_branch_finite_coordinates"
    unfolding slp_right_branch_complex_amplitude_finite_def
    by (simp add: algebra_simps)
  have integrand_diff:
      "(\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
          exp (\<i> * of_real (?phase coordinates)) *
            slp_right_branch_complex_amplitude_finite root_weight cutoff
              potential terminal_value (\<lambda>x. first x - second x)
              coordinates) =
        (\<lambda>coordinates.
          exp (\<i> * of_real (?phase coordinates)) *
              ?first_amplitude coordinates -
            exp (\<i> * of_real (?phase coordinates)) *
              ?second_amplitude coordinates)"
    by (rule ext) (simp only: amplitude_diff right_diff_distrib)
  show ?thesis
    unfolding slp_right_branch_finite_oscillatory_integral_def
    apply (subst integrand_diff)
    by (rule Bochner_Integration.integral_diff[OF
          first_integrand_integrable second_integrand_integrable])
qed

theorem slp_right_branch_finite_cancellation_model_eq_evaluated_pair:
  fixes branch_dummy :: "'i::finite itself"
    and center_field terminal_value root_weight cutoff potential ::
      "slp_point \<Rightarrow> complex"
  assumes terminal_center_amplitude_integrable:
      "integrable lborel
        (slp_right_branch_complex_amplitude_finite root_weight cutoff potential
          terminal_value (slp_center_average tau center_field) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    and terminal_base_amplitude_integrable:
      "integrable lborel
        (slp_right_branch_complex_amplitude_finite root_weight cutoff potential
          terminal_value center_field ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    and unit_center_source_amplitude_integrable:
      "integrable lborel
        (slp_right_branch_complex_amplitude_finite root_weight cutoff potential
          (\<lambda>_. 1)
            (slp_center_average tau
              (\<lambda>u. center_field u * terminal_value u)) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    and unit_base_source_amplitude_integrable:
      "integrable lborel
        (slp_right_branch_complex_amplitude_finite root_weight cutoff potential
          (\<lambda>_. 1) (\<lambda>u. center_field u * terminal_value u) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
  shows
    "slp_right_branch_finite_cancellation_model TYPE('i) tau root_weight
        cutoff potential terminal_value center_field =
      slp_right_branch_finite_oscillatory_integral TYPE('i) tau root_weight
          cutoff potential terminal_value
            (slp_center_average tau center_field) -
        slp_right_branch_finite_oscillatory_integral TYPE('i) tau root_weight
          cutoff potential (\<lambda>_. 1)
            (slp_center_average tau
              (\<lambda>u. center_field u * terminal_value u))"
proof -
  have principal:
      "slp_right_branch_principal_finite_integral TYPE('i) tau root_weight
          cutoff potential terminal_value center_field =
        slp_right_branch_finite_oscillatory_integral TYPE('i) tau root_weight
            cutoff potential terminal_value center_field -
          slp_right_branch_finite_oscillatory_integral TYPE('i) tau root_weight
            cutoff potential (\<lambda>_. 1)
              (\<lambda>u. center_field u * terminal_value u)"
    by (rule slp_right_branch_principal_finite_integral_eq_base_pair[OF
          terminal_base_amplitude_integrable
          unit_base_source_amplitude_integrable])
  have terminal_error:
      "slp_right_branch_finite_oscillatory_integral TYPE('i) tau root_weight
          cutoff potential terminal_value
            (\<lambda>output.
              slp_center_average tau center_field output -
                center_field output) =
        slp_right_branch_finite_oscillatory_integral TYPE('i) tau root_weight
            cutoff potential terminal_value
              (slp_center_average tau center_field) -
          slp_right_branch_finite_oscillatory_integral TYPE('i) tau root_weight
            cutoff potential terminal_value center_field"
    by (rule slp_right_branch_finite_oscillatory_integral_output_diff[OF
          terminal_center_amplitude_integrable
          terminal_base_amplitude_integrable])
  have unit_error:
      "slp_right_branch_finite_oscillatory_integral TYPE('i) tau root_weight
          cutoff potential (\<lambda>_. 1)
            (\<lambda>output.
              slp_center_average tau
                  (\<lambda>u. center_field u * terminal_value u) output -
                center_field output * terminal_value output) =
        slp_right_branch_finite_oscillatory_integral TYPE('i) tau root_weight
            cutoff potential (\<lambda>_. 1)
              (slp_center_average tau
                (\<lambda>u. center_field u * terminal_value u)) -
          slp_right_branch_finite_oscillatory_integral TYPE('i) tau root_weight
            cutoff potential (\<lambda>_. 1)
              (\<lambda>u. center_field u * terminal_value u)"
    by (rule slp_right_branch_finite_oscillatory_integral_output_diff[OF
          unit_center_source_amplitude_integrable
          unit_base_source_amplitude_integrable])
  show ?thesis
    unfolding slp_right_branch_finite_cancellation_model_def
    apply (subst principal)
    apply (subst terminal_error)
    apply (subst unit_error)
    by (simp add: algebra_simps)
qed

end
