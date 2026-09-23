theory Inverse_Schrodinger_Lp_Right_One_Sided_Finite_Principal_Integral
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Right_Born_Finite_Cauchy_Evaluated"
begin

section \<open>The direct right principal finite integral\<close>

definition slp_right_branch_principal_finite_integral ::
    "'i::finite itself \<Rightarrow> real \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow> complex"
where
  "slp_right_branch_principal_finite_integral dimension_type tau root_weight
      cutoff potential terminal_value test =
    integral\<^sup>L lborel
      (\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
        exp (\<i> * of_real
          (tau * slp_one_sided_finite_residual coordinates)) *
        (slp_right_branch_complex_amplitude_finite root_weight cutoff potential
            terminal_value test coordinates -
          slp_right_branch_complex_amplitude_finite root_weight cutoff potential
            (\<lambda>_. 1) (\<lambda>u. test u * terminal_value u) coordinates))"

theorem slp_right_branch_principal_finite_integral_eq_base_pair:
  fixes branch_dummy :: "'i::finite itself"
  assumes terminal_test_amplitude_integrable:
      "integrable lborel
        (slp_right_branch_complex_amplitude_finite root_weight cutoff potential
          terminal_value test ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    and unit_source_amplitude_integrable:
      "integrable lborel
        (slp_right_branch_complex_amplitude_finite root_weight cutoff potential
          (\<lambda>_. 1) (\<lambda>u. test u * terminal_value u) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
  shows
    "slp_right_branch_principal_finite_integral TYPE('i) tau root_weight
        cutoff potential terminal_value test =
      slp_right_branch_finite_oscillatory_integral TYPE('i) tau root_weight
          cutoff potential terminal_value test -
        slp_right_branch_finite_oscillatory_integral TYPE('i) tau root_weight
          cutoff potential (\<lambda>_. 1)
            (\<lambda>u. test u * terminal_value u)"
proof -
  let ?phase =
    "\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
      tau * slp_one_sided_finite_residual coordinates"
  let ?terminal_amplitude =
    "slp_right_branch_complex_amplitude_finite root_weight cutoff potential
      terminal_value test ::
      'i slp_left_branch_finite_coordinates \<Rightarrow> complex"
  let ?unit_amplitude =
    "slp_right_branch_complex_amplitude_finite root_weight cutoff potential
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
  have integrand_diff:
      "(\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
          exp (\<i> * of_real (?phase coordinates)) *
            (?terminal_amplitude coordinates - ?unit_amplitude coordinates)) =
        (\<lambda>coordinates.
          exp (\<i> * of_real (?phase coordinates)) *
              ?terminal_amplitude coordinates -
            exp (\<i> * of_real (?phase coordinates)) *
              ?unit_amplitude coordinates)"
    by (rule ext) (simp only: right_diff_distrib)
  show ?thesis
    unfolding slp_right_branch_principal_finite_integral_def
      slp_right_branch_finite_oscillatory_integral_def
    apply (subst integrand_diff)
    by (rule Bochner_Integration.integral_diff[OF
          terminal_integrand_integrable unit_integrand_integrable])
qed

end
