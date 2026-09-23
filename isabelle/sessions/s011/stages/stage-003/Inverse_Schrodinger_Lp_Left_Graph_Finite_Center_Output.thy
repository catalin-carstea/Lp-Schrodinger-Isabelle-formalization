theory Inverse_Schrodinger_Lp_Left_Graph_Finite_Center_Output
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Graph_Finite_Center_Evaluation"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_Oscillatory_Output_Bound"
begin

section \<open>Absorption of evaluated center fibers into the output factor\<close>

lemma slp_left_branch_finite_center_output_absorb:
  fixes coordinates :: "'i::finite slp_left_branch_finite_coordinates"
  shows
    "output_factor
        (slp_left_branch_output
          (slp_finite_branch_pair_list
            (\<lambda>i. fst (fst (snd coordinates)) $ i)
            (\<lambda>i. snd (fst (snd coordinates)) $ i))
          (snd (snd coordinates))) *
        (exp (\<i> * of_real
            (tau * slp_one_sided_finite_residual coordinates)) *
          slp_left_branch_complex_amplitude_finite root_weight cutoff
            potential terminal_value (\<lambda>_. 1) coordinates) =
      exp (\<i> * of_real
          (tau * slp_one_sided_finite_residual coordinates)) *
        slp_left_branch_complex_amplitude_finite root_weight cutoff potential
          terminal_value output_factor coordinates"
  unfolding slp_left_branch_complex_amplitude_finite_def
  by (simp add: algebra_simps)

lemma slp_left_branch_finite_center_output_integral:
  fixes branch_dummy :: "'i::finite itself"
  shows
    "(\<integral>(coordinates :: 'i slp_left_branch_finite_coordinates).
        output_factor
          (slp_left_branch_output
            (slp_finite_branch_pair_list
              (\<lambda>i. fst (fst (snd coordinates)) $ i)
              (\<lambda>i. snd (fst (snd coordinates)) $ i))
            (snd (snd coordinates))) *
          (exp (\<i> * of_real
              (tau * slp_one_sided_finite_residual coordinates)) *
            slp_left_branch_complex_amplitude_finite root_weight cutoff
              potential terminal_value (\<lambda>_. 1) coordinates)
      \<partial>lborel) =
    slp_left_branch_finite_oscillatory_integral TYPE('i) tau root_weight
      cutoff potential terminal_value output_factor"
  unfolding slp_left_branch_finite_oscillatory_integral_def
  by (simp only: slp_left_branch_finite_center_output_absorb)

theorem slp_left_branch_finite_center_primitive_pair_evaluated:
  fixes branch_dummy :: "'i::finite itself"
    and center_field primitive root_weight cutoff potential ::
      "slp_point \<Rightarrow> complex"
  assumes center_integrable: "integrable lborel center_field"
    and source_integrable:
      "integrable lborel (\<lambda>u. center_field u * primitive u)"
    and primitive_amplitude_integrable:
      "integrable lborel
        (slp_left_branch_complex_amplitude_finite root_weight cutoff potential
          primitive (\<lambda>_. 1) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    and unit_amplitude_integrable:
      "integrable lborel
        (slp_left_branch_complex_amplitude_finite root_weight cutoff potential
          (\<lambda>_. 1) (\<lambda>_. 1) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
  shows
    "of_real (tau / pi) *
        (\<integral>center.
          \<integral>(coordinates :: 'i slp_left_branch_finite_coordinates).
          slp_left_branch_finite_center_integrand tau center_field
            (slp_left_branch_complex_amplitude_finite root_weight cutoff
              potential primitive (\<lambda>_. 1))
            (center, coordinates) \<partial>lborel \<partial>lborel) -
      of_real (tau / pi) *
        (\<integral>center.
          \<integral>(coordinates :: 'i slp_left_branch_finite_coordinates).
          slp_left_branch_finite_center_integrand tau
            (\<lambda>u. center_field u * primitive u)
            (slp_left_branch_complex_amplitude_finite root_weight cutoff
              potential (\<lambda>_. 1) (\<lambda>_. 1))
            (center, coordinates) \<partial>lborel \<partial>lborel) =
      slp_left_branch_finite_oscillatory_integral TYPE('i) tau root_weight
          cutoff potential primitive (slp_center_average tau center_field) -
        slp_left_branch_finite_oscillatory_integral TYPE('i) tau root_weight
          cutoff potential (\<lambda>_. 1)
            (slp_center_average tau
              (\<lambda>u. center_field u * primitive u))"
proof -
  note primitive_evaluated =
    slp_left_branch_finite_center_integrand_scaled_fubini[
      where tau=tau and center_field=center_field and
        amplitude="slp_left_branch_complex_amplitude_finite root_weight cutoff
          potential primitive (\<lambda>_. 1)",
      OF center_integrable primitive_amplitude_integrable]
  note unit_evaluated =
    slp_left_branch_finite_center_integrand_scaled_fubini[
      where tau=tau and
        center_field="\<lambda>u. center_field u * primitive u" and
        amplitude="slp_left_branch_complex_amplitude_finite root_weight cutoff
          potential (\<lambda>_. 1) (\<lambda>_. 1)",
      OF source_integrable unit_amplitude_integrable]
  note primitive_output = slp_left_branch_finite_center_output_integral[
    where 'i='i and tau=tau and root_weight=root_weight and cutoff=cutoff and
      potential=potential and terminal_value=primitive and
      output_factor="slp_center_average tau center_field"]
  note unit_output = slp_left_branch_finite_center_output_integral[
    where 'i='i and tau=tau and root_weight=root_weight and cutoff=cutoff and
      potential=potential and terminal_value="\<lambda>_. 1" and
      output_factor="slp_center_average tau
        (\<lambda>u. center_field u * primitive u)"]
  show ?thesis
    apply (subst primitive_evaluated)
    apply (subst unit_evaluated)
    apply (subst primitive_output)
    apply (subst unit_output)
    by (rule refl)
qed

end
