theory Inverse_Schrodinger_Lp_Right_Graph_Finite_Center_Output
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Right_Graph_Finite_Center_Fubini"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Graph_Finite_Center_Evaluation"
begin

section \<open>Absorption of evaluated right center fibers\<close>

definition slp_right_branch_finite_oscillatory_integral ::
    "'i::finite itself \<Rightarrow> real \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow> complex"
where
  "slp_right_branch_finite_oscillatory_integral branch_dummy omega root_weight
      cutoff potential terminal_value output_factor =
    integral\<^sup>L lborel
      (\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
        exp (\<i> * of_real
          (omega * slp_one_sided_finite_residual coordinates)) *
        slp_right_branch_complex_amplitude_finite root_weight cutoff potential
          terminal_value output_factor coordinates)"

lemma slp_right_branch_finite_center_output_absorb:
  fixes coordinates :: "'i::finite slp_left_branch_finite_coordinates"
  shows
    "output_factor
        (slp_right_branch_output
          (slp_finite_branch_pair_list
            (\<lambda>i. fst (fst (snd coordinates)) $ i)
            (\<lambda>i. snd (fst (snd coordinates)) $ i))
          (snd (snd coordinates))) *
        (exp (\<i> * of_real
            (tau * slp_one_sided_finite_residual coordinates)) *
          slp_right_branch_complex_amplitude_finite root_weight cutoff
            potential terminal_value (\<lambda>_. 1) coordinates) =
      exp (\<i> * of_real
          (tau * slp_one_sided_finite_residual coordinates)) *
        slp_right_branch_complex_amplitude_finite root_weight cutoff potential
          terminal_value output_factor coordinates"
  unfolding slp_right_branch_complex_amplitude_finite_def
  by (simp add: algebra_simps)

lemma slp_right_branch_finite_center_output_integral:
  fixes branch_dummy :: "'i::finite itself"
  shows
    "(\<integral>(coordinates :: 'i slp_left_branch_finite_coordinates).
        output_factor
          (slp_right_branch_output
            (slp_finite_branch_pair_list
              (\<lambda>i. fst (fst (snd coordinates)) $ i)
              (\<lambda>i. snd (fst (snd coordinates)) $ i))
            (snd (snd coordinates))) *
          (exp (\<i> * of_real
              (tau * slp_one_sided_finite_residual coordinates)) *
            slp_right_branch_complex_amplitude_finite root_weight cutoff
              potential terminal_value (\<lambda>_. 1) coordinates)
      \<partial>lborel) =
    slp_right_branch_finite_oscillatory_integral TYPE('i) tau root_weight
      cutoff potential terminal_value output_factor"
  unfolding slp_right_branch_finite_oscillatory_integral_def
  by (simp only: slp_right_branch_finite_center_output_absorb)

theorem slp_right_branch_finite_center_integrand_scaled_fubini:
  fixes center_field :: "slp_point \<Rightarrow> complex"
    and amplitude ::
      "'i::finite slp_left_branch_finite_coordinates \<Rightarrow> complex"
  assumes center_integrable: "integrable lborel center_field"
    and amplitude_integrable: "integrable lborel amplitude"
  shows
    "of_real (tau / pi) *
        (\<integral>center.
          \<integral>(coordinates :: 'i slp_left_branch_finite_coordinates).
          slp_right_branch_finite_center_integrand tau center_field amplitude
            (center, coordinates) \<partial>lborel \<partial>lborel) =
      (\<integral>(coordinates :: 'i slp_left_branch_finite_coordinates).
        slp_center_average tau center_field
          (slp_right_branch_output
            (slp_finite_branch_pair_list
              (\<lambda>i. fst (fst (snd coordinates)) $ i)
              (\<lambda>i. snd (fst (snd coordinates)) $ i))
            (snd (snd coordinates))) *
          (exp (\<i> * of_real
              (tau * slp_one_sided_finite_residual coordinates)) *
            amplitude coordinates) \<partial>lborel)"
proof -
  note left_scaled =
    slp_left_branch_finite_center_integrand_scaled_fubini[
      where tau=tau and center_field=center_field and amplitude=amplitude,
      OF center_integrable amplitude_integrable]
  show ?thesis
    using left_scaled
    unfolding slp_right_branch_finite_center_integrand_eq_left
    by (simp only: slp_left_branch_output_eq_right)
qed

end
