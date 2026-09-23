theory Inverse_Schrodinger_Lp_Right_Graph_Finite_Center_Fubini
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Right_Graph_Finite_Primitive_Difference"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Graph_Finite_Center_Fubini"
begin

section \<open>Finite right center-coordinate integrability and Fubini\<close>

definition slp_right_branch_finite_center_integrand ::
    "real \<Rightarrow> (slp_point \<Rightarrow> complex) \<Rightarrow>
      ('i::finite slp_left_branch_finite_coordinates \<Rightarrow> complex) \<Rightarrow>
      slp_point \<times> 'i slp_left_branch_finite_coordinates \<Rightarrow> complex"
where
  "slp_right_branch_finite_center_integrand tau center_field amplitude pair =
    center_field (fst pair) *
      slp_center_kernel tau (fst pair)
        (slp_right_branch_output
          (slp_finite_branch_pair_list
            (\<lambda>i. fst (fst (snd (snd pair))) $ i)
            (\<lambda>i. snd (fst (snd (snd pair))) $ i))
          (snd (snd (snd pair)))) *
      (exp (\<i> * of_real
          (tau * slp_one_sided_finite_residual (snd pair))) *
        amplitude (snd pair))"

lemma slp_right_branch_finite_center_integrand_eq_left:
  "slp_right_branch_finite_center_integrand tau center_field amplitude =
    slp_left_branch_finite_center_integrand tau center_field amplitude"
  by (rule ext)
    (simp add: slp_right_branch_finite_center_integrand_def
      slp_left_branch_finite_center_integrand_def
      slp_left_branch_output_eq_right)

theorem slp_right_branch_finite_center_integrand_integrable:
  fixes center_field :: "slp_point \<Rightarrow> complex"
    and amplitude :: "'i::finite slp_left_branch_finite_coordinates \<Rightarrow> complex"
  assumes center_integrable: "integrable lborel center_field"
    and amplitude_integrable: "integrable lborel amplitude"
  shows
    "integrable
      ((lborel :: slp_point measure) \<Otimes>\<^sub>M
        (lborel :: 'i slp_left_branch_finite_coordinates measure))
      (slp_right_branch_finite_center_integrand tau center_field amplitude)"
  unfolding slp_right_branch_finite_center_integrand_eq_left
  by (rule slp_left_branch_finite_center_integrand_integrable[
        OF center_integrable amplitude_integrable])

theorem slp_right_branch_finite_center_integrand_fubini:
  fixes center_field :: "slp_point \<Rightarrow> complex"
    and amplitude :: "'i::finite slp_left_branch_finite_coordinates \<Rightarrow> complex"
  assumes center_integrable: "integrable lborel center_field"
    and amplitude_integrable: "integrable lborel amplitude"
  shows
    "(\<integral>center. \<integral>coordinates.
        slp_right_branch_finite_center_integrand tau center_field amplitude
          (center, coordinates) \<partial>lborel \<partial>lborel) =
      (\<integral>coordinates. \<integral>center.
        slp_right_branch_finite_center_integrand tau center_field amplitude
          (center, coordinates) \<partial>lborel \<partial>lborel)"
  unfolding slp_right_branch_finite_center_integrand_eq_left
  by (rule slp_left_branch_finite_center_integrand_fubini[
        OF center_integrable amplitude_integrable])

end
