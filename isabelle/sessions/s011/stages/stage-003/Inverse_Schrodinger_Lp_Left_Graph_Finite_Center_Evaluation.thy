theory Inverse_Schrodinger_Lp_Left_Graph_Finite_Center_Evaluation
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Graph_Finite_Center_Fubini"
begin

section \<open>Evaluation of the finite center fiber\<close>

lemma slp_center_average_as_symmetric_center_fiber:
  "of_real (tau / pi) *
      (\<integral>center. center_field center *
        slp_center_kernel tau center output \<partial>lborel) =
    slp_center_average tau center_field output"
proof -
  have pointwise:
      "center_field center * slp_center_kernel tau center output =
        slp_center_kernel tau output center * center_field center"
    for center
    by (simp only: slp_center_kernel_symmetric)
      (simp add: algebra_simps)
  show ?thesis
    unfolding slp_center_average_def
    by (simp only: pointwise)
qed

theorem slp_left_branch_finite_center_integrand_scaled_fubini:
  fixes center_field :: "slp_point \<Rightarrow> complex"
    and amplitude ::
      "'i::finite slp_left_branch_finite_coordinates \<Rightarrow> complex"
  assumes center_integrable: "integrable lborel center_field"
    and amplitude_integrable: "integrable lborel amplitude"
  shows
    "of_real (tau / pi) *
        (\<integral>center. \<integral>coordinates.
          slp_left_branch_finite_center_integrand tau center_field amplitude
            (center, coordinates) \<partial>lborel \<partial>lborel) =
      (\<integral>coordinates.
        slp_center_average tau center_field
          (slp_left_branch_output
            (slp_finite_branch_pair_list
              (\<lambda>i. fst (fst (snd coordinates)) $ i)
              (\<lambda>i. snd (fst (snd coordinates)) $ i))
            (snd (snd coordinates))) *
          (exp (\<i> * of_real
              (tau * slp_one_sided_finite_residual coordinates)) *
            amplitude coordinates) \<partial>lborel)"
proof -
  have fubini:
      "(\<integral>center. \<integral>coordinates.
          slp_left_branch_finite_center_integrand tau center_field amplitude
            (center, coordinates) \<partial>lborel \<partial>lborel) =
        (\<integral>coordinates. \<integral>center.
          slp_left_branch_finite_center_integrand tau center_field amplitude
            (center, coordinates) \<partial>lborel \<partial>lborel)"
    by (rule slp_left_branch_finite_center_integrand_fubini[
          OF center_integrable amplitude_integrable])
  have inner:
      "(\<integral>center.
          slp_left_branch_finite_center_integrand tau center_field amplitude
            (center, coordinates) \<partial>lborel) =
        (\<integral>center. center_field center *
          slp_center_kernel tau center
            (slp_left_branch_output
              (slp_finite_branch_pair_list
                (\<lambda>i. fst (fst (snd coordinates)) $ i)
                (\<lambda>i. snd (fst (snd coordinates)) $ i))
              (snd (snd coordinates))) \<partial>lborel) *
          (exp (\<i> * of_real
              (tau * slp_one_sided_finite_residual coordinates)) *
            amplitude coordinates)"
    for coordinates :: "'i slp_left_branch_finite_coordinates"
    unfolding slp_left_branch_finite_center_integrand_def
    by (simp only: fst_conv snd_conv
        Bochner_Integration.integral_mult_left_zero)
  have fiber:
      "of_real (tau / pi) *
          (\<integral>center.
            slp_left_branch_finite_center_integrand tau center_field amplitude
              (center, coordinates) \<partial>lborel) =
        slp_center_average tau center_field
          (slp_left_branch_output
            (slp_finite_branch_pair_list
              (\<lambda>i. fst (fst (snd coordinates)) $ i)
              (\<lambda>i. snd (fst (snd coordinates)) $ i))
            (snd (snd coordinates))) *
          (exp (\<i> * of_real
              (tau * slp_one_sided_finite_residual coordinates)) *
            amplitude coordinates)"
    for coordinates :: "'i slp_left_branch_finite_coordinates"
  proof -
    have center_fiber:
        "of_real (tau / pi) *
            (\<integral>center. center_field center *
              slp_center_kernel tau center
                (slp_left_branch_output
                  (slp_finite_branch_pair_list
                    (\<lambda>i. fst (fst (snd coordinates)) $ i)
                    (\<lambda>i. snd (fst (snd coordinates)) $ i))
                  (snd (snd coordinates))) \<partial>lborel) =
          slp_center_average tau center_field
            (slp_left_branch_output
              (slp_finite_branch_pair_list
                (\<lambda>i. fst (fst (snd coordinates)) $ i)
                (\<lambda>i. snd (fst (snd coordinates)) $ i))
              (snd (snd coordinates)))"
      by (rule slp_center_average_as_symmetric_center_fiber)
    show ?thesis
      by (simp only: inner mult.assoc[symmetric] center_fiber)
  qed
  have coefficient_through:
      "of_real (tau / pi) *
          (\<integral>coordinates. \<integral>center.
            slp_left_branch_finite_center_integrand tau center_field amplitude
              (center, coordinates) \<partial>lborel \<partial>lborel) =
        (\<integral>coordinates. of_real (tau / pi) *
          (\<integral>center.
            slp_left_branch_finite_center_integrand tau center_field amplitude
              (center, coordinates) \<partial>lborel) \<partial>lborel)"
    by (simp only: Bochner_Integration.integral_mult_right_zero)
  show ?thesis
    using fubini coefficient_through
    by (simp only: fiber)
qed

end
