theory Inverse_Schrodinger_Lp_Left_Graph_Natural_Zero_Integral
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Left_Graph_Natural_Fubini"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Left_Nested_Graph_Functional"
begin

section \<open>Order-zero natural graph integral\<close>

theorem slp_left_branch_oscillatory_graph_kernel_natural_zero_integral:
  assumes graph_integrable:
    "integrable
      (((PiM {..<0} (\<lambda>_::nat. (lborel :: slp_point measure)))
          \<Otimes>\<^sub>M
        (PiM {..<0} (\<lambda>_::nat. (lborel :: slp_point measure))))
          \<Otimes>\<^sub>M (lborel :: slp_point measure))
      (slp_left_branch_oscillatory_graph_kernel_natural 0 tau center cutoff
        potential terminal_value origin)"
  shows
    "integral\<^sup>L
        (((PiM {..<0} (\<lambda>_::nat. (lborel :: slp_point measure)))
            \<Otimes>\<^sub>M
          (PiM {..<0} (\<lambda>_::nat. (lborel :: slp_point measure))))
            \<Otimes>\<^sub>M (lborel :: slp_point measure))
        (slp_left_branch_oscillatory_graph_kernel_natural 0 tau center cutoff
          potential terminal_value origin) =
      slp_left_branch_nested_graph_functional 0 tau center cutoff potential
        terminal_value origin"
proof -
  let ?M = "\<lambda>_::nat. (lborel :: slp_point measure)"
  let ?MP = "PiM {..<0} ?M"
  let ?MF = "?MP \<Otimes>\<^sub>M ?MP"
  let ?All = "?MF \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?kernel =
    "slp_left_branch_oscillatory_graph_kernel_natural 0 tau center cutoff
      potential terminal_value origin"
  interpret product: product_sigma_finite ?M
    by standard
  have MP_sigma: "sigma_finite_measure ?MP"
    by (rule product.sigma_finite) simp
  interpret MP: sigma_finite_measure ?MP
    by (rule MP_sigma)
  interpret family_pair: pair_sigma_finite ?MP ?MP ..
  have MF_sigma: "sigma_finite_measure ?MF"
    by standard
  interpret MF: sigma_finite_measure ?MF
    by (rule MF_sigma)
  interpret all_coordinates:
    pair_sigma_finite ?MF "(lborel :: slp_point measure)" ..
  have terminal_split:
      "integral\<^sup>L ?All ?kernel =
        integral\<^sup>L ?MF
          (\<lambda>families. integral\<^sup>L (lborel :: slp_point measure)
            (\<lambda>terminal. ?kernel (families, terminal)))"
    using all_coordinates.integral_fst'[OF graph_integrable]
    by simp
  have families_integrable:
      "integrable ?MF
        (\<lambda>families. integral\<^sup>L (lborel :: slp_point measure)
          (\<lambda>terminal. ?kernel (families, terminal)))"
    using all_coordinates.integrable_fst'[OF graph_integrable]
    by simp
  have family_split:
      "integral\<^sup>L ?MF
          (\<lambda>families. integral\<^sup>L (lborel :: slp_point measure)
            (\<lambda>terminal. ?kernel (families, terminal))) =
        integral\<^sup>L ?MP (\<lambda>positive.
          integral\<^sup>L ?MP (\<lambda>negative.
            integral\<^sup>L (lborel :: slp_point measure) (\<lambda>terminal.
              ?kernel ((positive, negative), terminal))))"
    using family_pair.integral_fst'[OF families_integrable]
    by simp
  show ?thesis
    using terminal_split family_split
    unfolding slp_left_branch_oscillatory_graph_kernel_natural_def
      slp_left_branch_nested_graph_functional.simps
    by (simp add: PiM_empty pair_measure_count_space
        lebesgue_integral_count_space_finite)
qed

end
