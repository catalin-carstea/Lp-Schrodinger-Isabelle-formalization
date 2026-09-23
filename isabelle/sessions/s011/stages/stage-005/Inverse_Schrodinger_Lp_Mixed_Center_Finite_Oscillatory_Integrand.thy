theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Oscillatory_Integrand
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Residual_Measurable"
begin

section \<open>Exact oscillatory integrand on the solved center fiber\<close>

definition slp_mixed_center_finite_oscillatory_integrand ::
    "real \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      slp_point \<Rightarrow>
      ('i::finite, 'j::finite) slp_mixed_center_finite_coordinates \<Rightarrow>
      complex"
where
  "slp_mixed_center_finite_oscillatory_integrand frequency root_weight
      left_cutoff left_potential right_cutoff right_potential center
      coordinates =
    slp_parameterized_real_phase_integrand frequency
      slp_mixed_center_finite_residual
      (slp_mixed_center_finite_complex_amplitude root_weight left_cutoff
        left_potential right_cutoff right_potential)
      center coordinates"

theorem slp_mixed_center_finite_oscillatory_integrand_measurable:
  assumes root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    and left_cutoff_measurable:
      "left_cutoff \<in> borel_measurable lborel"
    and left_potential_measurable:
      "left_potential \<in> borel_measurable lborel"
    and right_cutoff_measurable:
      "right_cutoff \<in> borel_measurable lborel"
    and right_potential_measurable:
      "right_potential \<in> borel_measurable lborel"
  shows
    "case_prod (slp_mixed_center_finite_oscillatory_integrand frequency
        root_weight left_cutoff left_potential right_cutoff right_potential ::
      slp_point \<Rightarrow>
        ('i::finite, 'j::finite) slp_mixed_center_finite_coordinates
          \<Rightarrow> complex)
      \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
proof -
  have phase_measurable:
      "case_prod (slp_mixed_center_finite_residual ::
          slp_point \<Rightarrow>
            ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> real)
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_mixed_center_finite_residual_measurable)
  have amplitude_lborel_measurable:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_mixed_center_finite_complex_amplitude root_weight left_cutoff
          left_potential right_cutoff right_potential (fst z) (snd z)))
        \<in> borel_measurable lborel"
    by (rule slp_mixed_center_finite_complex_amplitude_measurable[OF
          root_weight_measurable left_cutoff_measurable
          left_potential_measurable right_cutoff_measurable
          right_potential_measurable])
  have amplitude_measurable:
      "case_prod (slp_mixed_center_finite_complex_amplitude root_weight
          left_cutoff left_potential right_cutoff right_potential ::
        slp_point \<Rightarrow>
          ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using amplitude_lborel_measurable
    by (simp only: lborel_prod split_beta')
  show ?thesis
    unfolding slp_mixed_center_finite_oscillatory_integrand_def
      slp_parameterized_real_phase_integrand_def
    using phase_measurable amplitude_measurable by measurable
qed

theorem slp_mixed_center_finite_oscillatory_integrand_norm:
  "norm_class.norm
      (slp_mixed_center_finite_oscillatory_integrand frequency root_weight
        left_cutoff left_potential right_cutoff right_potential center
        (coordinates ::
          ('i::finite, 'j::finite) slp_mixed_center_finite_coordinates)) =
    norm_class.norm
      (slp_mixed_center_finite_complex_amplitude root_weight left_cutoff
        left_potential right_cutoff right_potential center coordinates)"
  unfolding slp_mixed_center_finite_oscillatory_integrand_def
    slp_parameterized_real_phase_integrand_def
  by (simp only: norm_mult norm_exp_i_times mult_1_left)

end
