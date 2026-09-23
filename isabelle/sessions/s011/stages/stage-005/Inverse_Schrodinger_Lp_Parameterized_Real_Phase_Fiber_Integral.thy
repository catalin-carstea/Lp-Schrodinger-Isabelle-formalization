theory Inverse_Schrodinger_Lp_Parameterized_Real_Phase_Fiber_Integral
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Parameterized_Complex_Fiber_Integral"
begin

section \<open>Parameterized real-phase fiber integrals\<close>

definition slp_parameterized_real_phase_integrand ::
    "real \<Rightarrow>
      ('a::euclidean_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> real) \<Rightarrow>
      ('a \<Rightarrow> 'b \<Rightarrow> complex) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> complex"
where
  "slp_parameterized_real_phase_integrand frequency phase amplitude center fiber =
    exp (\<i> * of_real (frequency * phase center fiber)) *
      amplitude center fiber"

definition slp_parameterized_real_phase_fiber_integral ::
    "real \<Rightarrow>
      ('a::euclidean_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> real) \<Rightarrow>
      ('a \<Rightarrow> 'b \<Rightarrow> complex) \<Rightarrow> 'a \<Rightarrow> complex"
where
  "slp_parameterized_real_phase_fiber_integral frequency phase amplitude =
    slp_parameterized_complex_fiber_integral
      (slp_parameterized_real_phase_integrand frequency phase amplitude)"

theorem slp_parameterized_real_phase_fiber_integral_measurable_and_bound:
  fixes phase ::
      "'a::euclidean_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> real"
    and amplitude :: "'a \<Rightarrow> 'b \<Rightarrow> complex"
  assumes phase_measurable:
      "case_prod phase \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    and amplitude_measurable:
      "case_prod amplitude \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    and amplitude_integrable:
      "AE center in lborel. integrable lborel (amplitude center)"
  shows
    "(\<lambda>center.
      slp_parameterized_real_phase_fiber_integral frequency phase amplitude
        center) \<in> borel_measurable lborel"
    and
    "AE center in lborel.
      ennreal (norm_class.norm
        (slp_parameterized_real_phase_fiber_integral frequency phase amplitude
          center)) \<le>
      slp_parameterized_complex_absolute_fiber_mass amplitude center"
proof -
  let ?oscillatory =
    "slp_parameterized_real_phase_integrand frequency phase amplitude"
  have oscillatory_measurable:
      "case_prod ?oscillatory
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    unfolding slp_parameterized_real_phase_integrand_def
    using phase_measurable amplitude_measurable
    by measurable
  have oscillatory_integrable:
      "AE center in lborel. integrable lborel (?oscillatory center)"
    using amplitude_integrable
  proof eventually_elim
    fix center
    assume center_integrable: "integrable lborel (amplitude center)"
    have center_space:
        "center \<in> space (lborel :: 'a measure)"
      by simp
    have phase_section_measurable:
        "phase center \<in> borel_measurable lborel"
    proof -
      note phase_section_raw =
        measurable_compose_Pair1[OF center_space phase_measurable]
      show ?thesis
        using phase_section_raw by simp
    qed
    have scaled_phase_measurable:
        "(\<lambda>fiber. frequency * phase center fiber)
          \<in> borel_measurable lborel"
      using phase_section_measurable by measurable
    show "integrable lborel (?oscillatory center)"
      unfolding slp_parameterized_real_phase_integrand_def
      by (rule slp_unit_modulus_real_phase_integrable[OF center_integrable
            scaled_phase_measurable])
  qed
  note generic =
    slp_parameterized_complex_fiber_integral_measurable_and_bound[
      OF oscillatory_measurable oscillatory_integrable]
  show
      "(\<lambda>center.
        slp_parameterized_real_phase_fiber_integral frequency phase amplitude
          center) \<in> borel_measurable lborel"
    using generic(1)
    unfolding slp_parameterized_real_phase_fiber_integral_def .
  have mass_identity:
      "slp_parameterized_complex_absolute_fiber_mass ?oscillatory center =
        slp_parameterized_complex_absolute_fiber_mass amplitude center"
    for center
    unfolding slp_parameterized_complex_absolute_fiber_mass_def
      slp_parameterized_real_phase_integrand_def
    by (simp only: norm_mult norm_exp_i_times mult_1_left)
  from generic(2) show
      "AE center in lborel.
        ennreal (norm_class.norm
          (slp_parameterized_real_phase_fiber_integral frequency phase
            amplitude center)) \<le>
        slp_parameterized_complex_absolute_fiber_mass amplitude center"
  proof eventually_elim
    fix center
    assume bound:
        "ennreal (norm_class.norm
          (slp_parameterized_complex_fiber_integral ?oscillatory center)) \<le>
        slp_parameterized_complex_absolute_fiber_mass ?oscillatory center"
    show
        "ennreal (norm_class.norm
          (slp_parameterized_real_phase_fiber_integral frequency phase
            amplitude center)) \<le>
        slp_parameterized_complex_absolute_fiber_mass amplitude center"
      using bound
      by (simp only: slp_parameterized_real_phase_fiber_integral_def
          mass_identity)
  qed
qed

end
