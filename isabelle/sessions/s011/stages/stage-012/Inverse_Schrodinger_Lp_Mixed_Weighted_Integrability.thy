theory Inverse_Schrodinger_Lp_Mixed_Weighted_Integrability
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Mixed_Bracket_Integrand"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Absolute-mass certificates for the weighted mixed kernels\<close>

lemma slp_mixed_weighted_center_factor_integrable:
  fixes tau :: real and center :: slp_point
    and Q left_cutoff q A right_cutoff qt B H :: slp_scalar_field
  assumes base:
    "integrable lborel
      (slp_mixed_center_finite_weighted_oscillatory_integrand tau
        Q left_cutoff q A right_cutoff qt B (\<lambda>_. 1) center ::
        ('i::finite, 'j::finite) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
  shows "integrable lborel
    (slp_mixed_center_finite_weighted_oscillatory_integrand tau
      Q left_cutoff q A right_cutoff qt B H center ::
      ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
proof -
  have identity:
    "(slp_mixed_center_finite_weighted_oscillatory_integrand tau
        Q left_cutoff q A right_cutoff qt B H center ::
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex) =
      (\<lambda>x. H center *
        slp_mixed_center_finite_weighted_oscillatory_integrand tau
          Q left_cutoff q A right_cutoff qt B (\<lambda>_. 1) center x)"
    by (rule ext)
      (simp add: slp_mixed_center_finite_weighted_oscillatory_integrand_def
        slp_parameterized_real_phase_integrand_def
        slp_mixed_center_finite_weighted_complex_amplitude_def algebra_simps)
  show ?thesis unfolding identity
    by (rule Bochner_Integration.integrable_mult_right) (rule base)
qed

theorem slp_mixed_weighted_fibers_of_ae_finite_mass:
  fixes left_type :: "'i::finite itself" and right_type :: "'j::finite itself"
    and tau :: real
    and Q left_cutoff q A right_cutoff qt B H :: slp_scalar_field
  assumes Q_measurable: "Q \<in> borel_measurable lborel"
    and left_cutoff_measurable: "left_cutoff \<in> borel_measurable lborel"
    and q_measurable: "q \<in> borel_measurable lborel"
    and A_measurable: "A \<in> borel_measurable lborel"
    and right_cutoff_measurable: "right_cutoff \<in> borel_measurable lborel"
    and qt_measurable: "qt \<in> borel_measurable lborel"
    and B_measurable: "B \<in> borel_measurable lborel"
    and H_measurable: "H \<in> borel_measurable lborel"
    and ae_mass:
      "AE center in lborel.
        slp_mixed_center_finite_weighted_absolute_fiber_mass
          TYPE('i) TYPE('j) Q left_cutoff q A right_cutoff qt B H center < top_class.top"
  shows amplitude:
    "AE center in lborel. integrable lborel
      (slp_mixed_center_finite_weighted_complex_amplitude
        Q left_cutoff q A right_cutoff qt B H center ::
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    and oscillatory:
    "AE center in lborel. integrable lborel
      (slp_mixed_center_finite_weighted_oscillatory_integrand tau
        Q left_cutoff q A right_cutoff qt B H center ::
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
proof -
  let ?amplitude =
    "slp_mixed_center_finite_weighted_complex_amplitude
      Q left_cutoff q A right_cutoff qt B H ::
      slp_point \<Rightarrow>
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex"
  have joint:
    "(\<lambda>z :: slp_point \<times>
        ('i, 'j) slp_mixed_center_finite_coordinates.
      ?amplitude (fst z) (snd z)) \<in> borel_measurable lborel"
    by (rule slp_mixed_center_finite_weighted_complex_amplitude_measurable[OF
        Q_measurable left_cutoff_measurable q_measurable A_measurable
        right_cutoff_measurable qt_measurable B_measurable H_measurable])
  have product_joint:
    "case_prod ?amplitude \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using joint by (simp only: lborel_prod split_beta')
  have section_measurable: "?amplitude center \<in> borel_measurable lborel" for center
  proof -
    have center_space: "center \<in> space (lborel :: slp_point measure)" by simp
    note raw = measurable_compose_Pair1[OF center_space product_joint]
    show ?thesis using raw by simp
  qed
  have amplitude_integrable:
    "AE center in lborel. integrable lborel (?amplitude center)"
    using ae_mass
  proof eventually_elim
    fix center
    assume finite:
      "slp_mixed_center_finite_weighted_absolute_fiber_mass
        TYPE('i) TYPE('j) Q left_cutoff q A right_cutoff qt B H center < top_class.top"
    show "integrable lborel (?amplitude center)"
      using section_measurable[of center] finite
      unfolding integrable_iff_bounded
        slp_mixed_center_finite_weighted_absolute_fiber_mass_def
      by simp
  qed
  show "AE center in lborel. integrable lborel (?amplitude center)"
    by (rule amplitude_integrable)
  show "AE center in lborel. integrable lborel
      (slp_mixed_center_finite_weighted_oscillatory_integrand tau
        Q left_cutoff q A right_cutoff qt B H center ::
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    unfolding slp_mixed_center_finite_weighted_oscillatory_integrand_def
    by (rule slp_mixed_center_finite_weighted_oscillatory_fiber_integrable[OF
        slp_mixed_center_finite_residual_measurable amplitude_integrable])
qed

theorem slp_mixed_weighted_kernel_integrable_of_global_mass:
  fixes left_type :: "'i::finite itself" and right_type :: "'j::finite itself"
    and tau :: real
    and Q left_cutoff q A right_cutoff qt B H :: slp_scalar_field
  assumes Q_measurable: "Q \<in> borel_measurable lborel"
    and left_cutoff_measurable: "left_cutoff \<in> borel_measurable lborel"
    and q_measurable: "q \<in> borel_measurable lborel"
    and A_measurable: "A \<in> borel_measurable lborel"
    and right_cutoff_measurable: "right_cutoff \<in> borel_measurable lborel"
    and qt_measurable: "qt \<in> borel_measurable lborel"
    and B_measurable: "B \<in> borel_measurable lborel"
    and H_measurable: "H \<in> borel_measurable lborel"
    and mass_integrable:
      "nn_integral lborel
        (slp_mixed_center_finite_weighted_absolute_fiber_mass
          TYPE('i) TYPE('j) Q left_cutoff q A right_cutoff qt B H) < top_class.top"
  shows "integrable lborel
    (slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) tau Q left_cutoff q A right_cutoff qt B H)"
proof -
  let ?mass = "slp_mixed_center_finite_weighted_absolute_fiber_mass
    TYPE('i) TYPE('j) Q left_cutoff q A right_cutoff qt B H"
  let ?kernel = "slp_mixed_center_finite_weighted_oscillatory_kernel
    TYPE('i) TYPE('j) tau Q left_cutoff q A right_cutoff qt B H"
  have mass_measurable: "?mass \<in> borel_measurable lborel"
    by (rule slp_mixed_center_finite_weighted_absolute_fiber_mass_measurable[OF
        Q_measurable left_cutoff_measurable q_measurable A_measurable
        right_cutoff_measurable qt_measurable B_measurable H_measurable])
  have mass_not_infinite: "nn_integral lborel ?mass \<noteq> \<infinity>"
    using mass_integrable by simp
  have ae_mass: "AE center in lborel. ?mass center < top_class.top"
    using nn_integral_PInf_AE[OF mass_measurable mass_not_infinite]
    by (simp add: less_top)
  have amplitude:
    "AE center in lborel. integrable lborel
      (slp_mixed_center_finite_weighted_complex_amplitude
        Q left_cutoff q A right_cutoff qt B H center ::
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    by (rule slp_mixed_weighted_fibers_of_ae_finite_mass(1)[OF
        Q_measurable left_cutoff_measurable q_measurable A_measurable
        right_cutoff_measurable qt_measurable B_measurable H_measurable ae_mass])
  note properties =
    slp_mixed_center_finite_weighted_oscillatory_kernel_properties[OF
      Q_measurable left_cutoff_measurable q_measurable A_measurable
      right_cutoff_measurable qt_measurable B_measurable H_measurable amplitude]
  show ?thesis
    by (rule slp_integrable_from_ennreal_mass_bound[OF
        mass_measurable mass_integrable properties(1) properties(2)])
qed

end
