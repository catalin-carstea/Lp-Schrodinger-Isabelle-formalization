theory Inverse_Schrodinger_Lp_Right_Finite_Residual_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Right_Packed_Amplitude_Transport"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_Residual_Decay"
begin

section \<open>Transported direct right residual decay on finite coordinates\<close>

theorem slp_right_branch_complex_amplitude_finite_residual_decay:
  fixes branch_dummy :: "'i::finite itself"
  assumes stationary_phase:
      "hormander_quadratic_stationary_phase_decay_claim
        TYPE(('i + 'i) \<times> bool)"
    and density:
      "evans_compact_smooth_l1_density_claim TYPE(('i + 'i) \<times> bool)"
    and root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
    and terminal_value_measurable:
      "terminal_value \<in> borel_measurable lborel"
    and output_factor_measurable:
      "output_factor \<in> borel_measurable lborel"
    and finite_amplitude_integrable:
      "integrable lborel
        (slp_right_branch_complex_amplitude_finite root_weight cutoff potential
          terminal_value output_factor ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
  shows
    "((\<lambda>omega. integral\<^sup>L lborel
      (\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
        exp (\<i> * of_real
          (omega * slp_one_sided_finite_residual coordinates)) *
        slp_right_branch_complex_amplitude_finite root_weight cutoff potential
          terminal_value output_factor coordinates))
      \<longlongrightarrow> 0) at_top"
proof -
  let ?amplitude =
    "(slp_right_branch_complex_amplitude_packed root_weight cutoff potential
      terminal_value output_factor ::
        (real^bool) \<Rightarrow>
          (real^((unit + ('i + 'i)) \<times> bool)) \<Rightarrow> complex)"
  have amplitude_integrable:
      "integrable ((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
        (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))
        (case_prod ?amplitude)"
    using slp_right_branch_complex_amplitude_packed_integrable_iff_finite[
      OF root_weight_measurable cutoff_measurable potential_measurable
        terminal_value_measurable output_factor_measurable]
      finite_amplitude_integrable
    by blast
  have packed_decay:
      "((\<lambda>omega. integral\<^sup>L
        ((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
          (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))
        (\<lambda>(root, branch). exp (\<i> * of_real
          (omega * slp_one_sided_packed_residual branch)) *
          ?amplitude root branch))
        \<longlongrightarrow> 0) at_top"
    by (rule slp_one_sided_packed_residual_passive_root_decay[
          where F = ?amplitude, OF stationary_phase density
            amplitude_integrable])
  let ?packed_integrand =
    "(\<lambda>omega (root, branch). exp (\<i> * of_real
      (omega * slp_one_sided_packed_residual branch)) *
      ?amplitude root branch)"
  let ?finite_integrand =
    "(\<lambda>omega coordinates.
      exp (\<i> * of_real
        (omega * slp_one_sided_finite_residual coordinates)) *
      slp_right_branch_complex_amplitude_finite root_weight cutoff potential
        terminal_value output_factor coordinates)"
  have integral_transport:
      "integral\<^sup>L
          (lborel :: ((real^bool) \<times>
            (real^((unit + ('i + 'i)) \<times> bool))) measure)
          (?packed_integrand omega) =
        integral\<^sup>L
          (lborel :: ('i slp_left_branch_finite_coordinates) measure)
          (?finite_integrand omega)" for omega
  proof -
    have oscillation_integrable:
        "integrable ((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
          (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))
          (?packed_integrand omega)"
      by (rule slp_one_sided_passive_root_phase_integrable[
          where F = ?amplitude and omega = omega, OF amplitude_integrable])
    have oscillation_measurable_product:
        "?packed_integrand omega \<in> borel_measurable
          ((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
            (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))"
      using oscillation_integrable by measurable
    have oscillation_measurable:
        "?packed_integrand omega \<in> borel_measurable lborel"
      using oscillation_measurable_product
      by (simp only: lborel_prod)
    have transported:
        "integral\<^sup>L lborel (?packed_integrand omega) =
          integral\<^sup>L lborel
            (\<lambda>x. ?packed_integrand omega
              (slp_one_sided_finite_to_packed_coordinates x))"
      by (rule slp_one_sided_finite_packed_integral[OF
            oscillation_measurable])
    have pullback:
        "(\<lambda>x. ?packed_integrand omega
            (slp_one_sided_finite_to_packed_coordinates x)) =
          ?finite_integrand omega"
      unfolding slp_one_sided_finite_residual_def
      by (rule ext)
        (simp only: case_prod_unfold
          slp_right_branch_complex_amplitude_packed_finite)
    have pulled_integral:
        "integral\<^sup>L
            (lborel :: ('i slp_left_branch_finite_coordinates) measure)
            (\<lambda>x. ?packed_integrand omega
              (slp_one_sided_finite_to_packed_coordinates x)) =
          integral\<^sup>L
            (lborel :: ('i slp_left_branch_finite_coordinates) measure)
            (?finite_integrand omega)"
      by (rule arg_cong[
            where f="integral\<^sup>L
              (lborel :: ('i slp_left_branch_finite_coordinates) measure)",
            OF pullback])
    show ?thesis
      by (rule HOL.trans[OF transported pulled_integral])
  qed
  have packed_decay_lborel:
      "((\<lambda>omega. integral\<^sup>L
        (lborel :: ((real^bool) \<times>
          (real^((unit + ('i + 'i)) \<times> bool))) measure)
        (?packed_integrand omega)) \<longlongrightarrow> 0) at_top"
    using packed_decay by (simp only: lborel_prod)
  have eventual_integral_transport:
      "eventually
        (\<lambda>omega.
          integral\<^sup>L
              (lborel :: ('i slp_left_branch_finite_coordinates) measure)
              (\<lambda>coordinates.
                exp (\<i> * of_real
                  (omega * slp_one_sided_finite_residual coordinates)) *
                slp_right_branch_complex_amplitude_finite root_weight cutoff
                  potential terminal_value output_factor coordinates) =
            integral\<^sup>L
              (lborel :: ((real^bool) \<times>
                (real^((unit + ('i + 'i)) \<times> bool))) measure)
              (?packed_integrand omega)) at_top"
    by (rule always_eventually, rule allI,
        rule integral_transport[symmetric])
  have target_decay_iff:
      "((\<lambda>omega. integral\<^sup>L
          (lborel :: ('i slp_left_branch_finite_coordinates) measure)
          (\<lambda>coordinates.
            exp (\<i> * of_real
              (omega * slp_one_sided_finite_residual coordinates)) *
            slp_right_branch_complex_amplitude_finite root_weight cutoff
              potential terminal_value output_factor coordinates))
          \<longlongrightarrow> 0) at_top \<longleftrightarrow>
        ((\<lambda>omega. integral\<^sup>L
          (lborel :: ((real^bool) \<times>
            (real^((unit + ('i + 'i)) \<times> bool))) measure)
          (?packed_integrand omega)) \<longlongrightarrow> 0) at_top"
    by (rule tendsto_cong[OF eventual_integral_transport])
  show ?thesis
    using packed_decay_lborel by (subst target_decay_iff)
qed

end
