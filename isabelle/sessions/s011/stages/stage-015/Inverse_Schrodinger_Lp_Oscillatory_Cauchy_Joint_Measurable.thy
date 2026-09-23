theory Inverse_Schrodinger_Lp_Oscillatory_Cauchy_Joint_Measurable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Oscillatory_Cauchy"
begin

section \<open>Jointly measurable center-dependent Cauchy transforms\<close>

theorem slp_cauchy_kernel_joint_measurable:
  "(\<lambda>pair :: slp_point \<times> slp_point.
      slp_cauchy_kernel orientation (fst pair) (snd pair)) \<in>
    borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
proof -
  have first_measurable[measurable]:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_point_as_complex (fst pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using slp_point_as_complex_borel_measurable by measurable
  have second_measurable[measurable]:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_point_as_complex (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using slp_point_as_complex_borel_measurable by measurable
  have difference_measurable:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_point_as_complex (fst pair) -
            slp_point_as_complex (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by measurable
  have conjugate_measurable:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          cnj (slp_point_as_complex (fst pair) -
            slp_point_as_complex (snd pair))) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule borel_measurable_continuous_on[OF
          continuous_on_cnj[OF continuous_on_id] difference_measurable])
  show ?thesis
  proof (cases orientation)
    case SLP_Partial_Inverse
    show ?thesis
      unfolding slp_cauchy_kernel_def slp_cauchy_denominator_def
        SLP_Partial_Inverse
      using conjugate_measurable
      by (simp only: slp_cauchy_orientation.case
          borel_measurable_inverse)
  next
    case SLP_Dbar_Inverse
    show ?thesis
      unfolding slp_cauchy_kernel_def slp_cauchy_denominator_def
        SLP_Dbar_Inverse
      using difference_measurable
      by (simp only: slp_cauchy_orientation.case
          borel_measurable_inverse)
  qed
qed

theorem slp_cauchy_transform_joint_measurable:
  fixes field :: "slp_point \<Rightarrow> slp_scalar_field"
  assumes field_measurable:
    "(\<lambda>pair :: slp_point \<times> slp_point.
        field (fst pair) (snd pair)) \<in>
      borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
  shows
    "(\<lambda>pair :: slp_point \<times> slp_point.
        slp_cauchy_transform orientation (field (fst pair)) (snd pair)) \<in>
      borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
proof -
  have field_pair_measurable:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          field (fst pair) (snd pair)) \<in>
        borel_measurable lborel"
    using field_measurable by (simp only: lborel_prod)
  have field_borel_measurable:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          field (fst pair) (snd pair)) \<in>
        borel_measurable borel"
    using field_pair_measurable
    by (simp only: measurable_lborel1 measurable_lborel2)
  have kernel_pair_measurable:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_cauchy_kernel orientation (fst pair) (snd pair)) \<in>
        borel_measurable lborel"
    using slp_cauchy_kernel_joint_measurable[of orientation]
    by (simp only: lborel_prod)
  have kernel_borel_measurable:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_cauchy_kernel orientation (fst pair) (snd pair)) \<in>
        borel_measurable borel"
    using kernel_pair_measurable
    by (simp only: measurable_lborel1 measurable_lborel2)
  have field_lift_product:
      "(\<lambda>pair :: (slp_point \<times> slp_point) \<times> slp_point.
          field (fst (fst pair)) (snd pair)) \<in>
        borel_measurable
          ((lborel \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M lborel)"
  proof -
    have regroup_measurable:
        "(\<lambda>pair :: (slp_point \<times> slp_point) \<times> slp_point.
            (fst (fst pair), snd pair)) \<in>
          borel_measurable borel"
      by (rule borel_measurable_continuous_onI)
        (intro continuous_intros)
    have composed:
        "(\<lambda>pair :: (slp_point \<times> slp_point) \<times> slp_point.
            field (fst (fst pair)) (snd pair)) \<in>
          borel_measurable borel"
      using measurable_comp[OF regroup_measurable field_borel_measurable]
      by (simp only: comp_def fst_conv snd_conv)
    have composed_lborel:
        "(\<lambda>pair :: (slp_point \<times> slp_point) \<times> slp_point.
            field (fst (fst pair)) (snd pair)) \<in>
          borel_measurable lborel"
      using composed
      by (simp only: measurable_cong_sets[OF sets_lborel refl])
    show ?thesis
      using composed_lborel by (simp only: lborel_prod)
  qed
  have field_lift_measurable[measurable]:
      "(\<lambda>pair :: (slp_point \<times> slp_point) \<times> slp_point.
          field (fst (fst pair)) (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using field_lift_product by (simp only: lborel_prod)
  have kernel_lift_product:
      "(\<lambda>pair :: (slp_point \<times> slp_point) \<times> slp_point.
          slp_cauchy_kernel orientation (snd (fst pair)) (snd pair)) \<in>
        borel_measurable
          ((lborel \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M lborel)"
  proof -
    have regroup_measurable:
        "(\<lambda>pair :: (slp_point \<times> slp_point) \<times> slp_point.
            (snd (fst pair), snd pair)) \<in>
          borel_measurable borel"
      by (rule borel_measurable_continuous_onI)
        (intro continuous_intros)
    have composed:
        "(\<lambda>pair :: (slp_point \<times> slp_point) \<times> slp_point.
            slp_cauchy_kernel orientation (snd (fst pair)) (snd pair)) \<in>
          borel_measurable borel"
      using measurable_comp[OF regroup_measurable kernel_borel_measurable]
      by (simp only: comp_def fst_conv snd_conv)
    have composed_lborel:
        "(\<lambda>pair :: (slp_point \<times> slp_point) \<times> slp_point.
            slp_cauchy_kernel orientation (snd (fst pair)) (snd pair)) \<in>
          borel_measurable lborel"
      using composed
      by (simp only: measurable_cong_sets[OF sets_lborel refl])
    show ?thesis
      using composed_lborel by (simp only: lborel_prod)
  qed
  have kernel_lift_measurable[measurable]:
      "(\<lambda>pair :: (slp_point \<times> slp_point) \<times> slp_point.
          slp_cauchy_kernel orientation (snd (fst pair)) (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using kernel_lift_product by (simp only: lborel_prod)
  have integrand_joint_measurable:
      "(\<lambda>pair :: (slp_point \<times> slp_point) \<times> slp_point.
          field (fst (fst pair)) (snd pair) *
            slp_cauchy_kernel orientation (snd (fst pair)) (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by measurable
  have parameter_integral_measurable:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          integral\<^sup>L lborel (\<lambda>y.
            field (fst pair) y *
              slp_cauchy_kernel orientation (snd pair) y)) \<in>
        borel_measurable lborel"
    by (rule lborel.borel_measurable_lebesgue_integral[
          where f="\<lambda>pair y.
            field (fst pair) y *
              slp_cauchy_kernel orientation (snd pair) y"])
      (use integrand_joint_measurable in simp)
  have scaled_measurable:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          inverse (of_real pi) *
            integral\<^sup>L lborel (\<lambda>y.
              field (fst pair) y *
                slp_cauchy_kernel orientation (snd pair) y)) \<in>
        borel_measurable lborel"
    using parameter_integral_measurable by measurable
  show ?thesis
    unfolding slp_cauchy_transform_def slp_cauchy_integrand_def
    using scaled_measurable by (simp only: lborel_prod)
qed

theorem slp_oscillatory_modulation_joint_measurable:
  fixes field :: "slp_point \<Rightarrow> slp_scalar_field"
  assumes field_measurable:
    "(\<lambda>pair :: slp_point \<times> slp_point.
        field (fst pair) (snd pair)) \<in>
      borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
  shows
    "(\<lambda>pair :: slp_point \<times> slp_point.
        slp_oscillatory_modulation tau (fst pair)
          (field (fst pair)) (snd pair)) \<in>
      borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
proof -
  have field_pair_measurable:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          field (fst pair) (snd pair)) \<in>
        borel_measurable lborel"
    using field_measurable by (simp only: lborel_prod)
  have phase_pair_measurable:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_center_phase (fst pair) (snd pair)) \<in>
        borel_measurable lborel"
  proof -
    show ?thesis
      apply (simp only: measurable_lborel2)
      unfolding slp_center_phase_def
      by (rule borel_measurable_continuous_onI)
        (intro continuous_intros)
  qed
  have kernel_pair_measurable:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_center_kernel tau (fst pair) (snd pair)) \<in>
        borel_measurable lborel"
    unfolding slp_center_kernel_def
    using phase_pair_measurable by measurable
  have modulation_pair_measurable:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_center_kernel tau (fst pair) (snd pair) *
            field (fst pair) (snd pair)) \<in>
        borel_measurable lborel"
    using kernel_pair_measurable field_pair_measurable by measurable
  show ?thesis
    unfolding slp_oscillatory_modulation_def
    using modulation_pair_measurable by (simp only: lborel_prod)
qed

theorem slp_oscillatory_cauchy_inverses_joint_measurable:
  fixes field :: "slp_point \<Rightarrow> slp_scalar_field"
  assumes field_measurable:
    "(\<lambda>pair :: slp_point \<times> slp_point.
        field (fst pair) (snd pair)) \<in>
      borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
  shows
    "(\<lambda>pair :: slp_point \<times> slp_point.
        slp_partial_psi_inverse tau (fst pair)
          (field (fst pair)) (snd pair)) \<in>
      borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    "(\<lambda>pair :: slp_point \<times> slp_point.
        slp_dbar_psi_inverse tau (fst pair)
          (field (fst pair)) (snd pair)) \<in>
      borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
proof -
  have partial_modulation:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_oscillatory_modulation tau (fst pair)
            (field (fst pair)) (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_oscillatory_modulation_joint_measurable[OF
          field_measurable])
  have dbar_modulation:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_oscillatory_modulation (- tau) (fst pair)
            (field (fst pair)) (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_oscillatory_modulation_joint_measurable[OF
          field_measurable])
  show
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_partial_psi_inverse tau (fst pair)
            (field (fst pair)) (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    unfolding slp_partial_psi_inverse_def
    by (rule slp_cauchy_transform_joint_measurable[OF
          partial_modulation])
  show
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_dbar_psi_inverse tau (fst pair)
            (field (fst pair)) (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    unfolding slp_dbar_psi_inverse_def
    by (rule slp_cauchy_transform_joint_measurable[OF
          dbar_modulation])
qed

end
