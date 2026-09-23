theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Oscillatory_Integral_Uniform_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Oscillatory_Kernel"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Positive_Mass_Output_Density_Uniform_Bound"
begin

section \<open>Global finite mixed oscillatory-integral bound\<close>

context aim_planar_riesz_hls
begin

theorem slp_mixed_center_finite_oscillatory_integral_uniform_bound:
  fixes frequency B C p :: real
    and cutoff left_potential right_potential root_weight ::
      "slp_point \<Rightarrow> complex"
  assumes B_nonnegative: "0 \<le> B"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and left_potential_lp:
      "aim_complex_lp_on_plane p left_potential"
    and right_potential_lp:
      "aim_complex_lp_on_plane p right_potential"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and root_weight_integrable: "integrable lborel root_weight"
    and root_support:
      "\<And>x. root_weight x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and left_potential_support:
      "\<And>x. left_potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and right_potential_support:
      "\<And>x. right_potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
  shows
    "\<exists>(left_cap :: ennreal) (right_cap :: ennreal).
      left_cap < top_class.top \<and>
      right_cap < top_class.top \<and>
      (\<forall>root.
        nn_integral lborel
          (slp_positive_output_density (2 * B) cutoff left_potential
            (\<lambda>_. 1) CARD('i::finite) root) \<le> left_cap) \<and>
      (\<forall>root.
        nn_integral lborel
          (slp_positive_output_density (2 * B) cutoff right_potential
            (\<lambda>_. 1) CARD('j::finite) root) \<le> right_cap) \<and>
      ennreal (norm_class.norm
        (integral\<^sup>L lborel
          (slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j)
            frequency root_weight cutoff left_potential cutoff
            right_potential))) \<le>
        nn_integral lborel (\<lambda>root.
          ennreal (cmod (root_weight root))) * left_cap * right_cap"
proof -
  have root_weight_measurable[measurable]:
      "root_weight \<in> borel_measurable lborel"
    using root_weight_integrable unfolding integrable_iff_bounded by blast
  have radius_nonnegative: "0 \<le> 2 * B"
    using B_nonnegative by simp
  obtain left_cap right_cap where left_cap_finite:
      "left_cap < top_class.top"
    and right_cap_finite:
      "right_cap < top_class.top"
    and left_mass_bound:
      "\<And>root.
        nn_integral lborel
          (slp_positive_output_density (2 * B) cutoff left_potential
            (\<lambda>_. 1) CARD('i) root) \<le> left_cap"
    and right_mass_bound:
      "\<And>root.
        nn_integral lborel
          (slp_positive_output_density (2 * B) cutoff right_potential
            (\<lambda>_. 1) CARD('j) root) \<le> right_cap"
    and positive_mass_bound:
      "nn_integral lborel (\<lambda>center.
          slp_mixed_center_finite_positive_fiber_mass TYPE('i) TYPE('j)
            (2 * B) root_weight cutoff left_potential cutoff right_potential
            center) \<le>
        nn_integral lborel (\<lambda>root.
          ennreal (cmod (root_weight root))) * left_cap * right_cap"
    using
      slp_mixed_center_finite_positive_mass_output_density_uniform_bound[
        where R = "2 * B" and C = C and p = p and cutoff = cutoff
          and left_potential = left_potential
          and right_potential = right_potential
          and root_weight = root_weight and 'i = 'i and 'j = 'j,
        OF radius_nonnegative p_lower p_upper root_weight_measurable
          cutoff_measurable left_potential_lp right_potential_lp cutoff_bound
          C_nonnegative]
    by blast
  let ?kernel =
    "slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j) frequency
      root_weight cutoff left_potential cutoff right_potential"
  let ?positive_mass =
    "slp_mixed_center_finite_positive_fiber_mass TYPE('i) TYPE('j) (2 * B)
      root_weight cutoff left_potential cutoff right_potential"
  note kernel_properties =
    slp_mixed_center_finite_oscillatory_kernel_properties[
      where frequency = frequency and B = B and C = C and p = p
        and cutoff = cutoff and left_potential = left_potential
        and right_potential = right_potential and root_weight = root_weight
        and 'i = 'i and 'j = 'j,
      OF B_nonnegative p_lower p_upper cutoff_measurable left_potential_lp
        right_potential_lp cutoff_bound C_nonnegative root_weight_integrable
        root_support cutoff_support left_potential_support
        right_potential_support]
  have kernel_integrable: "integrable lborel ?kernel"
    by (rule kernel_properties(3))
  have kernel_positive_bound:
      "AE center in lborel.
        ennreal (norm_class.norm (?kernel center)) \<le> ?positive_mass center"
    by (rule kernel_properties(2))
  have integral_to_norm_mass:
      "ennreal (norm_class.norm (integral\<^sup>L lborel ?kernel)) \<le>
        nn_integral lborel (\<lambda>center.
          ennreal (norm_class.norm (?kernel center)))"
    by (rule Bochner_Integration.integral_norm_bound_ennreal[OF
          kernel_integrable])
  have norm_mass_to_positive:
      "nn_integral lborel (\<lambda>center.
          ennreal (norm_class.norm (?kernel center))) \<le>
        nn_integral lborel ?positive_mass"
    by (rule nn_integral_mono_AE[OF kernel_positive_bound])
  have oscillatory_bound:
      "ennreal (norm_class.norm (integral\<^sup>L lborel ?kernel)) \<le>
        nn_integral lborel (\<lambda>root.
          ennreal (cmod (root_weight root))) * left_cap * right_cap"
    by (rule order_trans[OF integral_to_norm_mass])
      (rule order_trans[OF norm_mass_to_positive positive_mass_bound])
  show ?thesis
    using left_cap_finite right_cap_finite left_mass_bound right_mass_bound
      oscillatory_bound
    by blast
qed

end

end
