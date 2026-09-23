theory Inverse_Schrodinger_Lp_Mixed_Center_Density_Finite_Target_From_Uniform_Fibers
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Positive_Ennreal_Root_Mixture_Lp"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Mixed_Center_Density_Convolution_Factorization"
begin

section \<open>Finite-target mixed center densities from uniform fibers\<close>

lemma slp_mixed_center_density_Lt_from_uniform_fibers:
  fixes R t :: real
    and cutoff left_potential right_potential :: "slp_point \<Rightarrow> complex"
    and left_terminal right_terminal :: "slp_point \<Rightarrow> ennreal"
    and root_weight :: "slp_point \<Rightarrow> complex"
    and left_order right_order :: nat
  assumes t_lower: "1 < t"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and left_potential_measurable:
      "left_potential \<in> borel_measurable lborel"
    and right_potential_measurable:
      "right_potential \<in> borel_measurable lborel"
    and left_terminal_measurable:
      "left_terminal \<in> borel_measurable lborel"
    and right_terminal_measurable:
      "right_terminal \<in> borel_measurable lborel"
    and root_weight_integrable: "integrable lborel root_weight"
    and uniform_fibers:
      "\<exists>K. 0 \<le> K \<and>
        (\<forall>root. slp_positive_ennreal_lp_on_plane t
          (slp_positive_ennreal_convolution
            (slp_left_positive_output_density R cutoff left_potential
              left_terminal left_order root)
            (\<lambda>offset.
              slp_right_positive_output_density R cutoff right_potential
                right_terminal right_order root (root + offset)))) \<and>
        (\<forall>root. integral\<^sup>L lborel
          (\<lambda>center. enn2real
            (slp_positive_ennreal_convolution
              (slp_left_positive_output_density R cutoff left_potential
                left_terminal left_order root)
              (\<lambda>offset.
                slp_right_positive_output_density R cutoff right_potential
                  right_terminal right_order root (root + offset)) center)
            powr t) \<le> K)"
  shows
    "slp_positive_ennreal_lp_on_plane t
      (slp_mixed_center_density R cutoff left_potential right_potential
        left_terminal right_terminal left_order right_order root_weight)"
proof -
  let ?weight =
    "\<lambda>root. Real_Vector_Spaces.norm (root_weight root)"
  let ?datum =
    "\<lambda>root center.
      slp_positive_ennreal_convolution
        (slp_left_positive_output_density R cutoff left_potential
          left_terminal left_order root)
        (\<lambda>offset.
          slp_right_positive_output_density R cutoff right_potential
            right_terminal right_order root (root + offset)) center"
  let ?mixed =
    "slp_mixed_center_density R cutoff left_potential right_potential
      left_terminal right_terminal left_order right_order root_weight"
  note left_density_joint[measurable] =
    slp_left_positive_output_density_joint_measurable[OF
      cutoff_measurable left_potential_measurable left_terminal_measurable]
  note right_density_joint[measurable] =
    slp_right_positive_output_density_joint_measurable[OF
      cutoff_measurable right_potential_measurable right_terminal_measurable]
  have datum_joint_measurable:
      "case_prod ?datum
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    unfolding slp_positive_ennreal_convolution_def by measurable
  have weight_measurable: "?weight \<in> borel_measurable lborel"
    using root_weight_integrable by measurable
  have weight_nonnegative: "0 \<le> ?weight root" for root by simp
  have weight_integrable: "integrable lborel ?weight"
    by (rule integrable_norm[OF root_weight_integrable])
  obtain K where K_nonnegative: "0 \<le> K"
    and datum_lp: "\<forall>root.
      slp_positive_ennreal_lp_on_plane t (?datum root)"
    and datum_power_bound: "\<forall>root. integral\<^sup>L lborel
      (\<lambda>center. enn2real (?datum root center) powr t) \<le> K"
    using uniform_fibers by blast
  let ?h = "t / (t - 1)"
  have t_positive: "0 < t" using t_lower by linarith
  have t_minus_one_positive: "0 < t - 1" using t_lower by linarith
  have t_nonzero: "t \<noteq> 0" using t_positive by simp
  have t_minus_one_nonzero: "t - 1 \<noteq> 0"
    using t_minus_one_positive by simp
  have h_lower: "1 < ?h"
    using t_minus_one_positive by (simp add: less_divide_eq)
  have h_conjugate: "1 / t + 1 / ?h = 1"
  proof -
    have inverse_h: "1 / ?h = (t - 1) / t"
      using t_nonzero t_minus_one_nonzero by simp
    have common: "1 / t + (t - 1) / t = (1 + (t - 1)) / t"
      by (rule add_divide_distrib [symmetric])
    show ?thesis
      using inverse_h common t_nonzero by simp
  qed
  have mixture_lp:
      "slp_positive_ennreal_lp_on_plane t
        (slp_positive_ennreal_root_mixture ?weight ?datum)"
    by (rule slp_positive_ennreal_root_mixture_Lp(1)[OF
          t_lower h_lower h_conjugate weight_measurable
          datum_joint_measurable weight_nonnegative weight_integrable
          datum_lp[rule_format] datum_power_bound[rule_format]
          K_nonnegative])
  have mixed_identity:
      "?mixed = slp_positive_ennreal_root_mixture ?weight ?datum"
  proof (rule ext)
    fix center :: slp_point
    show "?mixed center =
        slp_positive_ennreal_root_mixture ?weight ?datum center"
      unfolding slp_positive_ennreal_root_mixture_def
      by (rule slp_mixed_center_density_convolution_factorization[OF
            cutoff_measurable left_potential_measurable
            right_potential_measurable left_terminal_measurable
            right_terminal_measurable])
  qed
  show ?thesis using mixture_lp by (simp only: mixed_identity)
qed

end
