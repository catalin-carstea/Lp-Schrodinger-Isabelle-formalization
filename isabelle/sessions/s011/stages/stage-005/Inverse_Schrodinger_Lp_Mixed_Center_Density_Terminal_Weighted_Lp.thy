theory Inverse_Schrodinger_Lp_Mixed_Center_Density_Terminal_Weighted_Lp
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Mixed_Center_Density_Fiber_Uniform_Power"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Positive_Ennreal_Root_Mixture_Lp"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Mixed_Center_Density_Convolution_Factorization"
begin

section \<open>Terminal-weighted mixed center density in Lp\<close>

context aim_planar_riesz_hls
begin

theorem slp_mixed_center_density_terminal_weighted_Lp:
  fixes R C p :: real
    and cutoff left_potential right_potential root_weight ::
      "slp_point \<Rightarrow> complex"
    and left_order right_order :: nat
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and left_potential_lp: "aim_complex_lp_on_plane p left_potential"
    and right_potential_lp: "aim_complex_lp_on_plane p right_potential"
    and root_weight_integrable: "integrable lborel root_weight"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows mixed_lp:
    "slp_positive_ennreal_lp_on_plane (slp_branch_power_exponent p)
      (slp_mixed_center_density R cutoff left_potential right_potential
        (slp_positive_terminal_riesz_weight R left_potential)
        (slp_positive_terminal_riesz_weight R right_potential)
        left_order right_order root_weight)"
    and mixed_power_bound:
    "\<exists>K. 0 \<le> K \<and>
      integral\<^sup>L lborel
          (\<lambda>center.
            enn2real
              (slp_mixed_center_density R cutoff left_potential
                right_potential
                (slp_positive_terminal_riesz_weight R left_potential)
                (slp_positive_terminal_riesz_weight R right_potential)
                left_order right_order root_weight center)
              powr slp_branch_power_exponent p)
        \<le> (integral\<^sup>L lborel
              (\<lambda>root. Real_Vector_Spaces.norm (root_weight root)))
            powr (slp_branch_power_exponent p /
              slp_branch_holder_exponent p) *
          (K * integral\<^sup>L lborel
            (\<lambda>root. Real_Vector_Spaces.norm (root_weight root)))"
proof -
  let ?a = "slp_branch_power_exponent p"
  let ?b = "slp_branch_holder_exponent p"
  let ?left_terminal =
    "slp_positive_terminal_riesz_weight R left_potential"
  let ?right_terminal =
    "slp_positive_terminal_riesz_weight R right_potential"
  let ?weight =
    "\<lambda>root. Real_Vector_Spaces.norm (root_weight root)"
  let ?datum =
    "\<lambda>root center.
      slp_positive_ennreal_convolution
        (slp_left_positive_output_density R cutoff left_potential
          ?left_terminal left_order root)
        (\<lambda>offset.
          slp_right_positive_output_density R cutoff right_potential
            ?right_terminal right_order root (root + offset))
        center"
  let ?mixed =
    "slp_mixed_center_density R cutoff left_potential right_potential
      ?left_terminal ?right_terminal left_order right_order root_weight"
  note exponents = slp_branch_weighted_exponents[OF p_lower p_upper]
  have left_potential_measurable[measurable]:
      "left_potential \<in> borel_measurable lborel"
    using left_potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have right_potential_measurable[measurable]:
      "right_potential \<in> borel_measurable lborel"
    using right_potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have root_weight_measurable[measurable]:
      "root_weight \<in> borel_measurable lborel"
    using root_weight_integrable by measurable
  have left_terminal_measurable[measurable]:
      "?left_terminal \<in> borel_measurable lborel"
    by (rule slp_positive_terminal_riesz_weight_measurable[OF
          left_potential_measurable])
  have right_terminal_measurable[measurable]:
      "?right_terminal \<in> borel_measurable lborel"
    by (rule slp_positive_terminal_riesz_weight_measurable[OF
          right_potential_measurable])
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
  have weight_measurable:
      "?weight \<in> borel_measurable lborel"
    by measurable
  have weight_nonnegative: "0 \<le> ?weight root" for root
    by simp
  have weight_integrable: "integrable lborel ?weight"
    by (rule integrable_norm[OF root_weight_integrable])
  obtain K where K_nonnegative: "0 \<le> K"
    and datum_lp: "\<forall>root.
      slp_positive_ennreal_lp_on_plane ?a (?datum root)"
    and datum_power_bound: "\<forall>root. integral\<^sup>L lborel
      (\<lambda>center. enn2real (?datum root center) powr ?a) \<le> K"
    using slp_mixed_center_density_fiber_uniform_power[OF
      radius_nonnegative p_lower p_upper cutoff_measurable left_potential_lp
      right_potential_lp cutoff_bound C_nonnegative]
    by blast
  have datum_lp_each:
      "\<And>root. slp_positive_ennreal_lp_on_plane ?a (?datum root)"
    using datum_lp by blast
  have datum_power_bound_each:
      "\<And>root. integral\<^sup>L lborel
        (\<lambda>center. enn2real (?datum root center) powr ?a) \<le> K"
    using datum_power_bound by blast
  have mixture_lp:
      "slp_positive_ennreal_lp_on_plane ?a
        (slp_positive_ennreal_root_mixture ?weight ?datum)"
    by (rule slp_positive_ennreal_root_mixture_Lp(1)[OF
          exponents(1) exponents(3) exponents(4) weight_measurable
          datum_joint_measurable weight_nonnegative weight_integrable
          datum_lp_each datum_power_bound_each K_nonnegative])
  have mixture_power:
      "integral\<^sup>L lborel
          (\<lambda>center.
            enn2real
              (slp_positive_ennreal_root_mixture ?weight ?datum center)
              powr ?a)
        \<le> (integral\<^sup>L lborel ?weight) powr (?a / ?b) *
          (K * integral\<^sup>L lborel ?weight)"
    by (rule slp_positive_ennreal_root_mixture_Lp(2)[OF
          exponents(1) exponents(3) exponents(4) weight_measurable
          datum_joint_measurable weight_nonnegative weight_integrable
          datum_lp_each datum_power_bound_each K_nonnegative])
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
  show "slp_positive_ennreal_lp_on_plane ?a ?mixed"
    using mixture_lp by (simp only: mixed_identity)
  show "\<exists>K. 0 \<le> K \<and>
      integral\<^sup>L lborel
          (\<lambda>center. enn2real (?mixed center) powr ?a) \<le>
        (integral\<^sup>L lborel ?weight) powr (?a / ?b) *
          (K * integral\<^sup>L lborel ?weight)"
    using K_nonnegative mixture_power
    by (simp only: mixed_identity; blast)
qed

end

end
