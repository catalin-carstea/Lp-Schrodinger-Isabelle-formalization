theory Inverse_Schrodinger_Lp_Mixed_Center_Density_One_Terminal_L2
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Mixed_Center_One_Terminal_Fiber_Uniform_Power"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Positive_Ennreal_Root_Mixture_Lp"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Mixed_Center_Density_Convolution_Factorization"
begin

section \<open>One-terminal mixed center densities in L2\<close>

lemma slp_mixed_center_density_L2_from_uniform_fibers:
  fixes R :: real
    and cutoff left_potential right_potential :: "slp_point \<Rightarrow> complex"
    and left_terminal right_terminal :: "slp_point \<Rightarrow> ennreal"
    and root_weight :: "slp_point \<Rightarrow> complex"
    and left_order right_order :: nat
  assumes cutoff_measurable: "cutoff \<in> borel_measurable lborel"
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
        (\<forall>root. slp_positive_ennreal_lp_on_plane 2
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
            powr 2) \<le> K)"
  shows
    "slp_positive_ennreal_lp_on_plane 2
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
      slp_positive_ennreal_lp_on_plane 2 (?datum root)"
    and datum_power_bound: "\<forall>root. integral\<^sup>L lborel
      (\<lambda>center. enn2real (?datum root center) powr 2) \<le> K"
    using uniform_fibers by blast
  have two_lower: "1 < (2 :: real)" by simp
  have two_conjugate: "1 / (2 :: real) + 1 / 2 = 1" by simp
  have mixture_lp:
      "slp_positive_ennreal_lp_on_plane 2
        (slp_positive_ennreal_root_mixture ?weight ?datum)"
    by (rule slp_positive_ennreal_root_mixture_Lp(1)[OF
          two_lower two_lower two_conjugate weight_measurable
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

context aim_planar_riesz_hls
begin

theorem slp_mixed_center_density_one_terminal_L2:
  fixes R C p :: real
    and cutoff left_potential right_potential root_weight ::
      "slp_point \<Rightarrow> complex"
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and left_potential_lp: "aim_complex_lp_on_plane p left_potential"
    and right_potential_lp: "aim_complex_lp_on_plane p right_potential"
    and root_weight_integrable: "integrable lborel root_weight"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows left_terminal_right_unit:
    "\<And>left_order right_order.
      slp_positive_ennreal_lp_on_plane 2
        (slp_mixed_center_density R cutoff left_potential right_potential
          (slp_positive_terminal_riesz_weight R left_potential)
          (\<lambda>_. 1) left_order right_order root_weight)"
    and left_unit_right_terminal:
    "\<And>left_order right_order.
      slp_positive_ennreal_lp_on_plane 2
        (slp_mixed_center_density R cutoff left_potential right_potential
          (\<lambda>_. 1)
          (slp_positive_terminal_riesz_weight R right_potential)
          left_order right_order root_weight)"
proof -
  have left_potential_measurable:
      "left_potential \<in> borel_measurable lborel"
    using left_potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have right_potential_measurable:
      "right_potential \<in> borel_measurable lborel"
    using right_potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have left_terminal_measurable:
      "slp_positive_terminal_riesz_weight R left_potential
        \<in> borel_measurable lborel"
    by (rule slp_positive_terminal_riesz_weight_measurable[OF
          left_potential_measurable])
  have right_terminal_measurable:
      "slp_positive_terminal_riesz_weight R right_potential
        \<in> borel_measurable lborel"
    by (rule slp_positive_terminal_riesz_weight_measurable[OF
          right_potential_measurable])
  have unit_measurable:
      "(\<lambda>_ :: slp_point. (1 :: ennreal))
        \<in> borel_measurable lborel"
    by measurable
  note fibers = slp_mixed_center_one_terminal_fibers_uniform_power[OF
      radius_nonnegative p_lower p_upper cutoff_measurable left_potential_lp
      right_potential_lp cutoff_bound C_nonnegative]
  show "slp_positive_ennreal_lp_on_plane 2
      (slp_mixed_center_density R cutoff left_potential right_potential
        (slp_positive_terminal_riesz_weight R left_potential)
        (\<lambda>_. 1) left_order right_order root_weight)"
    for left_order right_order
    by (rule slp_mixed_center_density_L2_from_uniform_fibers[OF
          cutoff_measurable left_potential_measurable
          right_potential_measurable left_terminal_measurable unit_measurable
          root_weight_integrable fibers(1)])
  show "slp_positive_ennreal_lp_on_plane 2
      (slp_mixed_center_density R cutoff left_potential right_potential
        (\<lambda>_. 1)
        (slp_positive_terminal_riesz_weight R right_potential)
        left_order right_order root_weight)"
    for left_order right_order
    by (rule slp_mixed_center_density_L2_from_uniform_fibers[OF
          cutoff_measurable left_potential_measurable
          right_potential_measurable unit_measurable right_terminal_measurable
          root_weight_integrable fibers(2)])
qed

end

end
