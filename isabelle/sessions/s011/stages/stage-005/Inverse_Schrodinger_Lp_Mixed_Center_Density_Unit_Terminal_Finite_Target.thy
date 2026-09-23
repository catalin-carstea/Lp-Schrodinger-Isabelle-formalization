theory Inverse_Schrodinger_Lp_Mixed_Center_Density_Unit_Terminal_Finite_Target
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Mixed_Center_Density_Finite_Target_From_Uniform_Fibers"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Mixed_Center_Unit_Terminal_Fiber_Finite_Target"
begin

section \<open>Official unweighted mixed center densities at finite targets\<close>

context aim_planar_riesz_hls
begin

theorem slp_mixed_center_density_unit_terminal_finite_target:
  fixes R C p t :: real
    and cutoff left_potential right_potential root_weight ::
      "slp_point \<Rightarrow> complex"
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and t_lower: "1 < t"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and left_potential_lp: "aim_complex_lp_on_plane p left_potential"
    and right_potential_lp: "aim_complex_lp_on_plane p right_potential"
    and root_weight_integrable: "integrable lborel root_weight"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "\<And>left_order right_order.
      slp_positive_ennreal_lp_on_plane t
        (slp_mixed_center_density R cutoff left_potential right_potential
          (\<lambda>_. 1) (\<lambda>_. 1)
          left_order right_order root_weight)"
proof -
  have left_potential_measurable:
      "left_potential \<in> borel_measurable lborel"
    using left_potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have right_potential_measurable:
      "right_potential \<in> borel_measurable lborel"
    using right_potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have unit_measurable:
      "(\<lambda>_ :: slp_point. (1 :: ennreal))
        \<in> borel_measurable lborel"
    by measurable
  show "slp_positive_ennreal_lp_on_plane t
      (slp_mixed_center_density R cutoff left_potential right_potential
        (\<lambda>_. 1) (\<lambda>_. 1)
        left_order right_order root_weight)"
    for left_order right_order
  proof -
    have uniform_fibers:
        "\<exists>K. 0 \<le> K \<and>
          (\<forall>root. slp_positive_ennreal_lp_on_plane t
            (slp_positive_ennreal_convolution
              (slp_left_positive_output_density R cutoff left_potential
                (\<lambda>_. 1) left_order root)
              (\<lambda>offset.
                slp_right_positive_output_density R cutoff right_potential
                  (\<lambda>_. 1) right_order root (root + offset)))) \<and>
          (\<forall>root. integral\<^sup>L lborel
            (\<lambda>center. enn2real
              (slp_positive_ennreal_convolution
                (slp_left_positive_output_density R cutoff left_potential
                  (\<lambda>_. 1) left_order root)
                (\<lambda>offset.
                  slp_right_positive_output_density R cutoff right_potential
                    (\<lambda>_. 1) right_order root (root + offset)) center)
              powr t) \<le> K)"
      by (rule slp_mixed_center_unit_terminal_fibers_finite_target[OF
            radius_nonnegative p_lower p_upper t_lower cutoff_measurable
            left_potential_lp right_potential_lp cutoff_bound C_nonnegative])
    show ?thesis
      by (rule slp_mixed_center_density_Lt_from_uniform_fibers[OF
            t_lower cutoff_measurable left_potential_measurable
            right_potential_measurable unit_measurable unit_measurable
            root_weight_integrable uniform_fibers])
  qed
qed

end

end
