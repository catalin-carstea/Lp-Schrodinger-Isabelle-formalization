theory Inverse_Schrodinger_Lp_Mixed_Center_Density_Fiber_Uniform_Power
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Output_Density_All_Order_Terminal_Weighted_Mass_Power"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Mixed_Center_Density_Fiber_Endpoint"
begin

section \<open>Root-uniform power bound for each mixed convolution fiber\<close>

context aim_planar_riesz_hls
begin

theorem slp_mixed_center_density_fiber_uniform_power:
  fixes R C p :: real
    and cutoff left_potential right_potential :: "slp_point \<Rightarrow> complex"
    and left_order right_order :: nat
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and left_potential_lp: "aim_complex_lp_on_plane p left_potential"
    and right_potential_lp: "aim_complex_lp_on_plane p right_potential"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows "\<exists>K. 0 \<le> K \<and>
      (\<forall>root. slp_positive_ennreal_lp_on_plane
        (slp_branch_power_exponent p)
        (slp_positive_ennreal_convolution
          (slp_left_positive_output_density R cutoff left_potential
            (slp_positive_terminal_riesz_weight R left_potential)
            left_order root)
          (\<lambda>offset.
            slp_right_positive_output_density R cutoff right_potential
              (slp_positive_terminal_riesz_weight R right_potential)
              right_order root (root + offset)))) \<and>
      (\<forall>root. integral\<^sup>L lborel
          (\<lambda>center.
            enn2real
              (slp_positive_ennreal_convolution
                (slp_left_positive_output_density R cutoff left_potential
                  (slp_positive_terminal_riesz_weight R left_potential)
                  left_order root)
                (\<lambda>offset.
                  slp_right_positive_output_density R cutoff right_potential
                    (slp_positive_terminal_riesz_weight R right_potential)
                    right_order root (root + offset))
                center) powr slp_branch_power_exponent p) \<le> K)"
proof -
  note left_mass_result =
    slp_left_right_positive_output_density_all_orders_terminal_weighted_mass_power[OF
      radius_nonnegative p_lower p_upper cutoff_measurable left_potential_lp
      cutoff_bound C_nonnegative]
  obtain M where M_nonnegative: "0 \<le> M"
    and left_mass_power:
      "\<forall>root.
        enn2real
          (\<integral>\<^sup>+ output.
            slp_left_positive_output_density R cutoff left_potential
              (slp_positive_terminal_riesz_weight R left_potential)
              left_order root output
            \<partial>lborel) powr slp_branch_power_exponent p \<le> M"
    using left_mass_result(1)[of left_order] by blast
  note right_result =
    slp_left_right_positive_output_density_all_orders_terminal_weighted[OF
      radius_nonnegative p_lower p_upper cutoff_measurable right_potential_lp
      cutoff_bound C_nonnegative]
  obtain L where L_nonnegative: "0 \<le> L"
    and right_power:
      "\<forall>root. integral\<^sup>L lborel
        (\<lambda>output.
          enn2real
            (slp_right_positive_output_density R cutoff right_potential
              (slp_positive_terminal_riesz_weight R right_potential)
              right_order root output) powr slp_branch_power_exponent p) \<le> L"
    using right_result(3)[of right_order] by blast
  let ?K = "M * L"
  have K_nonnegative: "0 \<le> ?K"
    using M_nonnegative L_nonnegative by simp
  have all_fiber_lp:
      "\<forall>root. slp_positive_ennreal_lp_on_plane
        (slp_branch_power_exponent p)
        (slp_positive_ennreal_convolution
          (slp_left_positive_output_density R cutoff left_potential
            (slp_positive_terminal_riesz_weight R left_potential)
            left_order root)
          (\<lambda>offset.
            slp_right_positive_output_density R cutoff right_potential
              (slp_positive_terminal_riesz_weight R right_potential)
              right_order root (root + offset)))"
  proof
    fix root :: slp_point
    show "slp_positive_ennreal_lp_on_plane
        (slp_branch_power_exponent p)
        (slp_positive_ennreal_convolution
          (slp_left_positive_output_density R cutoff left_potential
            (slp_positive_terminal_riesz_weight R left_potential)
            left_order root)
          (\<lambda>offset.
            slp_right_positive_output_density R cutoff right_potential
              (slp_positive_terminal_riesz_weight R right_potential)
              right_order root (root + offset)))"
      by (rule slp_mixed_center_density_fiber_endpoint(1)[OF
            radius_nonnegative p_lower p_upper cutoff_measurable
            left_potential_lp right_potential_lp cutoff_bound C_nonnegative])
  qed
  have all_fiber_power:
      "\<forall>root. integral\<^sup>L lborel
        (\<lambda>center.
          enn2real
            (slp_positive_ennreal_convolution
              (slp_left_positive_output_density R cutoff left_potential
                (slp_positive_terminal_riesz_weight R left_potential)
                left_order root)
              (\<lambda>offset.
                slp_right_positive_output_density R cutoff right_potential
                  (slp_positive_terminal_riesz_weight R right_potential)
                  right_order root (root + offset))
              center) powr slp_branch_power_exponent p) \<le> ?K"
  proof
    fix root :: slp_point
    let ?left_mass_power =
      "enn2real
        (\<integral>\<^sup>+ output.
          slp_left_positive_output_density R cutoff left_potential
            (slp_positive_terminal_riesz_weight R left_potential)
            left_order root output
          \<partial>lborel) powr slp_branch_power_exponent p"
    let ?right_power =
      "integral\<^sup>L lborel
        (\<lambda>output.
          enn2real
            (slp_right_positive_output_density R cutoff right_potential
              (slp_positive_terminal_riesz_weight R right_potential)
              right_order root output) powr slp_branch_power_exponent p)"
    have endpoint:
        "integral\<^sup>L lborel
            (\<lambda>center.
              enn2real
                (slp_positive_ennreal_convolution
                  (slp_left_positive_output_density R cutoff left_potential
                    (slp_positive_terminal_riesz_weight R left_potential)
                    left_order root)
                  (\<lambda>offset.
                    slp_right_positive_output_density R cutoff right_potential
                      (slp_positive_terminal_riesz_weight R right_potential)
                      right_order root (root + offset))
                  center) powr slp_branch_power_exponent p)
          \<le> ?left_mass_power * ?right_power"
      by (rule slp_mixed_center_density_fiber_endpoint(2)[OF
            radius_nonnegative p_lower p_upper cutoff_measurable
            left_potential_lp right_potential_lp cutoff_bound C_nonnegative])
    have left_nonnegative: "0 \<le> ?left_mass_power"
      by simp
    have right_nonnegative: "0 \<le> ?right_power"
      by (rule integral_nonneg_AE) simp
    have left_bound: "?left_mass_power \<le> M"
      using left_mass_power by blast
    have right_bound: "?right_power \<le> L"
      using right_power by blast
    have product_bound: "?left_mass_power * ?right_power \<le> M * L"
      by (rule mult_mono[OF left_bound right_bound])
        (use left_nonnegative M_nonnegative in simp_all)
    show "integral\<^sup>L lborel
        (\<lambda>center.
          enn2real
            (slp_positive_ennreal_convolution
              (slp_left_positive_output_density R cutoff left_potential
                (slp_positive_terminal_riesz_weight R left_potential)
                left_order root)
              (\<lambda>offset.
                slp_right_positive_output_density R cutoff right_potential
                  (slp_positive_terminal_riesz_weight R right_potential)
                  right_order root (root + offset))
              center) powr slp_branch_power_exponent p) \<le> ?K"
      using endpoint product_bound by linarith
  qed
  show ?thesis
    using K_nonnegative all_fiber_lp all_fiber_power by blast
qed

end

end
