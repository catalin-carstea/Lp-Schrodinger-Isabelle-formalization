theory Inverse_Schrodinger_Lp_Mixed_Center_Density_Fiber_Endpoint
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Output_Density_All_Order_Terminal_Weighted_L1"
begin

section \<open>Endpoint Young bound for each mixed root fiber\<close>

context aim_planar_riesz_hls
begin

theorem slp_mixed_center_density_fiber_endpoint:
  fixes R C p :: real
    and cutoff left_potential right_potential :: "slp_point \<Rightarrow> complex"
    and left_order right_order :: nat
    and root :: slp_point
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and left_potential_lp: "aim_complex_lp_on_plane p left_potential"
    and right_potential_lp: "aim_complex_lp_on_plane p right_potential"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows fiber_lp:
    "slp_positive_ennreal_lp_on_plane (slp_branch_power_exponent p)
      (slp_positive_ennreal_convolution
        (slp_left_positive_output_density R cutoff left_potential
          (slp_positive_terminal_riesz_weight R left_potential)
          left_order root)
        (\<lambda>offset.
          slp_right_positive_output_density R cutoff right_potential
            (slp_positive_terminal_riesz_weight R right_potential)
            right_order root (root + offset)))"
    and fiber_power_bound:
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
      \<le> enn2real
          (\<integral>\<^sup>+ output.
            slp_left_positive_output_density R cutoff left_potential
              (slp_positive_terminal_riesz_weight R left_potential)
              left_order root output
            \<partial>lborel) powr slp_branch_power_exponent p *
        integral\<^sup>L lborel
          (\<lambda>output.
            enn2real
              (slp_right_positive_output_density R cutoff right_potential
                (slp_positive_terminal_riesz_weight R right_potential)
                right_order root output) powr slp_branch_power_exponent p)"
proof -
  note exponents = slp_branch_weighted_exponents[OF p_lower p_upper]
  note left_result =
    slp_left_right_positive_output_density_all_orders_terminal_weighted_L1[OF
      radius_nonnegative p_lower p_upper cutoff_measurable left_potential_lp
      cutoff_bound C_nonnegative]
  have left_density_L1:
      "slp_positive_ennreal_lp_on_plane 1
        (slp_left_positive_output_density R cutoff left_potential
          (slp_positive_terminal_riesz_weight R left_potential)
          left_order root)"
    by (rule left_result(2))
  note right_result =
    slp_left_right_positive_output_density_all_orders_terminal_weighted[OF
      radius_nonnegative p_lower p_upper cutoff_measurable right_potential_lp
      cutoff_bound C_nonnegative]
  obtain L where right_density_lp_all:
      "\<forall>origin. slp_positive_ennreal_lp_on_plane
        (slp_branch_power_exponent p)
        (slp_right_positive_output_density R cutoff right_potential
          (slp_positive_terminal_riesz_weight R right_potential)
          right_order origin)"
    using right_result(3)[of right_order] by blast
  have right_density_lp:
      "slp_positive_ennreal_lp_on_plane (slp_branch_power_exponent p)
        (slp_right_positive_output_density R cutoff right_potential
          (slp_positive_terminal_riesz_weight R right_potential)
          right_order root)"
    using right_density_lp_all by blast
  note endpoint = slp_positive_ennreal_convolution_shifted_L1_Lp[OF
      exponents(1) exponents(3) exponents(4) left_density_L1
      right_density_lp, where shift=root]
  show
    "slp_positive_ennreal_lp_on_plane (slp_branch_power_exponent p)
      (slp_positive_ennreal_convolution
        (slp_left_positive_output_density R cutoff left_potential
          (slp_positive_terminal_riesz_weight R left_potential)
          left_order root)
        (\<lambda>offset.
          slp_right_positive_output_density R cutoff right_potential
            (slp_positive_terminal_riesz_weight R right_potential)
            right_order root (root + offset)))"
    by (rule endpoint(1))
  show
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
      \<le> enn2real
          (\<integral>\<^sup>+ output.
            slp_left_positive_output_density R cutoff left_potential
              (slp_positive_terminal_riesz_weight R left_potential)
              left_order root output
            \<partial>lborel) powr slp_branch_power_exponent p *
        integral\<^sup>L lborel
          (\<lambda>output.
            enn2real
              (slp_right_positive_output_density R cutoff right_potential
                (slp_positive_terminal_riesz_weight R right_potential)
                right_order root output) powr slp_branch_power_exponent p)"
    by (rule endpoint(2))
qed

end

end
