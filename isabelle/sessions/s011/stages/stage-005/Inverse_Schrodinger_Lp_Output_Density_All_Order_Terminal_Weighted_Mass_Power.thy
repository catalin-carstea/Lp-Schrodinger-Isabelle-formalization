theory Inverse_Schrodinger_Lp_Output_Density_All_Order_Terminal_Weighted_Mass_Power
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Positive_Ennreal_Cball_Mass_Power_Bound"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Output_Density_All_Order_Terminal_Weighted_L1"
begin

section \<open>Uniform mass powers for terminal-weighted output densities\<close>

context aim_planar_riesz_hls
begin

theorem slp_left_right_positive_output_density_all_orders_terminal_weighted_mass_power:
  fixes R C p :: real
    and cutoff potential :: "slp_point \<Rightarrow> complex"
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows left_all_orders:
      "\<And>n. \<exists>M. 0 \<le> M \<and> (\<forall>origin.
        enn2real
          (\<integral>\<^sup>+ output.
            slp_left_positive_output_density R cutoff potential
              (slp_positive_terminal_riesz_weight R potential) n origin output
            \<partial>lborel) powr slp_branch_power_exponent p \<le> M)"
    and right_all_orders:
      "\<And>n. \<exists>M. 0 \<le> M \<and> (\<forall>origin.
        enn2real
          (\<integral>\<^sup>+ output.
            slp_right_positive_output_density R cutoff potential
              (slp_positive_terminal_riesz_weight R potential) n origin output
            \<partial>lborel) powr slp_branch_power_exponent p \<le> M)"
proof -
  let ?a = "slp_branch_power_exponent p"
  let ?b = "slp_branch_holder_exponent p"
  note exponents = slp_branch_weighted_exponents[OF p_lower p_upper]
  note all_order =
    slp_left_right_positive_output_density_all_orders_terminal_weighted[OF
      radius_nonnegative p_lower p_upper cutoff_measurable potential_lp
      cutoff_bound C_nonnegative]
  show "\<exists>M. 0 \<le> M \<and> (\<forall>origin.
      enn2real
        (\<integral>\<^sup>+ output.
          slp_left_positive_output_density R cutoff potential
            (slp_positive_terminal_riesz_weight R potential) n origin output
          \<partial>lborel) powr ?a \<le> M)"
    for n
  proof -
    obtain L where L_nonnegative: "0 \<le> L"
      and left_lp:
        "\<forall>origin. slp_positive_ennreal_lp_on_plane ?a
          (slp_left_positive_output_density R cutoff potential
            (slp_positive_terminal_riesz_weight R potential) n origin)"
      and left_power:
        "\<forall>origin. integral\<^sup>L lborel
          (\<lambda>output. enn2real
            (slp_left_positive_output_density R cutoff potential
              (slp_positive_terminal_riesz_weight R potential) n origin output)
              powr ?a) \<le> L"
      using all_order(2)[of n] by blast
    let ?radius = "real (Suc n) * R"
    let ?M =
      "(unit_ball_vol (DIM(slp_point)) * ?radius ^ DIM(slp_point))
        powr (?a / ?b) * L"
    have local_radius_nonnegative: "0 \<le> ?radius"
      using radius_nonnegative by simp
    have M_nonnegative: "0 \<le> ?M"
      using L_nonnegative by simp
    have bound: "enn2real
        (\<integral>\<^sup>+ output.
          slp_left_positive_output_density R cutoff potential
            (slp_positive_terminal_riesz_weight R potential) n origin output
          \<partial>lborel) powr ?a \<le> ?M"
      for origin
    proof (rule slp_positive_ennreal_lp_cball_mass_power_bound[OF
          exponents(1) exponents(3) exponents(4)
          local_radius_nonnegative L_nonnegative])
      show "slp_positive_ennreal_lp_on_plane ?a
          (slp_left_positive_output_density R cutoff potential
            (slp_positive_terminal_riesz_weight R potential) n origin)"
        using left_lp by blast
      show "\<And>output. output \<notin> cball origin ?radius \<Longrightarrow>
          slp_left_positive_output_density R cutoff potential
            (slp_positive_terminal_riesz_weight R potential) n origin output = 0"
      proof -
        fix out :: slp_point
        assume outside: "out \<notin> cball origin ?radius"
        have far: "?radius < Real_Vector_Spaces.norm (out - origin)"
          using outside by (simp add: dist_norm norm_minus_commute)
        show "slp_left_positive_output_density R cutoff potential
            (slp_positive_terminal_riesz_weight R potential) n origin out = 0"
          unfolding slp_left_positive_output_density_def
          by (rule slp_positive_output_density_outside[OF
                radius_nonnegative far])
      qed
      show "integral\<^sup>L lborel
          (\<lambda>output. enn2real
            (slp_left_positive_output_density R cutoff potential
              (slp_positive_terminal_riesz_weight R potential) n origin output)
              powr ?a) \<le> L"
        using left_power by blast
    qed
    show ?thesis using M_nonnegative bound by blast
  qed
  show "\<exists>M. 0 \<le> M \<and> (\<forall>origin.
      enn2real
        (\<integral>\<^sup>+ output.
          slp_right_positive_output_density R cutoff potential
            (slp_positive_terminal_riesz_weight R potential) n origin output
          \<partial>lborel) powr ?a \<le> M)"
    for n
  proof -
    obtain L where L_nonnegative: "0 \<le> L"
      and right_lp:
        "\<forall>origin. slp_positive_ennreal_lp_on_plane ?a
          (slp_right_positive_output_density R cutoff potential
            (slp_positive_terminal_riesz_weight R potential) n origin)"
      and right_power:
        "\<forall>origin. integral\<^sup>L lborel
          (\<lambda>output. enn2real
            (slp_right_positive_output_density R cutoff potential
              (slp_positive_terminal_riesz_weight R potential) n origin output)
              powr ?a) \<le> L"
      using all_order(3)[of n] by blast
    let ?radius = "real (Suc n) * R"
    let ?M =
      "(unit_ball_vol (DIM(slp_point)) * ?radius ^ DIM(slp_point))
        powr (?a / ?b) * L"
    have local_radius_nonnegative: "0 \<le> ?radius"
      using radius_nonnegative by simp
    have M_nonnegative: "0 \<le> ?M"
      using L_nonnegative by simp
    have bound: "enn2real
        (\<integral>\<^sup>+ output.
          slp_right_positive_output_density R cutoff potential
            (slp_positive_terminal_riesz_weight R potential) n origin output
          \<partial>lborel) powr ?a \<le> ?M"
      for origin
    proof (rule slp_positive_ennreal_lp_cball_mass_power_bound[OF
          exponents(1) exponents(3) exponents(4)
          local_radius_nonnegative L_nonnegative])
      show "slp_positive_ennreal_lp_on_plane ?a
          (slp_right_positive_output_density R cutoff potential
            (slp_positive_terminal_riesz_weight R potential) n origin)"
        using right_lp by blast
      show "\<And>output. output \<notin> cball origin ?radius \<Longrightarrow>
          slp_right_positive_output_density R cutoff potential
            (slp_positive_terminal_riesz_weight R potential) n origin output = 0"
      proof -
        fix out :: slp_point
        assume outside: "out \<notin> cball origin ?radius"
        have far: "?radius < Real_Vector_Spaces.norm (out - origin)"
          using outside by (simp add: dist_norm norm_minus_commute)
        show "slp_right_positive_output_density R cutoff potential
            (slp_positive_terminal_riesz_weight R potential) n origin out = 0"
          unfolding slp_right_positive_output_density_def
          by (rule slp_positive_output_density_outside[OF
                radius_nonnegative far])
      qed
      show "integral\<^sup>L lborel
          (\<lambda>output. enn2real
            (slp_right_positive_output_density R cutoff potential
              (slp_positive_terminal_riesz_weight R potential) n origin output)
              powr ?a) \<le> L"
        using right_power by blast
    qed
    show ?thesis using M_nonnegative bound by blast
  qed
qed

end

end
