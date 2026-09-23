theory Inverse_Schrodinger_Lp_Born_All_Order_Terminal_Weighted_Aliases
  imports Inverse_Schrodinger_Lp_Born_All_Order_Terminal_Weighted
begin

section \<open>Left and right all-order weighted branch certificates\<close>

context aim_planar_riesz_hls
begin

theorem slp_left_right_positive_output_density_all_orders_terminal_weighted:
  fixes R C p :: real
    and cutoff potential :: "slp_point \<Rightarrow> complex"
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows power_range:
      "1 < slp_branch_power_exponent p \<and>
        slp_branch_power_exponent p < p"
    and left_all_orders:
      "\<And>n. \<exists>L. 0 \<le> L \<and>
        (\<forall>origin. slp_positive_ennreal_lp_on_plane
          (slp_branch_power_exponent p)
          (slp_left_positive_output_density R cutoff potential
            (slp_positive_terminal_riesz_weight R potential) n origin)) \<and>
        (\<forall>origin. integral\<^sup>L lborel
          (\<lambda>output.
            enn2real
              (slp_left_positive_output_density R cutoff potential
                (slp_positive_terminal_riesz_weight R potential) n origin
                output) powr slp_branch_power_exponent p) \<le> L)"
    and right_all_orders:
      "\<And>n. \<exists>L. 0 \<le> L \<and>
        (\<forall>origin. slp_positive_ennreal_lp_on_plane
          (slp_branch_power_exponent p)
          (slp_right_positive_output_density R cutoff potential
            (slp_positive_terminal_riesz_weight R potential) n origin)) \<and>
        (\<forall>origin. integral\<^sup>L lborel
          (\<lambda>output.
            enn2real
              (slp_right_positive_output_density R cutoff potential
                (slp_positive_terminal_riesz_weight R potential) n origin
                output) powr slp_branch_power_exponent p) \<le> L)"
proof -
  note result = slp_positive_output_density_all_orders_terminal_weighted[OF
      radius_nonnegative p_lower p_upper cutoff_measurable potential_lp
      cutoff_bound C_nonnegative]
  show "1 < slp_branch_power_exponent p \<and>
      slp_branch_power_exponent p < p"
    by (rule result(1))
  show "\<exists>L. 0 \<le> L \<and>
      (\<forall>origin. slp_positive_ennreal_lp_on_plane
        (slp_branch_power_exponent p)
        (slp_left_positive_output_density R cutoff potential
          (slp_positive_terminal_riesz_weight R potential) n origin)) \<and>
      (\<forall>origin. integral\<^sup>L lborel
        (\<lambda>output.
          enn2real
            (slp_left_positive_output_density R cutoff potential
              (slp_positive_terminal_riesz_weight R potential) n origin
              output) powr slp_branch_power_exponent p) \<le> L)"
    for n
    using result(2)[of n]
    by (simp only: slp_left_positive_output_density_def)
  show "\<exists>L. 0 \<le> L \<and>
      (\<forall>origin. slp_positive_ennreal_lp_on_plane
        (slp_branch_power_exponent p)
        (slp_right_positive_output_density R cutoff potential
          (slp_positive_terminal_riesz_weight R potential) n origin)) \<and>
      (\<forall>origin. integral\<^sup>L lborel
        (\<lambda>output.
          enn2real
            (slp_right_positive_output_density R cutoff potential
              (slp_positive_terminal_riesz_weight R potential) n origin
              output) powr slp_branch_power_exponent p) \<le> L)"
    for n
    using result(2)[of n]
    by (simp only: slp_right_positive_output_density_def)
qed

end

end
