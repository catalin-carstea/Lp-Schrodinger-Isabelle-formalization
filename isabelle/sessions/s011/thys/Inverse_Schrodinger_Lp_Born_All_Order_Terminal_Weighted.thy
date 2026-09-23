theory Inverse_Schrodinger_Lp_Born_All_Order_Terminal_Weighted
  imports Inverse_Schrodinger_Lp_Born_Terminal_Weighted_Lp
begin

section \<open>All-order weighted control for the exact terminal weight\<close>

context aim_planar_riesz_hls
begin

theorem slp_positive_output_density_all_orders_terminal_weighted:
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
    and all_orders:
      "\<And>n. \<exists>L. 0 \<le> L \<and>
        (\<forall>origin. slp_positive_ennreal_lp_on_plane
          (slp_branch_power_exponent p)
          (slp_positive_output_density R cutoff potential
            (slp_positive_terminal_riesz_weight R potential) n origin)) \<and>
        (\<forall>origin. integral\<^sup>L lborel
          (\<lambda>output.
            enn2real
              (slp_positive_output_density R cutoff potential
                (slp_positive_terminal_riesz_weight R potential) n origin
                output) powr slp_branch_power_exponent p) \<le> L)"
proof -
  have terminal_lp:
      "slp_positive_ennreal_lp_on_plane
        (slp_branch_terminal_exponent p)
        (slp_positive_terminal_riesz_weight R potential)"
    by (rule slp_positive_terminal_riesz_weight_lp[OF radius_nonnegative
          p_lower p_upper potential_lp])
  note result = slp_positive_output_density_all_orders_weighted[OF
      radius_nonnegative p_lower p_upper cutoff_measurable potential_lp
      terminal_lp cutoff_bound C_nonnegative]
  show "1 < slp_branch_power_exponent p \<and>
      slp_branch_power_exponent p < p"
    by (rule result(1))
  show "\<exists>L. 0 \<le> L \<and>
      (\<forall>origin. slp_positive_ennreal_lp_on_plane
        (slp_branch_power_exponent p)
        (slp_positive_output_density R cutoff potential
          (slp_positive_terminal_riesz_weight R potential) n origin)) \<and>
      (\<forall>origin. integral\<^sup>L lborel
        (\<lambda>output.
          enn2real
            (slp_positive_output_density R cutoff potential
              (slp_positive_terminal_riesz_weight R potential) n origin
              output) powr slp_branch_power_exponent p) \<le> L)"
    for n
    by (rule result(2))
qed

end

end
