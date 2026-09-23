theory Inverse_Schrodinger_Lp_Output_Density_All_Order_Terminal_Weighted_L1
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Positive_Output_Density_Bounded_Support"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_All_Order_Terminal_Weighted_Aliases"
begin

section \<open>All-order fixed-root L1 certificates\<close>

context aim_planar_riesz_hls
begin

theorem slp_left_right_positive_output_density_all_orders_terminal_weighted_L1:
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
    and left_all_orders_L1:
      "\<And>n origin. slp_positive_ennreal_lp_on_plane 1
        (slp_left_positive_output_density R cutoff potential
          (slp_positive_terminal_riesz_weight R potential) n origin)"
    and right_all_orders_L1:
      "\<And>n origin. slp_positive_ennreal_lp_on_plane 1
        (slp_right_positive_output_density R cutoff potential
          (slp_positive_terminal_riesz_weight R potential) n origin)"
proof -
  note all_order =
    slp_left_right_positive_output_density_all_orders_terminal_weighted[OF
      radius_nonnegative p_lower p_upper cutoff_measurable potential_lp
      cutoff_bound C_nonnegative]
  have exponent_lower: "1 < slp_branch_power_exponent p"
    using all_order(1) by blast
  show
    "1 < slp_branch_power_exponent p \<and>
      slp_branch_power_exponent p < p"
    by (rule all_order(1))
  show
    "slp_positive_ennreal_lp_on_plane 1
      (slp_left_positive_output_density R cutoff potential
        (slp_positive_terminal_riesz_weight R potential) n origin)"
    for n origin
  proof -
    obtain L where left_lp_all:
      "\<forall>root. slp_positive_ennreal_lp_on_plane
        (slp_branch_power_exponent p)
        (slp_left_positive_output_density R cutoff potential
          (slp_positive_terminal_riesz_weight R potential) n root)"
      using all_order(2)[of n] by blast
    have left_lp:
      "slp_positive_ennreal_lp_on_plane
        (slp_branch_power_exponent p)
        (slp_left_positive_output_density R cutoff potential
          (slp_positive_terminal_riesz_weight R potential) n origin)"
      using left_lp_all by blast
    have left_support:
      "bounded {out.
        slp_left_positive_output_density R cutoff potential
          (slp_positive_terminal_riesz_weight R potential) n origin out
          \<noteq> 0}"
      by (rule slp_left_positive_output_density_bounded_support[OF
            radius_nonnegative])
    show ?thesis
      by (rule slp_positive_ennreal_lp_bounded_support_to_L1[OF
            less_imp_le[OF exponent_lower] left_lp left_support])
  qed
  show
    "slp_positive_ennreal_lp_on_plane 1
      (slp_right_positive_output_density R cutoff potential
        (slp_positive_terminal_riesz_weight R potential) n origin)"
    for n origin
  proof -
    obtain L where right_lp_all:
      "\<forall>root. slp_positive_ennreal_lp_on_plane
        (slp_branch_power_exponent p)
        (slp_right_positive_output_density R cutoff potential
          (slp_positive_terminal_riesz_weight R potential) n root)"
      using all_order(3)[of n] by blast
    have right_lp:
      "slp_positive_ennreal_lp_on_plane
        (slp_branch_power_exponent p)
        (slp_right_positive_output_density R cutoff potential
          (slp_positive_terminal_riesz_weight R potential) n origin)"
      using right_lp_all by blast
    have right_support:
      "bounded {out.
        slp_right_positive_output_density R cutoff potential
          (slp_positive_terminal_riesz_weight R potential) n origin out
          \<noteq> 0}"
      by (rule slp_right_positive_output_density_bounded_support[OF
            radius_nonnegative])
    show ?thesis
      by (rule slp_positive_ennreal_lp_bounded_support_to_L1[OF
            less_imp_le[OF exponent_lower] right_lp right_support])
  qed
qed

end

end
