theory Inverse_Schrodinger_Lp_Born_All_Order_Weighted
  imports Inverse_Schrodinger_Lp_Born_Weighted_Exponents
begin

section \<open>All-order control at an explicit manuscript exponent\<close>

context aim_planar_riesz_hls
begin

theorem slp_positive_output_density_all_orders_weighted:
  fixes R C p :: real
    and cutoff potential :: "slp_point \<Rightarrow> complex"
    and terminal_weight :: "slp_point \<Rightarrow> ennreal"
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and terminal_lp:
      "slp_positive_ennreal_lp_on_plane
        (slp_branch_terminal_exponent p) terminal_weight"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows power_range:
      "1 < slp_branch_power_exponent p \<and>
        slp_branch_power_exponent p < p"
    and all_orders:
      "\<And>n. \<exists>L. 0 \<le> L \<and>
        (\<forall>origin. slp_positive_ennreal_lp_on_plane
          (slp_branch_power_exponent p)
          (slp_positive_output_density R cutoff potential terminal_weight n
            origin)) \<and>
        (\<forall>origin. integral\<^sup>L lborel
          (\<lambda>output.
            enn2real
              (slp_positive_output_density R cutoff potential terminal_weight n
                origin output) powr slp_branch_power_exponent p) \<le> L)"
proof -
  note exponents = slp_branch_weighted_exponents[OF p_lower p_upper]
  show "1 < slp_branch_power_exponent p \<and>
      slp_branch_power_exponent p < p"
    using exponents(1,2) by blast
  have kernel_lower:
      "1 \<le> slp_branch_kernel_exponent p"
    using exponents(5) by linarith
  show "\<exists>L. 0 \<le> L \<and>
      (\<forall>origin. slp_positive_ennreal_lp_on_plane
        (slp_branch_power_exponent p)
        (slp_positive_output_density R cutoff potential terminal_weight n
          origin)) \<and>
      (\<forall>origin. integral\<^sup>L lborel
        (\<lambda>output.
          enn2real
            (slp_positive_output_density R cutoff potential terminal_weight n
              origin output) powr slp_branch_power_exponent p) \<le> L)"
    for n
    by (rule slp_positive_output_density_all_orders_from_terminal_lp[OF
          radius_nonnegative p_lower p_upper exponents(1) exponents(3)
          exponents(4) kernel_lower exponents(6) exponents(7) exponents(8)
          exponents(9) cutoff_measurable potential_lp terminal_lp cutoff_bound
          C_nonnegative])
qed

end

end
