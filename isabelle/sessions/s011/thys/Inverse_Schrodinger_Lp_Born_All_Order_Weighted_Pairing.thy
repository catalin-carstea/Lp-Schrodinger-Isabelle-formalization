theory Inverse_Schrodinger_Lp_Born_All_Order_Weighted_Pairing
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_All_Order_Weighted"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Positive_Ennreal_Complex_Pairing_Bound"
begin

section \<open>Uniform output pairings for a generic terminal weight\<close>

context aim_planar_riesz_hls
begin

theorem slp_positive_output_density_all_orders_weighted_pairing_uniform:
  fixes R C p :: real
    and cutoff potential output_factor :: "slp_point \<Rightarrow> complex"
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
    and output_factor_lp:
      "aim_complex_lp_on_plane (slp_branch_holder_exponent p) output_factor"
  shows
    "\<And>n. \<exists>pairing_cap :: ennreal. pairing_cap < top_class.top \<and>
      (\<forall>origin.
        (\<integral>\<^sup>+ output.
          slp_positive_output_density R cutoff potential terminal_weight n
              origin output *
            ennreal (cmod (output_factor output))
          \<partial>lborel) \<le> pairing_cap)"
proof -
  note exponents = slp_branch_weighted_exponents[OF p_lower p_upper]
  note weighted = slp_positive_output_density_all_orders_weighted[OF
      radius_nonnegative p_lower p_upper cutoff_measurable potential_lp
      terminal_lp cutoff_bound C_nonnegative]
  fix n
  obtain L where L_nonnegative: "0 \<le> L"
    and density_lp:
      "\<forall>origin. slp_positive_ennreal_lp_on_plane
        (slp_branch_power_exponent p)
        (slp_positive_output_density R cutoff potential terminal_weight n
          origin)"
    and density_power_bound:
      "\<forall>origin. integral\<^sup>L lborel
        (\<lambda>output.
          enn2real
            (slp_positive_output_density R cutoff potential terminal_weight n
              origin output) powr slp_branch_power_exponent p) \<le> L"
    using weighted(2)[of n] by blast
  let ?bound =
    "ennreal
      (L / slp_branch_power_exponent p +
        integral\<^sup>L lborel
          (\<lambda>x. cmod (output_factor x) powr
            slp_branch_holder_exponent p) /
          slp_branch_holder_exponent p)"
  have bound_finite: "?bound < top_class.top"
    by simp
  have pairing_uniform:
      "(\<integral>\<^sup>+ output.
        slp_positive_output_density R cutoff potential terminal_weight n
            origin output *
          ennreal (cmod (output_factor output))
        \<partial>lborel) \<le> ?bound"
    for origin
    by (rule slp_positive_ennreal_lp_complex_pairing_le[OF
          exponents(1) exponents(3) exponents(4)
          density_lp[rule_format, of origin]
          density_power_bound[rule_format, of origin]
          L_nonnegative output_factor_lp])
  show "\<exists>pairing_cap :: ennreal. pairing_cap < top_class.top \<and>
      (\<forall>origin.
        (\<integral>\<^sup>+ output.
          slp_positive_output_density R cutoff potential terminal_weight n
              origin output *
            ennreal (cmod (output_factor output))
          \<partial>lborel) \<le> pairing_cap)"
    by (intro exI[of _ ?bound] conjI bound_finite allI pairing_uniform)
qed

end

end
