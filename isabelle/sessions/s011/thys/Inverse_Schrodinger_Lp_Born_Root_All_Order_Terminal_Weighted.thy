theory Inverse_Schrodinger_Lp_Born_Root_All_Order_Terminal_Weighted
  imports Inverse_Schrodinger_Lp_Born_Root_Finite_Power
    Inverse_Schrodinger_Lp_Born_All_Order_Terminal_Weighted
    Inverse_Schrodinger_Lp_Born_One_Sided_Root_Lp
begin

section \<open>All-order root control with the exact terminal weight\<close>

context aim_planar_riesz_hls
begin

theorem slp_positive_root_output_density_all_orders_terminal_weighted_lp_root:
  fixes R C p :: real
    and X :: "slp_point set"
    and cutoff potential root_weight :: "slp_point \<Rightarrow> complex"
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and root_weight_lp: "aim_complex_lp_on_plane p root_weight"
    and root_weight_outside:
      "\<And>x. x \<notin> X \<Longrightarrow> root_weight x = 0"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows power_range:
      "1 < slp_branch_power_exponent p \<and>
        slp_branch_power_exponent p < p"
    and all_orders:
      "\<And>n. \<exists>L. 0 \<le> L \<and>
        slp_positive_ennreal_lp_on_plane
          (slp_branch_power_exponent p)
          (slp_positive_root_output_density R cutoff potential
            (slp_positive_terminal_riesz_weight R potential) n root_weight) \<and>
        integral\<^sup>L lborel
          (\<lambda>output. enn2real
            (slp_positive_root_output_density R cutoff potential
              (slp_positive_terminal_riesz_weight R potential) n root_weight
              output) powr slp_branch_power_exponent p) \<le>
        (integral\<^sup>L lborel (\<lambda>root. cmod (root_weight root)))
            powr (slp_branch_power_exponent p /
              slp_branch_holder_exponent p) *
          (L * integral\<^sup>L lborel
            (\<lambda>root. cmod (root_weight root)))"
proof -
  have potential_measurable:
      "potential \<in> borel_measurable lborel"
    using potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have root_weight_integrable: "integrable lborel root_weight"
    by (rule aim_complex_lp_on_plane_integrable_bounded_support[OF
          _ X_measurable X_bounded root_weight_lp root_weight_outside])
      (use p_lower in simp)
  have terminal_lp:
      "slp_positive_ennreal_lp_on_plane
        (slp_branch_terminal_exponent p)
        (slp_positive_terminal_riesz_weight R potential)"
    by (rule slp_positive_terminal_riesz_weight_lp[OF radius_nonnegative
          p_lower p_upper potential_lp])
  have terminal_measurable:
      "slp_positive_terminal_riesz_weight R potential
        \<in> borel_measurable lborel"
    using terminal_lp
    unfolding slp_positive_ennreal_lp_on_plane_def by blast
  note exponents = slp_branch_weighted_exponents[OF p_lower p_upper]
  note branch = slp_positive_output_density_all_orders_terminal_weighted[OF
      radius_nonnegative p_lower p_upper cutoff_measurable potential_lp
      cutoff_bound C_nonnegative]
  show "1 < slp_branch_power_exponent p \<and>
      slp_branch_power_exponent p < p"
    by (rule branch(1))
  show "\<exists>L. 0 \<le> L \<and>
      slp_positive_ennreal_lp_on_plane
        (slp_branch_power_exponent p)
        (slp_positive_root_output_density R cutoff potential
          (slp_positive_terminal_riesz_weight R potential) n root_weight) \<and>
      integral\<^sup>L lborel
        (\<lambda>output. enn2real
          (slp_positive_root_output_density R cutoff potential
            (slp_positive_terminal_riesz_weight R potential) n root_weight
            output) powr slp_branch_power_exponent p) \<le>
      (integral\<^sup>L lborel (\<lambda>root. cmod (root_weight root)))
          powr (slp_branch_power_exponent p /
            slp_branch_holder_exponent p) *
        (L * integral\<^sup>L lborel
          (\<lambda>root. cmod (root_weight root)))"
    for n
  proof -
    obtain L where L_nonnegative: "0 \<le> L"
      and density_lp:
        "\<forall>origin. slp_positive_ennreal_lp_on_plane
          (slp_branch_power_exponent p)
          (slp_positive_output_density R cutoff potential
            (slp_positive_terminal_riesz_weight R potential) n origin)"
      and density_bound:
        "\<forall>origin. integral\<^sup>L lborel
          (\<lambda>output. enn2real
            (slp_positive_output_density R cutoff potential
              (slp_positive_terminal_riesz_weight R potential) n origin
              output) powr slp_branch_power_exponent p) \<le> L"
      using branch(2)[of n] by blast
    have root_lp:
        "slp_positive_ennreal_lp_on_plane
          (slp_branch_power_exponent p)
          (slp_positive_root_output_density R cutoff potential
            (slp_positive_terminal_riesz_weight R potential) n root_weight)"
      by (rule slp_positive_root_output_density_finite_power(1)[OF
            exponents(1) exponents(3) exponents(4) cutoff_measurable
            potential_measurable terminal_measurable root_weight_integrable
            _ _ L_nonnegative])
        (use density_lp density_bound in blast)+
    have root_bound:
        "integral\<^sup>L lborel
          (\<lambda>output. enn2real
            (slp_positive_root_output_density R cutoff potential
              (slp_positive_terminal_riesz_weight R potential) n root_weight
              output) powr slp_branch_power_exponent p) \<le>
        (integral\<^sup>L lborel (\<lambda>root. cmod (root_weight root)))
            powr (slp_branch_power_exponent p /
              slp_branch_holder_exponent p) *
          (L * integral\<^sup>L lborel
            (\<lambda>root. cmod (root_weight root)))"
      by (rule slp_positive_root_output_density_finite_power(2)[OF
            exponents(1) exponents(3) exponents(4) cutoff_measurable
            potential_measurable terminal_measurable root_weight_integrable
            _ _ L_nonnegative])
        (use density_lp density_bound in blast)+
    show ?thesis using L_nonnegative root_lp root_bound by blast
  qed
qed

end

end
