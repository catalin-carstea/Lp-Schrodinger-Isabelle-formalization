theory Inverse_Schrodinger_Lp_Born_All_Order_Uniform_Power
  imports Inverse_Schrodinger_Lp_Born_Successor_Uniform_Power
begin

section \<open>All-order uniform finite-power induction\<close>

context aim_planar_riesz_hls
begin

lemma slp_positive_output_density_all_orders_uniform_power:
  fixes R C p a b L0 B :: real
    and cutoff potential :: "slp_point \<Rightarrow> complex"
    and terminal_weight :: "slp_point \<Rightarrow> ennreal"
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and a_lower: "1 < a"
    and b_lower: "1 < b"
    and conjugate: "1 / a + 1 / b = 1"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and terminal_weight_measurable:
      "terminal_weight \<in> borel_measurable lborel"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and base_lp:
      "\<And>origin. slp_positive_ennreal_lp_on_plane a
        (slp_positive_output_density R cutoff potential terminal_weight 0
          origin)"
    and base_power_bound:
      "\<And>origin.
        integral\<^sup>L lborel
          (\<lambda>output.
            enn2real
              (slp_positive_output_density R cutoff potential terminal_weight 0
                origin output) powr a) \<le> L0"
    and L0_nonnegative: "0 \<le> L0"
    and block_mass_bound:
      "\<And>origin.
        integral\<^sup>L lborel
          (slp_positive_branch_block_weight_real R cutoff potential origin)
          \<le> B"
    and B_nonnegative: "0 \<le> B"
  shows "\<And>n. \<exists>L. 0 \<le> L \<and>
    (\<forall>origin. slp_positive_ennreal_lp_on_plane a
      (slp_positive_output_density R cutoff potential terminal_weight n
        origin)) \<and>
    (\<forall>origin. integral\<^sup>L lborel
      (\<lambda>output.
        enn2real
          (slp_positive_output_density R cutoff potential terminal_weight n
            origin output) powr a) \<le> L)"
proof -
  fix n
  show "\<exists>L. 0 \<le> L \<and>
      (\<forall>origin. slp_positive_ennreal_lp_on_plane a
        (slp_positive_output_density R cutoff potential terminal_weight n
          origin)) \<and>
      (\<forall>origin. integral\<^sup>L lborel
        (\<lambda>output.
          enn2real
            (slp_positive_output_density R cutoff potential terminal_weight n
              origin output) powr a) \<le> L)"
  proof (induction n)
    case 0
    show ?case
      using L0_nonnegative base_lp base_power_bound by blast
  next
    case (Suc n)
    then obtain L where
      L_nonnegative: "0 \<le> L" and
      current_lp:
        "\<forall>origin. slp_positive_ennreal_lp_on_plane a
          (slp_positive_output_density R cutoff potential terminal_weight n
            origin)" and
      current_power_bound:
        "\<forall>origin. integral\<^sup>L lborel
          (\<lambda>output.
            enn2real
              (slp_positive_output_density R cutoff potential terminal_weight n
                origin output) powr a) \<le> L"
      by blast
    let ?next_bound =
      "inverse (pi ^ 2) powr a *
        (B powr (a / b) * (L * B))"
    have next_nonnegative: "0 \<le> ?next_bound"
      using L_nonnegative B_nonnegative by simp
    have next_lp:
        "\<And>origin. slp_positive_ennreal_lp_on_plane a
          (slp_positive_output_density R cutoff potential terminal_weight
            (Suc n) origin)"
      by (rule slp_positive_output_density_Suc_uniform_power(1)[OF
            radius_nonnegative p_lower p_upper a_lower b_lower conjugate
            cutoff_measurable potential_lp terminal_weight_measurable
            cutoff_bound current_lp[rule_format]
            current_power_bound[rule_format] L_nonnegative block_mass_bound
            B_nonnegative])
    have next_power_bound:
        "\<And>origin. integral\<^sup>L lborel
          (\<lambda>output.
            enn2real
              (slp_positive_output_density R cutoff potential terminal_weight
                (Suc n) origin output) powr a) \<le> ?next_bound"
      by (rule slp_positive_output_density_Suc_uniform_power(2)[OF
            radius_nonnegative p_lower p_upper a_lower b_lower conjugate
            cutoff_measurable potential_lp terminal_weight_measurable
            cutoff_bound current_lp[rule_format]
            current_power_bound[rule_format] L_nonnegative block_mass_bound
            B_nonnegative])
    show ?case
      using next_nonnegative next_lp next_power_bound by blast
  qed
qed

end

end
