theory Inverse_Schrodinger_Lp_Positive_Inner_Mass_Terminal_Weighted
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Positive_Inner_Mass_Functional"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Positive_Branch_Functional_Monotone"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Output_Pushforward"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_All_Order_Terminal_Weighted_Pairing"
begin

section \<open>Uniform terminal-weighted finite inner mass\<close>

context aim_planar_riesz_hls
begin

theorem slp_left_branch_positive_inner_mass_terminal_weighted_uniform:
  fixes branch_dummy :: "'i::finite itself"
    and R C p :: real
    and cutoff potential terminal_value output_factor ::
      "slp_point \<Rightarrow> complex"
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and terminal_value_measurable:
      "terminal_value \<in> borel_measurable lborel"
    and terminal_value_le:
      "\<And>x. ennreal (cmod (terminal_value x)) \<le>
        slp_positive_terminal_riesz_weight R potential x"
    and output_factor_lp:
      "aim_complex_lp_on_plane (slp_branch_holder_exponent p) output_factor"
  shows
    "\<exists>inner_cap :: ennreal. inner_cap < top_class.top \<and>
      (\<forall>origin.
        slp_left_branch_positive_inner_mass_finite TYPE('i) R cutoff
          potential terminal_value output_factor origin \<le> inner_cap)"
proof -
  have potential_measurable:
      "potential \<in> borel_measurable lborel"
    using potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have output_factor_measurable:
      "output_factor \<in> borel_measurable lborel"
    using output_factor_lp unfolding aim_complex_lp_on_plane_def by blast
  have output_test_measurable:
      "(\<lambda>x. ennreal (cmod (output_factor x)))
        \<in> borel_measurable lborel"
    using output_factor_measurable by measurable
  have terminal_weight_measurable:
      "slp_positive_terminal_riesz_weight R potential
        \<in> borel_measurable lborel"
    by (rule slp_positive_terminal_riesz_weight_measurable[OF
          potential_measurable])
  obtain pairing_cap where pairing_cap_finite:
      "pairing_cap < top_class.top"
    and pairing_bound:
      "\<forall>origin.
        (\<integral>\<^sup>+ output.
          slp_positive_output_density R cutoff potential
              (slp_positive_terminal_riesz_weight R potential) CARD('i)
              origin output *
            ennreal (cmod (output_factor output))
          \<partial>lborel) \<le> pairing_cap"
    using slp_positive_output_density_all_orders_terminal_weighted_pairing_uniform[
      OF radius_nonnegative p_lower p_upper cutoff_measurable potential_lp
        cutoff_bound C_nonnegative output_factor_lp, of "CARD('i)"]
    by blast
  have inner_bound:
      "slp_left_branch_positive_inner_mass_finite TYPE('i) R cutoff
          potential terminal_value output_factor origin \<le> pairing_cap"
    for origin
  proof -
    have functional_le:
        "slp_positive_branch_functional R cutoff potential
            (\<lambda>x. ennreal (cmod (terminal_value x))) CARD('i) origin
            (\<lambda>x. ennreal (cmod (output_factor x))) \<le>
          slp_positive_branch_functional R cutoff potential
            (slp_positive_terminal_riesz_weight R potential) CARD('i) origin
            (\<lambda>x. ennreal (cmod (output_factor x)))"
      by (rule slp_positive_branch_functional_mono)
        (rule terminal_value_le, simp)
    have pushforward:
        "(\<integral>\<^sup>+ output.
            ennreal (cmod (output_factor output)) *
              slp_positive_output_density R cutoff potential
                (slp_positive_terminal_riesz_weight R potential) CARD('i)
                origin output
            \<partial>lborel) =
          slp_positive_branch_functional R cutoff potential
            (slp_positive_terminal_riesz_weight R potential) CARD('i) origin
            (\<lambda>x. ennreal (cmod (output_factor x)))"
      by (rule slp_positive_output_density_pushforward[OF
            cutoff_measurable potential_measurable terminal_weight_measurable
            output_test_measurable])
    have functional_bound:
        "slp_positive_branch_functional R cutoff potential
            (slp_positive_terminal_riesz_weight R potential) CARD('i) origin
            (\<lambda>x. ennreal (cmod (output_factor x))) \<le> pairing_cap"
      using pairing_bound[rule_format, of origin] pushforward
      by (simp add: mult.commute)
    show ?thesis
      apply (subst slp_left_branch_positive_inner_mass_finite_functional[
          OF cutoff_measurable potential_measurable terminal_value_measurable
            output_factor_measurable])
      using functional_le functional_bound by auto
  qed
  show ?thesis
    by (intro exI[of _ pairing_cap] conjI pairing_cap_finite allI inner_bound)
qed

end

end
