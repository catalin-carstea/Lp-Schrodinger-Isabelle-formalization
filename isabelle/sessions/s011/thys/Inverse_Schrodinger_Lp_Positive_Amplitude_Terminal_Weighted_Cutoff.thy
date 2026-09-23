theory Inverse_Schrodinger_Lp_Positive_Amplitude_Terminal_Weighted_Cutoff
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Positive_Inner_Mass_Terminal_Weighted_Cutoff"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Positive_Amplitude_Terminal_Weighted"
begin

section \<open>Cutoff-local terminal-weighted packed amplitude finiteness\<close>

context aim_planar_riesz_hls
begin

theorem slp_left_branch_positive_amplitude_packed_terminal_weighted_cutoff_lt_top:
  fixes branch_dummy :: "'i::finite itself"
    and R C p :: real
    and root_weight cutoff potential terminal_value output_factor ::
      "slp_point \<Rightarrow> complex"
  assumes root_weight_integrable: "integrable lborel root_weight"
    and radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and terminal_value_measurable:
      "terminal_value \<in> borel_measurable lborel"
    and terminal_value_cutoff_le:
      "\<And>x. ennreal (cmod (cutoff x)) *
          ennreal (cmod (terminal_value x)) \<le>
        ennreal (cmod (cutoff x)) *
          slp_positive_terminal_riesz_weight R potential x"
    and output_factor_lp:
      "aim_complex_lp_on_plane (slp_branch_holder_exponent p) output_factor"
  shows
    "(\<integral>\<^sup>+ coordinates.
        case_prod (slp_left_branch_positive_amplitude_packed R root_weight
          cutoff potential terminal_value output_factor) coordinates
      \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
        (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) <
      top_class.top"
proof -
  have potential_measurable:
      "potential \<in> borel_measurable lborel"
    using potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have output_factor_measurable:
      "output_factor \<in> borel_measurable lborel"
    using output_factor_lp unfolding aim_complex_lp_on_plane_def by blast
  have inner_mass_uniform:
      "\<exists>inner_cap :: ennreal. inner_cap < top_class.top \<and>
        (\<forall>origin.
          slp_left_branch_positive_inner_mass_finite TYPE('i) R cutoff
            potential terminal_value output_factor origin \<le> inner_cap)"
    by (rule slp_left_branch_positive_inner_mass_terminal_weighted_cutoff_uniform[
          OF radius_nonnegative p_lower p_upper cutoff_measurable potential_lp
            cutoff_bound C_nonnegative terminal_value_measurable
            terminal_value_cutoff_le output_factor_lp])
  show ?thesis
    by (rule slp_left_branch_positive_amplitude_packed_lt_top_from_inner_mass[
          OF root_weight_integrable cutoff_measurable potential_measurable
            terminal_value_measurable output_factor_measurable
            inner_mass_uniform])
qed

end

end
