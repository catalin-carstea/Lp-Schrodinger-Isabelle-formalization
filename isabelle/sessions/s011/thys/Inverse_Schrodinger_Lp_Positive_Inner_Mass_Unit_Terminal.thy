theory Inverse_Schrodinger_Lp_Positive_Inner_Mass_Unit_Terminal
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Positive_Inner_Mass_Weighted_Cutoff"
begin

section \<open>Bounded-carrier unit-terminal finite inner mass\<close>

lemma slp_positive_ennreal_lp_indicator_bounded:
  fixes X :: "slp_point set"
  assumes q_positive: "0 < q"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
  shows
    "slp_positive_ennreal_lp_on_plane q
      (\<lambda>x. ennreal (indicator X x :: real))"
proof -
  have indicator_integrable:
      "integrable lborel (indicator X :: slp_point \<Rightarrow> real)"
    using X_measurable emeasure_bounded_finite[OF X_bounded]
    by (simp add: integrable_indicator_iff)
  have lifted_measurable:
      "(\<lambda>x. ennreal (indicator X x :: real))
        \<in> borel_measurable lborel"
    using X_measurable by measurable
  have power_eq:
      "(\<lambda>x. enn2real (ennreal (indicator X x :: real)) powr q) =
        indicator X"
    by (rule ext) (simp add: indicator_def q_positive)
  show ?thesis
    unfolding slp_positive_ennreal_lp_on_plane_def power_eq
    using lifted_measurable indicator_integrable by simp
qed

context aim_planar_riesz_hls
begin

theorem slp_left_branch_positive_inner_mass_unit_terminal_uniform:
  fixes branch_dummy :: "'i::finite itself"
    and R C p :: real
    and X :: "slp_point set"
    and cutoff potential output_factor :: "slp_point \<Rightarrow> complex"
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and cutoff_outside: "\<And>x. x \<notin> X \<Longrightarrow> cutoff x = 0"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and output_factor_lp:
      "aim_complex_lp_on_plane (slp_branch_holder_exponent p) output_factor"
  shows
    "\<exists>inner_cap :: ennreal. inner_cap < top_class.top \<and>
      (\<forall>origin.
        slp_left_branch_positive_inner_mass_finite TYPE('i) R cutoff
          potential (\<lambda>_. 1) output_factor origin \<le> inner_cap)"
proof -
  have terminal_positive: "0 < slp_branch_terminal_exponent p"
    unfolding slp_branch_terminal_exponent_def
    by (rule divide_pos_pos) (use p_lower p_upper in linarith)+
  have terminal_lp:
      "slp_positive_ennreal_lp_on_plane
        (slp_branch_terminal_exponent p)
        (\<lambda>x. ennreal (indicator X x :: real))"
    by (rule slp_positive_ennreal_lp_indicator_bounded[OF
          terminal_positive X_measurable X_bounded])
  have terminal_cutoff_le:
      "ennreal (cmod (cutoff x)) * ennreal (cmod (1 :: complex)) \<le>
        ennreal (cmod (cutoff x)) *
          ennreal (indicator X x :: real)"
    for x
    by (cases "x \<in> X")
       (simp_all add: indicator_def cutoff_outside)
  show ?thesis
    by (rule slp_left_branch_positive_inner_mass_weighted_cutoff_uniform[OF
          radius_nonnegative p_lower p_upper cutoff_measurable potential_lp
          terminal_lp cutoff_bound C_nonnegative _ terminal_cutoff_le
          output_factor_lp]) measurable
qed

end

end
