theory Inverse_Schrodinger_Lp_Cauchy_Local_Lp_Below_Two
  imports Inverse_Schrodinger_Lp_Cauchy_HLS_Local
begin

section \<open>Finite-measure descent between explicit power-integrability predicates\<close>

lemma slp_powr_le_one_add_powr:
  fixes p q x :: real
  assumes p_nonnegative: "0 \<le> p"
    and exponent_order: "p \<le> q"
    and x_nonnegative: "0 \<le> x"
  shows "x powr p \<le> 1 + x powr q"
proof (cases "x \<le> 1")
  case True
  have absolute_bound: "\<bar>x\<bar> \<le> 1"
    using x_nonnegative True by simp
  have "x powr p \<le> 1"
    by (rule powr_le1[OF p_nonnegative absolute_bound])
  also have "1 \<le> 1 + x powr q"
    by simp
  finally show ?thesis .
next
  case False
  have x_at_least_one: "1 \<le> x"
    using False by linarith
  have "x powr p \<le> x powr q"
    by (rule powr_mono[OF exponent_order x_at_least_one])
  also have "x powr q \<le> 1 + x powr q"
    by simp
  finally show ?thesis .
qed

lemma slp_complex_lp_on_mono_exponent_bounded:
  assumes p_positive: "0 < p"
    and exponent_order: "p \<le> q"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and f_lp: "slp_complex_lp_on q X f"
  shows "slp_complex_lp_on p X f"
proof -
  let ?g = "slp_restrict_field X f"
  have q_positive: "0 < q"
    using p_positive exponent_order by linarith
  have g_measurable: "?g \<in> borel_measurable lborel"
    and g_q_integrable:
      "integrable lborel (\<lambda>x. norm (?g x) powr q)"
    using f_lp
    unfolding slp_complex_lp_on_def aim_complex_lp_on_plane_def
    by auto
  have g_p_measurable:
    "(\<lambda>x. norm (?g x) powr p) \<in> borel_measurable lborel"
    using g_measurable by measurable
  have indicator_integrable:
    "integrable lborel (indicator X :: slp_point \<Rightarrow> real)"
    using X_measurable emeasure_bounded_finite[OF X_bounded]
    by (simp add: integrable_indicator_iff)
  have majorant_integrable:
    "integrable lborel
      (\<lambda>x. indicator X x + norm (?g x) powr q)"
    by (rule Bochner_Integration.integrable_add[OF
          indicator_integrable g_q_integrable])
  have pointwise_bound:
    "AE x in lborel.
      norm (norm (?g x) powr p) \<le>
        norm (indicator X x + norm (?g x) powr q)"
  proof (rule AE_I2)
    fix x :: slp_point
    have raw_bound:
      "norm (?g x) powr p \<le>
        indicator X x + norm (?g x) powr q"
    proof (cases "x \<in> X")
      case True
      have "norm (?g x) powr p \<le> 1 + norm (?g x) powr q"
        by (rule slp_powr_le_one_add_powr)
           (use p_positive exponent_order in auto)
      then show ?thesis
        using True by simp
    next
      case False
      then show ?thesis
        using p_positive q_positive
        by (simp add: slp_restrict_field_def)
    qed
    have left_nonnegative: "0 \<le> norm (?g x) powr p"
      by simp
    have right_nonnegative:
      "0 \<le> indicator X x + norm (?g x) powr q"
      by (cases "x \<in> X") simp_all
    show "norm (norm (?g x) powr p) \<le>
        norm (indicator X x + norm (?g x) powr q)"
      using raw_bound left_nonnegative right_nonnegative by simp
  qed
  have g_p_integrable:
    "integrable lborel (\<lambda>x. norm (?g x) powr p)"
    by (rule Bochner_Integration.integrable_bound[OF
          majorant_integrable g_p_measurable pointwise_bound])
  show ?thesis
    unfolding slp_complex_lp_on_def aim_complex_lp_on_plane_def
    using g_measurable g_p_integrable by blast
qed

lemma slp_hls_target_exponent_gt_input:
  assumes p_lower: "1 < p"
    and p_upper: "p < 2"
  shows "p < aim_hls_target_exponent p"
proof -
  have denominator_positive: "0 < 2 - p"
    using p_upper by linarith
  have p_positive: "0 < p"
    using p_lower by linarith
  have square_positive: "0 < p * p"
    by (rule mult_pos_pos[OF p_positive p_positive])
  have cleared: "p * (2 - p) < 2 * p"
  proof -
    have "p * (2 - p) = 2 * p - p * p"
      by (simp add: algebra_simps)
    also have "... < 2 * p"
      using square_positive by linarith
    finally show ?thesis .
  qed
  show ?thesis
    unfolding aim_hls_target_exponent_def
    by (subst pos_less_divide_eq[OF denominator_positive])
       (use cleared in simp)
qed

section \<open>The local zero-order term below exponent two\<close>

context aim_planar_hls_cauchy
begin

theorem slp_both_cauchy_local_lp_below_two:
  assumes p_lower: "1 < (p::real)"
    and p_upper: "p < 2"
    and f_lp: "aim_complex_lp_on_plane p f"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
  shows "slp_complex_lp_on p X (slp_dbar_inverse f) \<and>
    slp_complex_lp_on p X (slp_partial_inverse f)"
proof -
  have target_memberships:
    "slp_complex_lp_on (aim_hls_target_exponent p) X
        (slp_dbar_inverse f) \<and>
      slp_complex_lp_on (aim_hls_target_exponent p) X
        (slp_partial_inverse f)"
    using slp_both_cauchy_hls_sum_on_measurable assms by blast
  have p_positive: "0 < p"
    using p_lower by linarith
  have exponent_order: "p \<le> aim_hls_target_exponent p"
    using slp_hls_target_exponent_gt_input[OF p_lower p_upper]
    by linarith
  have dbar_local:
    "slp_complex_lp_on p X (slp_dbar_inverse f)"
    by (rule slp_complex_lp_on_mono_exponent_bounded[OF
          p_positive exponent_order X_measurable X_bounded])
       (use target_memberships in blast)
  have partial_local:
    "slp_complex_lp_on p X (slp_partial_inverse f)"
    by (rule slp_complex_lp_on_mono_exponent_bounded[OF
          p_positive exponent_order X_measurable X_bounded])
       (use target_memberships in blast)
  show ?thesis
    using dbar_local partial_local by blast
qed

end

end
