theory Inverse_Schrodinger_Lp_Inner_Cauchy_Fixed_Carrier_Norm
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Inner_Cauchy_Cutoff_Norm_Bounds"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Quantitative_Complex_Holder"
begin

section \<open>Homogeneous finite-measure exponent descent\<close>

theorem slp_complex_lp_norm_on_mono_exponent_bounded:
  assumes p_positive: "0 < (p::real)"
    and exponent_order: "p < q"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and f_lp: "slp_complex_lp_on q X f"
  shows membership: "slp_complex_lp_on p X f"
    and norm_bound:
      "slp_complex_lp_norm_on p X f \<le>
        measure lborel X powr (1 / p - 1 / q) *
          slp_complex_lp_norm_on q X f"
proof -
  have q_positive: "0 < q"
    using p_positive exponent_order by linarith
  have p_nonzero: "p \<noteq> 0" and q_nonzero: "q \<noteq> 0"
    using p_positive q_positive by simp_all
  have q_minus_p_positive: "0 < q - p"
    using exponent_order by linarith
  have first_exponent_lower: "1 < q / p"
    using p_positive exponent_order
    by (simp add: less_divide_eq)
  have second_exponent_lower: "1 < q / (q - p)"
    using q_minus_p_positive p_positive
    by (simp add: less_divide_eq)
  have second_exponent_positive: "0 < q / (q - p)"
    using second_exponent_lower by linarith
  have conjugate_exponents:
      "1 / (q / p) + 1 / (q / (q - p)) = (1::real)"
    using p_nonzero q_nonzero q_minus_p_positive
    by (simp add: divide_simps algebra_simps)
  have first_inverse: "1 / (q / p) = p / q"
    using p_nonzero q_nonzero by (simp add: divide_simps algebra_simps)
  have second_inverse: "1 / (q / (q - p)) = (q - p) / q"
    using q_nonzero q_minus_p_positive
    by (simp add: divide_simps algebra_simps)
  have first_root_exponent: "(p / q) * (1 / p) = 1 / q"
    using p_nonzero q_nonzero by (simp add: divide_simps algebra_simps)
  have second_root_exponent:
      "((q - p) / q) * (1 / p) = 1 / p - 1 / q"
    using p_nonzero q_nonzero by (simp add: divide_simps algebra_simps)

  let ?g = "slp_restrict_field X f"
  have g_measurable: "?g \<in> borel_measurable lborel"
    and g_q_integrable:
      "integrable lborel (\<lambda>x. norm_class.norm (?g x) powr q)"
    using f_lp
    unfolding slp_complex_lp_on_def aim_complex_lp_on_plane_def
    by auto
  have lower_measurable:
      "(\<lambda>x. norm_class.norm (?g x) powr p) \<in> borel_measurable lborel"
    using g_measurable by measurable
  have indicator_measurable:
      "(indicator X :: slp_point \<Rightarrow> real)
        \<in> borel_measurable lborel"
    using X_measurable by measurable
  have indicator_integrable:
      "integrable lborel (indicator X :: slp_point \<Rightarrow> real)"
    using X_measurable emeasure_bounded_finite[OF X_bounded]
    by (simp add: integrable_indicator_iff)
  have lower_power_integrable:
      "integrable lborel
        (\<lambda>x. (norm_class.norm (?g x) powr p) powr (q / p))"
    using g_q_integrable p_nonzero
    by (simp add: powr_powr)
  have indicator_power_eq:
      "(\<lambda>x. indicator X x powr (q / (q - p))) =
        (indicator X :: slp_point \<Rightarrow> real)"
    apply (rule ext)
    using second_exponent_positive
    by (auto simp: indicator_def)
  have indicator_power_integrable:
      "integrable lborel
        (\<lambda>x. indicator X x powr (q / (q - p)))"
    using indicator_integrable indicator_power_eq by simp
  note holder = slp_nonnegative_holder_integral[
    where M=lborel and q="q / p" and r="q / (q - p)"
      and f="\<lambda>x. norm_class.norm (?g x) powr p"
      and g="indicator X",
    OF first_exponent_lower second_exponent_lower conjugate_exponents
      lower_measurable indicator_measurable]
  have restricted_product:
      "(\<lambda>x. norm_class.norm (?g x) powr p * indicator X x) =
        (\<lambda>x. norm_class.norm (?g x) powr p)"
    apply (rule ext)
    using p_positive
    by (auto simp: slp_restrict_field_def indicator_def)
  have indicator_power_integral:
      "integral\<^sup>L lborel
          (\<lambda>x. indicator X x powr (q / (q - p))) =
        measure lborel X"
    using X_measurable indicator_power_eq by simp
  have raw_holder:
      "integral\<^sup>L lborel
          (\<lambda>x. (norm_class.norm (?g x) powr p) * indicator X x) \<le>
        (integral\<^sup>L lborel
          (\<lambda>x. (norm_class.norm (?g x) powr p) powr (q / p)))
            powr (1 / (q / p)) *
        (integral\<^sup>L lborel
          (\<lambda>x. indicator X x powr (q / (q - p))))
            powr (1 / (q / (q - p)))"
    by (rule holder(2))
       (simp_all add: lower_power_integrable indicator_power_integrable)
  have power_bound:
      "integral\<^sup>L lborel (\<lambda>x. norm_class.norm (?g x) powr p) \<le>
        (integral\<^sup>L lborel (\<lambda>x. norm_class.norm (?g x) powr q))
            powr (p / q) *
          measure lborel X powr ((q - p) / q)"
    using raw_holder p_nonzero
    unfolding restricted_product first_inverse second_inverse
      indicator_power_integral
    by (simp add: powr_powr)
  have lower_integral_nonnegative:
      "0 \<le> integral\<^sup>L lborel (\<lambda>x. norm_class.norm (?g x) powr p)"
    by (rule integral_nonneg_AE) simp
  have reciprocal_nonnegative: "0 \<le> 1 / p"
    using p_positive by simp
  have rooted_bound:
      "(integral\<^sup>L lborel (\<lambda>x. norm_class.norm (?g x) powr p))
          powr (1 / p) \<le>
        ((integral\<^sup>L lborel (\<lambda>x. norm_class.norm (?g x) powr q))
            powr (p / q) *
          measure lborel X powr ((q - p) / q)) powr (1 / p)"
    by (rule powr_mono2[OF reciprocal_nonnegative
          lower_integral_nonnegative power_bound])
  have root_presentation:
      "((integral\<^sup>L lborel (\<lambda>x. norm_class.norm (?g x) powr q))
            powr (p / q) *
          measure lborel X powr ((q - p) / q)) powr (1 / p) =
        measure lborel X powr (1 / p - 1 / q) *
          (integral\<^sup>L lborel (\<lambda>x. norm_class.norm (?g x) powr q))
            powr (1 / q)"
    using first_root_exponent second_root_exponent p_nonzero q_nonzero
    by (simp add: powr_mult powr_powr mult.commute)
  show "slp_complex_lp_on p X f"
    by (rule slp_complex_lp_on_mono_exponent_bounded[OF
          p_positive less_imp_le[OF exponent_order]
          X_measurable X_bounded f_lp])
  show "slp_complex_lp_norm_on p X f \<le>
      measure lborel X powr (1 / p - 1 / q) *
        slp_complex_lp_norm_on q X f"
    using rooted_bound root_presentation
    unfolding slp_complex_lp_norm_on_def aim_complex_lp_norm_def
    by simp
qed

section \<open>Fixed-carrier raw inner-Cauchy graph bounds\<close>

context slp_cauchy_local_w1s
begin

theorem slp_both_inner_cauchy_fixed_carrier_w1p_norm_bounds:
  fixes s :: real
    and X Y :: "slp_point set"
  assumes exponent_lower: "1 < s"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and Y_bounded: "bounded Y"
  shows
    "\<exists>C::real. 0 < C \<and>
      (\<forall>tau c source.
        aim_complex_lp_on_plane s source \<and>
        {x. source x \<noteq> 0} \<subseteq> Y
        \<longrightarrow>
        slp_w1p_norm_on s X
            (slp_dbar_psi_inverse tau c source)
            (slp_dbar_inverse_gradient
              (slp_oscillatory_modulation (- tau) c source))
          \<le> C * aim_complex_lp_norm s source
        \<and>
        slp_w1p_norm_on s X
            (slp_partial_psi_inverse (- tau) c source)
            (slp_partial_inverse_gradient
              (slp_oscillatory_modulation (- tau) c source))
          \<le> C * aim_complex_lp_norm s source)"
proof -
  let ?E = "closure Y"
  have exponent_positive: "0 < s" and exponent_one_le: "1 \<le> s"
    using exponent_lower by linarith+
  have local_norm_nonnegative [simp]:
      "0 \<le> slp_complex_lp_norm_on p A h"
    for p :: real and A :: "slp_point set" and h :: slp_scalar_field
    unfolding slp_complex_lp_norm_on_def aim_complex_lp_norm_def
    by (rule powr_ge_zero)
  have E_measurable: "?E \<in> sets lborel"
    by simp
  have E_bounded: "bounded ?E"
    by (rule bounded_closure[OF Y_bounded])
  have carried_restriction:
      "slp_restrict_field ?E g = g"
    if carrier: "{x. g x \<noteq> 0} \<subseteq> Y"
    for g :: slp_scalar_field
  proof (rule ext)
    fix x
    show "slp_restrict_field ?E g x = g x"
    proof (cases "x \<in> ?E")
      case True
      then show ?thesis by (simp add: slp_restrict_field_def)
    next
      case False
      have "g x = 0"
      proof (rule ccontr)
        assume "g x \<noteq> 0"
        then have "x \<in> Y" using carrier by blast
        then show False using False by simp
      qed
      then show ?thesis using False by (simp add: slp_restrict_field_def)
    qed
  qed
  obtain K :: real where K_positive: "0 < K"
    and K_bound:
      "\<And>p f Z. 1 < p \<Longrightarrow> p < 2 \<Longrightarrow>
        aim_complex_lp_on_plane p f \<Longrightarrow> Z \<in> sets lborel \<Longrightarrow>
        slp_complex_lp_on (aim_hls_target_exponent p) Z
            (slp_dbar_inverse f) \<and>
        slp_complex_lp_on (aim_hls_target_exponent p) Z
            (slp_partial_inverse f) \<and>
        slp_complex_lp_norm_on (aim_hls_target_exponent p) Z
              (slp_partial_inverse f) +
          slp_complex_lp_norm_on (aim_hls_target_exponent p) Z
              (slp_dbar_inverse f)
          \<le> K / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
    using slp_both_cauchy_hls_sum_on_measurable by blast
  have zero_order_package:
      "\<exists>Z::real. 0 \<le> Z \<and>
        (\<forall>g. aim_complex_lp_on_plane s g \<and>
            {x. g x \<noteq> 0} \<subseteq> Y
          \<longrightarrow>
          slp_complex_lp_norm_on s X (slp_dbar_inverse g)
              \<le> Z * aim_complex_lp_norm s g \<and>
          slp_complex_lp_norm_on s X (slp_partial_inverse g)
              \<le> Z * aim_complex_lp_norm s g)"
  proof (cases "s < 2")
    case True
    let ?t = "aim_hls_target_exponent s"
    let ?A = "measure lborel X powr (1 / s - 1 / ?t)"
    let ?H = "K / ((s - 1) * (2 - s))"
    let ?Z = "abs (?A * ?H) + 1"
    have target_strict: "s < ?t"
      by (rule slp_hls_target_exponent_gt_input[OF exponent_lower True])
    have A_nonnegative: "0 \<le> ?A" by simp
    show ?thesis
    proof (rule exI[of _ ?Z], rule conjI)
      show "0 \<le> ?Z" by simp
      show "\<forall>g. aim_complex_lp_on_plane s g \<and>
          {x. g x \<noteq> 0} \<subseteq> Y
        \<longrightarrow>
        slp_complex_lp_norm_on s X (slp_dbar_inverse g)
            \<le> ?Z * aim_complex_lp_norm s g \<and>
        slp_complex_lp_norm_on s X (slp_partial_inverse g)
            \<le> ?Z * aim_complex_lp_norm s g"
      proof (intro allI impI)
      fix g :: slp_scalar_field
      assume hypotheses:
        "aim_complex_lp_on_plane s g \<and> {x. g x \<noteq> 0} \<subseteq> Y"
      have g_lp: "aim_complex_lp_on_plane s g" using hypotheses by blast
      note hls = K_bound[OF exponent_lower True g_lp X_measurable]
      have hls_dbar:
          "slp_complex_lp_on ?t X (slp_dbar_inverse g)"
        by (rule conjunct1[OF hls])
      have hls_partial:
          "slp_complex_lp_on ?t X (slp_partial_inverse g)"
        by (rule conjunct1[OF conjunct2[OF hls]])
      note dbar_descent = slp_complex_lp_norm_on_mono_exponent_bounded[
        where p=s and q="?t" and X=X and f="slp_dbar_inverse g",
        OF exponent_positive target_strict X_measurable X_bounded
          hls_dbar]
      note partial_descent = slp_complex_lp_norm_on_mono_exponent_bounded[
        where p=s and q="?t" and X=X and f="slp_partial_inverse g",
        OF exponent_positive target_strict X_measurable X_bounded
          hls_partial]
      have hls_sum:
          "slp_complex_lp_norm_on ?t X (slp_partial_inverse g) +
            slp_complex_lp_norm_on ?t X (slp_dbar_inverse g)
          \<le> ?H * aim_complex_lp_norm s g"
        by (rule conjunct2[OF conjunct2[OF hls]])
      have coefficient_le: "?A * ?H \<le> ?Z"
        by (rule order_trans[OF abs_ge_self]) simp
      have source_norm_nonnegative: "0 \<le> aim_complex_lp_norm s g"
        unfolding aim_complex_lp_norm_def by (rule powr_ge_zero)
      have common_bound:
          "?A * (?H * aim_complex_lp_norm s g)
            \<le> ?Z * aim_complex_lp_norm s g"
        using mult_right_mono[OF coefficient_le source_norm_nonnegative]
        by (simp add: algebra_simps)
      have scaled_hls:
          "?A * (slp_complex_lp_norm_on ?t X (slp_partial_inverse g) +
            slp_complex_lp_norm_on ?t X (slp_dbar_inverse g))
          \<le> ?A * (?H * aim_complex_lp_norm s g)"
        by (rule mult_left_mono[OF hls_sum A_nonnegative])
      have dbar_target_le_sum:
          "slp_complex_lp_norm_on ?t X (slp_dbar_inverse g) \<le>
            slp_complex_lp_norm_on ?t X (slp_partial_inverse g) +
              slp_complex_lp_norm_on ?t X (slp_dbar_inverse g)"
        by simp
      have partial_target_le_sum:
          "slp_complex_lp_norm_on ?t X (slp_partial_inverse g) \<le>
            slp_complex_lp_norm_on ?t X (slp_partial_inverse g) +
              slp_complex_lp_norm_on ?t X (slp_dbar_inverse g)"
        by simp
      have dbar_bound:
          "slp_complex_lp_norm_on s X (slp_dbar_inverse g)
            \<le> ?Z * aim_complex_lp_norm s g"
        by (rule order_trans[OF dbar_descent(2)])
          (rule order_trans[OF mult_left_mono[OF dbar_target_le_sum A_nonnegative]
            order_trans[OF scaled_hls common_bound]])
      have partial_bound:
          "slp_complex_lp_norm_on s X (slp_partial_inverse g)
            \<le> ?Z * aim_complex_lp_norm s g"
        by (rule order_trans[OF partial_descent(2)])
          (rule order_trans[OF mult_left_mono[OF partial_target_le_sum A_nonnegative]
            order_trans[OF scaled_hls common_bound]])
      show "slp_complex_lp_norm_on s X (slp_dbar_inverse g)
              \<le> ?Z * aim_complex_lp_norm s g \<and>
            slp_complex_lp_norm_on s X (slp_partial_inverse g)
              \<le> ?Z * aim_complex_lp_norm s g"
        by (rule conjI[OF dbar_bound partial_bound])
      qed
    qed
  next
    case False
    note not_below = False
    show ?thesis
    proof (cases "s = 2")
      case True
      let ?r = "3 / 2 :: real"
      let ?t = "6::real"
      let ?AY = "measure lborel ?E powr (1 / ?r - 1 / s)"
      let ?AX = "measure lborel X powr (1 / s - 1 / ?t)"
      let ?H = "K / ((?r - 1) * (2 - ?r))"
      let ?Z = "abs (?AX * ?H * ?AY) + 1"
      have r_positive: "0 < ?r" and r_lower: "1 < ?r"
        and r_upper: "?r < 2" and s_lt_t: "s < ?t"
        using True by simp_all
      have AY_nonnegative: "0 \<le> ?AY" and AX_nonnegative: "0 \<le> ?AX"
        by simp_all
      have H_nonnegative: "0 \<le> ?H"
        using K_positive by (simp add: divide_nonneg_pos)
      show ?thesis
      proof (rule exI[of _ ?Z], rule conjI)
        show "0 \<le> ?Z" by simp
        show "\<forall>g. aim_complex_lp_on_plane s g \<and>
            {x. g x \<noteq> 0} \<subseteq> Y
          \<longrightarrow>
          slp_complex_lp_norm_on s X (slp_dbar_inverse g)
              \<le> ?Z * aim_complex_lp_norm s g \<and>
          slp_complex_lp_norm_on s X (slp_partial_inverse g)
              \<le> ?Z * aim_complex_lp_norm s g"
        proof (intro allI impI)
        fix g :: slp_scalar_field
        assume hypotheses:
          "aim_complex_lp_on_plane s g \<and> {x. g x \<noteq> 0} \<subseteq> Y"
        have g_lp: "aim_complex_lp_on_plane s g" and g_carrier:
            "{x. g x \<noteq> 0} \<subseteq> Y"
          using hypotheses by blast+
        have g_local_s: "slp_complex_lp_on s ?E g"
          by (rule aim_complex_lp_on_plane_restrict[OF
                exponent_positive E_measurable g_lp])
        have r_lt_s: "?r < s" using True by simp
        note input_descent = slp_complex_lp_norm_on_mono_exponent_bounded[
          where p="?r" and q=s and X="?E" and f=g,
          OF r_positive r_lt_s E_measurable E_bounded g_local_s]
        have g_r: "aim_complex_lp_on_plane ?r g"
          using input_descent(1) carried_restriction[OF g_carrier]
          unfolding slp_complex_lp_on_def by simp
        have input_bound:
            "aim_complex_lp_norm ?r g \<le> ?AY * aim_complex_lp_norm s g"
          using input_descent(2) carried_restriction[OF g_carrier]
          unfolding slp_complex_lp_norm_on_def by simp
        note hls0 = K_bound[OF r_lower r_upper g_r X_measurable]
        have hls:
            "slp_complex_lp_on ?t X (slp_dbar_inverse g) \<and>
              slp_complex_lp_on ?t X (slp_partial_inverse g) \<and>
              slp_complex_lp_norm_on ?t X (slp_partial_inverse g) +
                slp_complex_lp_norm_on ?t X (slp_dbar_inverse g)
              \<le> ?H * aim_complex_lp_norm ?r g"
          using hls0 slp_hls_target_exponent_three_halves by simp
        have hls_dbar:
            "slp_complex_lp_on ?t X (slp_dbar_inverse g)"
          by (rule conjunct1[OF hls])
        have hls_partial:
            "slp_complex_lp_on ?t X (slp_partial_inverse g)"
          by (rule conjunct1[OF conjunct2[OF hls]])
        note dbar_descent = slp_complex_lp_norm_on_mono_exponent_bounded[
          where p=s and q="?t" and X=X and f="slp_dbar_inverse g",
          OF exponent_positive s_lt_t X_measurable X_bounded hls_dbar]
        note partial_descent = slp_complex_lp_norm_on_mono_exponent_bounded[
          where p=s and q="?t" and X=X and f="slp_partial_inverse g",
          OF exponent_positive s_lt_t X_measurable X_bounded
            hls_partial]
        have scaled_input:
            "?H * aim_complex_lp_norm ?r g \<le>
              ?H * (?AY * aim_complex_lp_norm s g)"
          by (rule mult_left_mono[OF input_bound H_nonnegative])
        have scaled_hls:
            "?AX * (slp_complex_lp_norm_on ?t X (slp_partial_inverse g) +
              slp_complex_lp_norm_on ?t X (slp_dbar_inverse g)) \<le>
              ?AX * (?H * (?AY * aim_complex_lp_norm s g))"
          by (rule order_trans[OF mult_left_mono[
                OF conjunct2[OF conjunct2[OF hls]] AX_nonnegative]
              mult_left_mono[OF scaled_input AX_nonnegative]])
        have coefficient_le: "?AX * ?H * ?AY \<le> ?Z"
          by (rule order_trans[OF abs_ge_self]) simp
        have source_norm_nonnegative: "0 \<le> aim_complex_lp_norm s g"
          unfolding aim_complex_lp_norm_def by (rule powr_ge_zero)
        have common_bound:
            "?AX * (?H * (?AY * aim_complex_lp_norm s g)) \<le>
              ?Z * aim_complex_lp_norm s g"
          using mult_right_mono[OF coefficient_le source_norm_nonnegative]
          by (simp add: algebra_simps)
        have dbar_bound:
            "slp_complex_lp_norm_on s X (slp_dbar_inverse g)
              \<le> ?Z * aim_complex_lp_norm s g"
          by (rule order_trans[OF dbar_descent(2)])
            (rule order_trans[OF mult_left_mono[OF _ AX_nonnegative]
              order_trans[OF scaled_hls common_bound]], simp)
        have partial_bound:
            "slp_complex_lp_norm_on s X (slp_partial_inverse g)
              \<le> ?Z * aim_complex_lp_norm s g"
          by (rule order_trans[OF partial_descent(2)])
            (rule order_trans[OF mult_left_mono[OF _ AX_nonnegative]
              order_trans[OF scaled_hls common_bound]], simp)
        show "slp_complex_lp_norm_on s X (slp_dbar_inverse g)
                \<le> ?Z * aim_complex_lp_norm s g \<and>
              slp_complex_lp_norm_on s X (slp_partial_inverse g)
                \<le> ?Z * aim_complex_lp_norm s g"
          by (rule conjI[OF dbar_bound partial_bound])
        qed
      qed
    next
      case False
      have s_above: "2 < s" using not_below False by linarith
      let ?r = "slp_hls_source_exponent s"
      let ?AY = "measure lborel ?E powr (1 / ?r - 1 / s)"
      let ?H = "K / ((?r - 1) * (2 - ?r))"
      let ?Z = "abs (?H * ?AY) + 1"
      have r_lower: "1 < ?r" and r_upper: "?r < 2"
        using slp_hls_source_exponent_bounds[OF s_above] by auto
      have r_positive: "0 < ?r" using r_lower by linarith
      have r_lt_s: "?r < s" using r_upper s_above by linarith
      have AY_nonnegative: "0 \<le> ?AY" by simp
      have H_nonnegative: "0 \<le> ?H"
        using K_positive r_lower r_upper by (simp add: divide_nonneg_pos)
      show ?thesis
      proof (rule exI[of _ ?Z], rule conjI)
        show "0 \<le> ?Z" by simp
        show "\<forall>g. aim_complex_lp_on_plane s g \<and>
            {x. g x \<noteq> 0} \<subseteq> Y
          \<longrightarrow>
          slp_complex_lp_norm_on s X (slp_dbar_inverse g)
              \<le> ?Z * aim_complex_lp_norm s g \<and>
          slp_complex_lp_norm_on s X (slp_partial_inverse g)
              \<le> ?Z * aim_complex_lp_norm s g"
        proof (intro allI impI)
        fix g :: slp_scalar_field
        assume hypotheses:
          "aim_complex_lp_on_plane s g \<and> {x. g x \<noteq> 0} \<subseteq> Y"
        have g_lp: "aim_complex_lp_on_plane s g" and g_carrier:
            "{x. g x \<noteq> 0} \<subseteq> Y"
          using hypotheses by blast+
        have g_local_s: "slp_complex_lp_on s ?E g"
          by (rule aim_complex_lp_on_plane_restrict[OF
                exponent_positive E_measurable g_lp])
        note input_descent = slp_complex_lp_norm_on_mono_exponent_bounded[
          where p="?r" and q=s and X="?E" and f=g,
          OF r_positive r_lt_s E_measurable E_bounded g_local_s]
        have g_r: "aim_complex_lp_on_plane ?r g"
          using input_descent(1) carried_restriction[OF g_carrier]
          unfolding slp_complex_lp_on_def by simp
        have input_bound:
            "aim_complex_lp_norm ?r g \<le> ?AY * aim_complex_lp_norm s g"
          using input_descent(2) carried_restriction[OF g_carrier]
          unfolding slp_complex_lp_norm_on_def by simp
        note hls0 = K_bound[OF r_lower r_upper g_r X_measurable]
        have hls:
            "slp_complex_lp_on s X (slp_dbar_inverse g) \<and>
              slp_complex_lp_on s X (slp_partial_inverse g) \<and>
              slp_complex_lp_norm_on s X (slp_partial_inverse g) +
                slp_complex_lp_norm_on s X (slp_dbar_inverse g)
              \<le> ?H * aim_complex_lp_norm ?r g"
          using hls0 slp_hls_source_target_identity[OF s_above] by simp
        have scaled_input:
            "?H * aim_complex_lp_norm ?r g \<le>
              ?H * (?AY * aim_complex_lp_norm s g)"
          by (rule mult_left_mono[OF input_bound H_nonnegative])
        have coefficient_le: "?H * ?AY \<le> ?Z"
          by (rule order_trans[OF abs_ge_self]) simp
        have source_norm_nonnegative: "0 \<le> aim_complex_lp_norm s g"
          unfolding aim_complex_lp_norm_def by (rule powr_ge_zero)
        have common_bound:
            "?H * (?AY * aim_complex_lp_norm s g) \<le>
              ?Z * aim_complex_lp_norm s g"
          using mult_right_mono[OF coefficient_le source_norm_nonnegative]
          by (simp add: algebra_simps)
        have dbar_bound:
            "slp_complex_lp_norm_on s X (slp_dbar_inverse g)
              \<le> ?Z * aim_complex_lp_norm s g"
          by (rule order_trans[OF _ order_trans[
                OF conjunct2[OF conjunct2[OF hls]]
                  order_trans[OF scaled_input common_bound]]], simp)
        have partial_bound:
            "slp_complex_lp_norm_on s X (slp_partial_inverse g)
              \<le> ?Z * aim_complex_lp_norm s g"
          by (rule order_trans[OF _ order_trans[
                OF conjunct2[OF conjunct2[OF hls]]
                  order_trans[OF scaled_input common_bound]]], simp)
        show "slp_complex_lp_norm_on s X (slp_dbar_inverse g)
                \<le> ?Z * aim_complex_lp_norm s g \<and>
              slp_complex_lp_norm_on s X (slp_partial_inverse g)
                \<le> ?Z * aim_complex_lp_norm s g"
          by (rule conjI[OF dbar_bound partial_bound])
        qed
      qed
    qed
  qed
  obtain Z :: real where Z_nonnegative: "0 \<le> Z"
    and zero_order:
      "\<And>g. aim_complex_lp_on_plane s g \<Longrightarrow>
        {x. g x \<noteq> 0} \<subseteq> Y \<Longrightarrow>
        slp_complex_lp_norm_on s X (slp_dbar_inverse g)
            \<le> Z * aim_complex_lp_norm s g \<and>
        slp_complex_lp_norm_on s X (slp_partial_inverse g)
            \<le> Z * aim_complex_lp_norm s g"
    using zero_order_package by blast
  obtain S :: real where S_positive: "0 < S"
    and both_beurling:
      "\<And>g. aim_complex_lp_on_plane s g \<Longrightarrow>
        (AE z in lborel. slp_beurling_pv_exists g z) \<and>
        aim_complex_lp_on_plane s (slp_beurling_transform g) \<and>
        aim_complex_lp_norm s (slp_beurling_transform g)
          \<le> S * aim_complex_lp_norm s g \<and>
        (AE z in lborel. slp_opposite_beurling_pv_exists g z) \<and>
        aim_complex_lp_on_plane s (slp_opposite_beurling_transform g) \<and>
        aim_complex_lp_norm s (slp_opposite_beurling_transform g)
          \<le> S * aim_complex_lp_norm s g"
    using slp_both_beurling_lp exponent_lower by blast
  let ?C = "4 * (Z + 8 * (1 + S)) + 1"
  have C_positive: "0 < ?C"
  proof -
    have one_plus_S_nonnegative: "0 \<le> 1 + S"
      using S_positive by linarith
    have eight_nonnegative: "0 \<le> 8 * (1 + S)"
      by (rule mult_nonneg_nonneg) (simp_all add: one_plus_S_nonnegative)
    have inner_nonnegative: "0 \<le> Z + 8 * (1 + S)"
      by (rule add_nonneg_nonneg[OF Z_nonnegative eight_nonnegative])
    have four_nonnegative: "0 \<le> (4::real)"
      by simp
    have scaled_nonnegative: "0 \<le> 4 * (Z + 8 * (1 + S))"
      by (rule mult_nonneg_nonneg[OF four_nonnegative inner_nonnegative])
    show ?thesis using scaled_nonnegative by linarith
  qed
  have final_bound:
      "slp_w1p_norm_on s X
          (slp_dbar_inverse (slp_oscillatory_modulation (- tau) c source))
          (slp_dbar_inverse_gradient
            (slp_oscillatory_modulation (- tau) c source))
          \<le> ?C * aim_complex_lp_norm s source \<and>
        slp_w1p_norm_on s X
          (slp_partial_inverse (slp_oscillatory_modulation (- tau) c source))
          (slp_partial_inverse_gradient
            (slp_oscillatory_modulation (- tau) c source))
          \<le> ?C * aim_complex_lp_norm s source"
    if source_lp: "aim_complex_lp_on_plane s source"
      and source_carrier: "{x. source x \<noteq> 0} \<subseteq> Y"
    for tau :: real and c :: slp_point and source :: slp_scalar_field
  proof -
    let ?g = "slp_oscillatory_modulation (- tau) c source"
    let ?N = "aim_complex_lp_norm s ?g"
    let ?D = "4 * (1 + S)"
    have g_lp: "aim_complex_lp_on_plane s ?g" using source_lp by simp
    have g_carrier: "{x. ?g x \<noteq> 0} \<subseteq> Y"
      using source_carrier by simp
    have g_support: "bounded {x. ?g x \<noteq> 0}"
      by (rule bounded_subset[OF Y_bounded g_carrier])
    note zero = zero_order[OF g_lp g_carrier]
    note beurling = both_beurling[OF g_lp]
    have direct_lp: "aim_complex_lp_on_plane s (slp_beurling_transform ?g)"
      using beurling by blast
    have direct_bound:
        "aim_complex_lp_norm s (slp_beurling_transform ?g) \<le> S * ?N"
      using beurling by blast
    have opposite_lp:
        "aim_complex_lp_on_plane s (slp_opposite_beurling_transform ?g)"
      using beurling by blast
    have opposite_bound:
        "aim_complex_lp_norm s (slp_opposite_beurling_transform ?g) \<le> S * ?N"
      using beurling by blast
    note dbar_add = slp_complex_lp_add_norm_coarse_triangle[
      OF exponent_one_le g_lp direct_lp]
    note dbar_diff = slp_complex_lp_diff_norm_coarse_triangle[
      OF exponent_one_le direct_lp g_lp]
    note partial_add = slp_complex_lp_add_norm_coarse_triangle[
      OF exponent_one_le g_lp opposite_lp]
    note partial_diff = slp_complex_lp_diff_norm_coarse_triangle[
      OF exponent_one_le g_lp opposite_lp]
    have dbar_zero_lp:
        "aim_complex_lp_on_plane s
          (\<lambda>x. slp_dbar_inverse_gradient ?g x $ 0)"
      using dbar_add(1) by simp
    have dbar_one_lp:
        "aim_complex_lp_on_plane s
          (\<lambda>x. slp_dbar_inverse_gradient ?g x $ 1)"
      using aim_complex_lp_on_plane_cmult_unit[
        where c="\<i>" and f="\<lambda>x. slp_beurling_transform ?g x - ?g x",
        OF _ dbar_diff(1)] by simp
    have partial_zero_lp:
        "aim_complex_lp_on_plane s
          (\<lambda>x. slp_partial_inverse_gradient ?g x $ 0)"
      using partial_add(1) by simp
    have partial_one_lp:
        "aim_complex_lp_on_plane s
          (\<lambda>x. slp_partial_inverse_gradient ?g x $ 1)"
      using aim_complex_lp_on_plane_cmult_unit[
        where c="\<i>" and f="\<lambda>x. ?g x - slp_opposite_beurling_transform ?g x",
        OF _ partial_diff(1)] by simp
    have N_nonnegative: "0 \<le> ?N"
      unfolding aim_complex_lp_norm_def by (rule powr_ge_zero)
    have dbar_zero_global:
        "aim_complex_lp_norm s (\<lambda>x. slp_dbar_inverse_gradient ?g x $ 0)
          \<le> ?D * ?N"
      using dbar_add(2) direct_bound
      by (simp add: algebra_simps)
    have dbar_one_global:
        "aim_complex_lp_norm s (\<lambda>x. slp_dbar_inverse_gradient ?g x $ 1)
          \<le> ?D * ?N"
    proof -
      have unit_norm:
          "aim_complex_lp_norm s (\<lambda>x. slp_dbar_inverse_gradient ?g x $ 1) =
            aim_complex_lp_norm s
              (\<lambda>x. slp_beurling_transform ?g x - ?g x)"
        by (simp add: aim_complex_lp_norm_def norm_mult)
      show ?thesis
        unfolding unit_norm
        using dbar_diff(2) direct_bound N_nonnegative
        by (simp add: algebra_simps; linarith)
    qed
    have partial_zero_global:
        "aim_complex_lp_norm s (\<lambda>x. slp_partial_inverse_gradient ?g x $ 0)
          \<le> ?D * ?N"
      using partial_add(2) opposite_bound
      by (simp add: algebra_simps)
    have partial_one_global:
        "aim_complex_lp_norm s (\<lambda>x. slp_partial_inverse_gradient ?g x $ 1)
          \<le> ?D * ?N"
    proof -
      have unit_norm:
          "aim_complex_lp_norm s (\<lambda>x. slp_partial_inverse_gradient ?g x $ 1) =
            aim_complex_lp_norm s
              (\<lambda>x. ?g x - slp_opposite_beurling_transform ?g x)"
        by (simp add: aim_complex_lp_norm_def norm_mult)
      show ?thesis
        unfolding unit_norm
        using partial_diff(2) opposite_bound N_nonnegative
        by (simp add: algebra_simps; linarith)
    qed
    have dbar_zero_restriction:
        "aim_complex_lp_norm s
            (slp_restrict_field X (\<lambda>x. slp_dbar_inverse_gradient ?g x $ 0))
          \<le> aim_complex_lp_norm s
            (\<lambda>x. slp_dbar_inverse_gradient ?g x $ 0)"
      using slp_complex_lp_norm_on_le[
        OF exponent_positive X_measurable dbar_zero_lp]
      by (simp add: slp_complex_lp_norm_on_def)
    have dbar_one_restriction:
        "aim_complex_lp_norm s
            (slp_restrict_field X (\<lambda>x. slp_dbar_inverse_gradient ?g x $ 1))
          \<le> aim_complex_lp_norm s
            (\<lambda>x. slp_dbar_inverse_gradient ?g x $ 1)"
      using slp_complex_lp_norm_on_le[
        OF exponent_positive X_measurable dbar_one_lp]
      by (simp add: slp_complex_lp_norm_on_def)
    have partial_zero_restriction:
        "aim_complex_lp_norm s
            (slp_restrict_field X (\<lambda>x. slp_partial_inverse_gradient ?g x $ 0))
          \<le> aim_complex_lp_norm s
            (\<lambda>x. slp_partial_inverse_gradient ?g x $ 0)"
      using slp_complex_lp_norm_on_le[
        OF exponent_positive X_measurable partial_zero_lp]
      by (simp add: slp_complex_lp_norm_on_def)
    have partial_one_restriction:
        "aim_complex_lp_norm s
            (slp_restrict_field X (\<lambda>x. slp_partial_inverse_gradient ?g x $ 1))
          \<le> aim_complex_lp_norm s
            (\<lambda>x. slp_partial_inverse_gradient ?g x $ 1)"
      using slp_complex_lp_norm_on_le[
        OF exponent_positive X_measurable partial_one_lp]
      by (simp add: slp_complex_lp_norm_on_def)
    have dbar_zero_local:
        "aim_complex_lp_norm s
            (slp_restrict_field X (\<lambda>x. slp_dbar_inverse_gradient ?g x $ 0))
          \<le> ?D * ?N"
      by (rule order_trans[OF dbar_zero_restriction dbar_zero_global])
    have dbar_one_local:
        "aim_complex_lp_norm s
            (slp_restrict_field X (\<lambda>x. slp_dbar_inverse_gradient ?g x $ 1))
          \<le> ?D * ?N"
      by (rule order_trans[OF dbar_one_restriction dbar_one_global])
    have partial_zero_local:
        "aim_complex_lp_norm s
            (slp_restrict_field X (\<lambda>x. slp_partial_inverse_gradient ?g x $ 0))
          \<le> ?D * ?N"
      by (rule order_trans[OF partial_zero_restriction partial_zero_global])
    have partial_one_local:
        "aim_complex_lp_norm s
            (slp_restrict_field X (\<lambda>x. slp_partial_inverse_gradient ?g x $ 1))
          \<le> ?D * ?N"
      by (rule order_trans[OF partial_one_restriction partial_one_global])
    have certificates:
        "slp_local_w1s_certificate s X
            (slp_dbar_inverse ?g) (slp_dbar_inverse_gradient ?g) \<and>
          slp_local_w1s_certificate s X
            (slp_partial_inverse ?g) (slp_partial_inverse_gradient ?g)"
      by (rule slp_both_cauchy_local_w1s_certificates[OF
            exponent_lower g_lp g_support X_measurable X_bounded])
    have dbar_pair:
        "slp_w1p_pair_on s X
          (slp_dbar_inverse ?g) (slp_dbar_inverse_gradient ?g)"
      by (rule slp_local_w1s_certificate_w1p_pair_on)
        (rule conjunct1[OF certificates])
    have partial_pair:
        "slp_w1p_pair_on s X
          (slp_partial_inverse ?g) (slp_partial_inverse_gradient ?g)"
      by (rule slp_local_w1s_certificate_w1p_pair_on)
        (rule conjunct2[OF certificates])
    have dbar_base:
        "aim_complex_lp_norm s (slp_restrict_field X (slp_dbar_inverse ?g))
          \<le> Z * ?N"
      using conjunct1[OF zero]
      by (simp add: slp_complex_lp_norm_on_def)
    have partial_base:
        "aim_complex_lp_norm s (slp_restrict_field X (slp_partial_inverse ?g))
          \<le> Z * ?N"
      using conjunct2[OF zero]
      by (simp add: slp_complex_lp_norm_on_def)
    have dbar_component_sum:
        "aim_complex_lp_norm s (slp_restrict_field X (slp_dbar_inverse ?g)) +
            aim_complex_lp_norm s
              (slp_restrict_field X
                (\<lambda>x. slp_dbar_inverse_gradient ?g x $ 0)) +
            aim_complex_lp_norm s
              (slp_restrict_field X
                (\<lambda>x. slp_dbar_inverse_gradient ?g x $ 1))
          \<le> Z * ?N + ?D * ?N + ?D * ?N"
      using dbar_base dbar_zero_local dbar_one_local by linarith
    have partial_component_sum:
        "aim_complex_lp_norm s (slp_restrict_field X (slp_partial_inverse ?g)) +
            aim_complex_lp_norm s
              (slp_restrict_field X
                (\<lambda>x. slp_partial_inverse_gradient ?g x $ 0)) +
            aim_complex_lp_norm s
              (slp_restrict_field X
                (\<lambda>x. slp_partial_inverse_gradient ?g x $ 1))
          \<le> Z * ?N + ?D * ?N + ?D * ?N"
      using partial_base partial_zero_local partial_one_local by linarith
    have dbar_graph0:
        "slp_w1p_norm_on s X
            (slp_dbar_inverse ?g) (slp_dbar_inverse_gradient ?g)
          \<le> 4 * (Z * ?N + ?D * ?N + ?D * ?N)"
      by (rule order_trans[OF slp_w1p_norm_on_component_sum_bound[
            OF exponent_one_le dbar_pair]])
        (rule mult_left_mono[OF dbar_component_sum], simp)
    have partial_graph0:
        "slp_w1p_norm_on s X
            (slp_partial_inverse ?g) (slp_partial_inverse_gradient ?g)
          \<le> 4 * (Z * ?N + ?D * ?N + ?D * ?N)"
      by (rule order_trans[OF slp_w1p_norm_on_component_sum_bound[
            OF exponent_one_le partial_pair]])
        (rule mult_left_mono[OF partial_component_sum], simp)
    have graph_coefficient:
        "4 * (Z * ?N + ?D * ?N + ?D * ?N) =
          (4 * (Z + 8 * (1 + S))) * ?N"
      by (simp add: algebra_simps)
    have coefficient_le: "4 * (Z + 8 * (1 + S)) \<le> ?C" by simp
    have dbar_graph:
        "slp_w1p_norm_on s X
            (slp_dbar_inverse ?g) (slp_dbar_inverse_gradient ?g)
          \<le> ?C * ?N"
      using dbar_graph0 graph_coefficient
        mult_right_mono[OF coefficient_le N_nonnegative] by linarith
    have partial_graph:
        "slp_w1p_norm_on s X
            (slp_partial_inverse ?g) (slp_partial_inverse_gradient ?g)
          \<le> ?C * ?N"
      using partial_graph0 graph_coefficient
        mult_right_mono[OF coefficient_le N_nonnegative] by linarith
    show ?thesis
      using dbar_graph partial_graph source_lp
      by simp
  qed
  show ?thesis
    by (rule exI[of _ ?C], rule conjI[OF C_positive])
      (intro allI impI, elim conjE,
       unfold slp_dbar_psi_inverse_def slp_partial_psi_inverse_def,
       rule final_bound)
qed

end

end
