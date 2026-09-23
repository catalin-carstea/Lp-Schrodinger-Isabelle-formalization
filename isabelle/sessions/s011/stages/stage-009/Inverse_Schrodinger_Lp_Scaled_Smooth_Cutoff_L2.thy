theory Inverse_Schrodinger_Lp_Scaled_Smooth_Cutoff_L2
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Smooth_Cutoff_Profile"
    "HOL-Analysis.Ball_Volume"
begin

section \<open>Positive-power mass of the canonical scaled cutoff\<close>

definition slp_global_scaled_cutoff ::
  "real \<Rightarrow> slp_point \<Rightarrow> slp_point \<Rightarrow> real"
where
  "slp_global_scaled_cutoff delta c z =
    slp_global_cutoff.slp_scaled_cutoff delta c z"

definition slp_global_scaled_cutoff_power ::
  "real \<Rightarrow> real \<Rightarrow> slp_point \<Rightarrow>
    slp_point \<Rightarrow> real"
where
  "slp_global_scaled_cutoff_power q delta c z =
    norm (slp_global_scaled_cutoff delta c z) powr q"

lemma slp_global_scaled_cutoff_borel_measurable [measurable]:
  "slp_global_scaled_cutoff delta c \<in> borel_measurable lborel"
proof -
  have cutoff_derivative:
      "((slp_global_scaled_cutoff delta c) has_derivative
        slp_global_cutoff.slp_scaled_cutoff_derivative delta c z) (at z)"
    for z
    unfolding slp_global_scaled_cutoff_def
    by (rule slp_global_cutoff.slp_scaled_cutoff_has_derivative)
  have continuous_cutoff:
      "continuous_on UNIV (slp_global_scaled_cutoff delta c)"
  proof (rule continuous_at_imp_continuous_on)
    show "\<forall>z \<in> UNIV. isCont (slp_global_scaled_cutoff delta c) z"
      by (intro ballI has_derivative_continuous[OF cutoff_derivative])
  qed
  have borel:
      "slp_global_scaled_cutoff delta c \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF continuous_cutoff])
  show ?thesis
  proof (rule borel_measurable_subalgebra[where N=borel])
    show "sets borel \<subseteq> sets (lborel :: slp_point measure)"
      by simp
    show "space borel = space (lborel :: slp_point measure)"
      by simp
    show "slp_global_scaled_cutoff delta c \<in> borel_measurable borel"
      by (rule borel)
  qed
qed

lemma slp_global_scaled_cutoff_power_borel_measurable [measurable]:
  "slp_global_scaled_cutoff_power q delta c \<in>
    borel_measurable lborel"
  unfolding slp_global_scaled_cutoff_power_def by measurable

lemma slp_global_scaled_cutoff_power_nonnegative [simp]:
  "0 \<le> slp_global_scaled_cutoff_power q delta c z"
  unfolding slp_global_scaled_cutoff_power_def by simp

lemma slp_global_scaled_cutoff_power_indicator_bound:
  assumes delta_positive: "0 < delta"
    and q_positive: "0 < q"
  shows
    "slp_global_scaled_cutoff_power q delta c z \<le>
      indicator (cball c (2 * delta)) z"
proof (cases "z \<in> cball c (2 * delta)")
  case True
  have cutoff_bound:
      "norm (slp_global_scaled_cutoff delta c z) \<le> 1"
    unfolding slp_global_scaled_cutoff_def
    by (rule slp_global_cutoff.slp_scaled_cutoff_norm)
  have
      "norm (slp_global_scaled_cutoff delta c z) powr q \<le>
        (1 :: real) powr q"
    by (rule powr_mono2)
      (use q_positive cutoff_bound in auto)
  with True show ?thesis
    by (simp add: slp_global_scaled_cutoff_power_def)
next
  case False
  have outside: "2 * delta \<le> norm (z - c)"
    using False by (simp add: dist_norm norm_minus_commute)
  have cutoff_zero: "slp_global_scaled_cutoff delta c z = 0"
    unfolding slp_global_scaled_cutoff_def
    by (rule slp_global_cutoff.slp_scaled_cutoff_outer[
          OF delta_positive outside])
  with False q_positive show ?thesis
    by (simp add: slp_global_scaled_cutoff_power_def)
qed

theorem slp_global_scaled_cutoff_power_integrable:
  assumes delta_positive: "0 < delta"
    and q_positive: "0 < q"
  shows
    "integrable lborel (slp_global_scaled_cutoff_power q delta c)"
proof -
  let ?ball = "cball c (2 * delta)"
  have ball_measurable: "?ball \<in> sets (lborel :: slp_point measure)"
    by measurable
  have ball_finite: "emeasure lborel ?ball < \<infinity>"
    by (rule emeasure_lborel_cball_finite)
  have majorant_integrable:
      "integrable lborel (indicator ?ball :: slp_point \<Rightarrow> real)"
    by (rule integrable_real_indicator[OF ball_measurable ball_finite])
  have power_measurable:
      "slp_global_scaled_cutoff_power q delta c \<in>
        borel_measurable lborel"
    by measurable
  show ?thesis
  proof (rule Bochner_Integration.integrable_bound[
      OF majorant_integrable power_measurable])
    show "AE z in lborel.
        norm (slp_global_scaled_cutoff_power q delta c z) \<le>
        norm (indicator ?ball z :: real)"
      using slp_global_scaled_cutoff_power_indicator_bound[
        OF delta_positive q_positive]
      by (auto simp: indicator_def)
  qed
qed

theorem slp_global_scaled_cutoff_power_integral_le_ball:
  assumes delta_positive: "0 < delta"
    and q_positive: "0 < q"
  shows
    "integral\<^sup>L lborel
        (slp_global_scaled_cutoff_power q delta c) \<le>
      pi * (2 * delta) ^ 2"
proof -
  let ?ball = "cball c (2 * delta)"
  have power_integrable:
      "integrable lborel (slp_global_scaled_cutoff_power q delta c)"
    by (rule slp_global_scaled_cutoff_power_integrable[
          OF delta_positive q_positive])
  have ball_measurable: "?ball \<in> sets (lborel :: slp_point measure)"
    by measurable
  have ball_finite: "emeasure lborel ?ball < \<infinity>"
    by (rule emeasure_lborel_cball_finite)
  have majorant_integrable:
      "integrable lborel (indicator ?ball :: slp_point \<Rightarrow> real)"
    by (rule integrable_real_indicator[OF ball_measurable ball_finite])
  have integral_le:
      "integral\<^sup>L lborel
          (slp_global_scaled_cutoff_power q delta c) \<le>
        integral\<^sup>L lborel
          (indicator ?ball :: slp_point \<Rightarrow> real)"
    by (rule Bochner_Integration.integral_mono[
          OF power_integrable majorant_integrable])
      (use slp_global_scaled_cutoff_power_indicator_bound[
          OF delta_positive q_positive] in auto)
  have ball_measure:
      "measure lborel ?ball = pi * (2 * delta) ^ 2"
    using content_cball[where c=c and r="2 * delta"] delta_positive
    by (simp add: content_def unit_ball_vol_2)
  have majorant_integral:
      "integral\<^sup>L lborel
        (indicator ?ball :: slp_point \<Rightarrow> real) =
        pi * (2 * delta) ^ 2"
    using ball_measure by simp
  show ?thesis
    using integral_le majorant_integral by simp
qed

theorem slp_global_scaled_cutoff_L2_root_le:
  assumes delta_positive: "0 < delta"
  shows
    "(integral\<^sup>L lborel
        (slp_global_scaled_cutoff_power 2 delta c)) powr (1 / 2) \<le>
      2 * sqrt pi * delta"
proof -
  have integral_nonnegative:
      "0 \<le> integral\<^sup>L lborel
        (slp_global_scaled_cutoff_power 2 delta c)"
    by (rule Bochner_Integration.integral_nonneg) simp
  have integral_le:
      "integral\<^sup>L lborel
          (slp_global_scaled_cutoff_power 2 delta c) \<le>
        pi * (2 * delta) ^ 2"
    by (rule slp_global_scaled_cutoff_power_integral_le_ball[
          OF delta_positive]) simp
  have volume_nonnegative: "0 \<le> pi * (2 * delta) ^ 2"
    by (rule mult_nonneg_nonneg) simp_all
  have root_le:
      "(integral\<^sup>L lborel
          (slp_global_scaled_cutoff_power 2 delta c)) powr (1 / 2) \<le>
        (pi * (2 * delta) ^ 2) powr (1 / 2)"
    by (rule powr_mono2)
      (use integral_nonnegative integral_le in auto)
  have volume_root:
      "(pi * (2 * delta) ^ 2) powr (1 / 2) =
        2 * sqrt pi * delta"
  proof -
    have two_delta_nonnegative: "0 \<le> 2 * delta"
      using delta_positive by simp
    have sqrt_two_delta_square:
        "sqrt ((2 * delta) ^ 2) = 2 * delta"
    proof -
      have "sqrt ((2 * delta) ^ 2) = \<bar>2 * delta\<bar>"
        by (rule real_sqrt_abs)
      also have "... = 2 * delta"
        by (rule abs_of_nonneg[OF two_delta_nonnegative])
      finally show ?thesis .
    qed
    have
        "(pi * (2 * delta) ^ 2) powr (1 / 2) =
          sqrt (pi * (2 * delta) ^ 2)"
      by (rule powr_half_sqrt[OF volume_nonnegative])
    also have "... = sqrt pi * sqrt ((2 * delta) ^ 2)"
      by (rule real_sqrt_mult)
    also have "... = sqrt pi * (2 * delta)"
      by (simp only: sqrt_two_delta_square)
    also have "... = 2 * sqrt pi * delta"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  show ?thesis
    using root_le volume_root by simp
qed

end
