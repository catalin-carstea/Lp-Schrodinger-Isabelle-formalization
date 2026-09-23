theory Inverse_Schrodinger_Lp_Quantitative_Value_Split_Moments
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Interpolation_Exponent_Selection"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Quantitative low/high value decomposition of planar Lp fields\<close>

definition slp_value_low_part ::
    "real \<Rightarrow> slp_scalar_field \<Rightarrow> slp_scalar_field"
  where
    "slp_value_low_part T f =
      (\<lambda>x. if norm (f x) \<le> T then f x else 0)"

definition slp_value_high_part ::
    "real \<Rightarrow> slp_scalar_field \<Rightarrow> slp_scalar_field"
  where
    "slp_value_high_part T f =
      (\<lambda>x. f x - slp_value_low_part T f x)"

theorem slp_quantitative_value_split_moment_bounds:
  fixes p a b T :: real and f :: slp_scalar_field
  assumes a_positive: "0 < a"
    and a_below_p: "a < p"
    and p_below_b: "p < b"
    and threshold_positive: "0 < T"
    and field_lp: "aim_complex_lp_on_plane p f"
  shows
    "(\<forall>x. f x =
        slp_value_low_part T f x + slp_value_high_part T f x)
      \<and> aim_complex_lp_on_plane a (slp_value_high_part T f)
      \<and> aim_complex_lp_on_plane b (slp_value_low_part T f)
      \<and> integral\<^sup>L lborel
          (\<lambda>x. norm (slp_value_high_part T f x) powr a)
        \<le> T powr (a - p) *
          integral\<^sup>L lborel (\<lambda>x. norm (f x) powr p)
      \<and> integral\<^sup>L lborel
          (\<lambda>x. norm (slp_value_low_part T f x) powr b)
        \<le> T powr (b - p) *
          integral\<^sup>L lborel (\<lambda>x. norm (f x) powr p)"
proof -
  have p_positive: "0 < p"
    using a_positive a_below_p by linarith
  have b_positive: "0 < b"
    using p_positive p_below_b by linarith
  have high_exponent_nonpositive: "a - p \<le> 0"
    using a_below_p by linarith
  have low_exponent_nonnegative: "0 \<le> b - p"
    using p_below_b by linarith
  have field_measurable: "f \<in> borel_measurable lborel"
    and p_weight_integrable:
      "integrable lborel (\<lambda>x. norm (f x) powr p)"
    using field_lp unfolding aim_complex_lp_on_plane_def by blast+

  let ?low = "slp_value_low_part T f"
  let ?high = "slp_value_high_part T f"
  let ?p_weight = "\<lambda>x. norm (f x) powr p"
  let ?high_weight = "\<lambda>x. norm (?high x) powr a"
  let ?low_weight = "\<lambda>x. norm (?low x) powr b"
  let ?high_majorant = "\<lambda>x. T powr (a - p) * ?p_weight x"
  let ?low_majorant = "\<lambda>x. T powr (b - p) * ?p_weight x"

  have split_identity: "f x = ?low x + ?high x" for x
    unfolding slp_value_high_part_def by simp
  have low_measurable: "?low \<in> borel_measurable lborel"
    unfolding slp_value_low_part_def using field_measurable by measurable
  have high_measurable: "?high \<in> borel_measurable lborel"
    unfolding slp_value_high_part_def using field_measurable low_measurable
    by measurable

  have high_pointwise:
      "?high_weight x \<le> ?high_majorant x" for x
  proof (cases "norm (f x) \<le> T")
    case True
    then show ?thesis
      unfolding slp_value_high_part_def slp_value_low_part_def
      by simp
  next
    case False
    have threshold_below: "T \<le> norm (f x)"
      using False by linarith
    have negative_power_bound:
        "norm (f x) powr (a - p) \<le> T powr (a - p)"
      by (rule powr_mono2'[OF high_exponent_nonpositive
            threshold_positive threshold_below])
    have high_at_x: "?high x = f x"
      using False unfolding slp_value_high_part_def slp_value_low_part_def
      by simp
    have high_power_split:
        "?high_weight x =
          norm (f x) powr p * norm (f x) powr (a - p)"
      unfolding high_at_x by (subst powr_add[symmetric]) simp
    have multiplied_bound:
        "norm (f x) powr p * norm (f x) powr (a - p) \<le>
          norm (f x) powr p * T powr (a - p)"
      by (rule mult_left_mono[OF negative_power_bound]) simp
    show ?thesis
      using high_power_split multiplied_bound by (simp add: mult.commute)
  qed

  have low_pointwise:
      "?low_weight x \<le> ?low_majorant x" for x
  proof (cases "norm (f x) \<le> T")
    case True
    have nonnegative_norm: "0 \<le> norm (f x)"
      by simp
    have positive_power_bound:
        "norm (f x) powr (b - p) \<le> T powr (b - p)"
      by (rule powr_mono2[OF low_exponent_nonnegative
            nonnegative_norm True])
    have low_at_x: "?low x = f x"
      using True unfolding slp_value_low_part_def by simp
    have low_power_split:
        "?low_weight x =
          norm (f x) powr p * norm (f x) powr (b - p)"
      unfolding low_at_x by (subst powr_add[symmetric]) simp
    have multiplied_bound:
        "norm (f x) powr p * norm (f x) powr (b - p) \<le>
          norm (f x) powr p * T powr (b - p)"
      by (rule mult_left_mono[OF positive_power_bound]) simp
    show ?thesis
      using low_power_split multiplied_bound by (simp add: mult.commute)
  next
    case False
    then show ?thesis
      unfolding slp_value_low_part_def by simp
  qed

  have high_weight_measurable:
      "?high_weight \<in> borel_measurable lborel"
    using high_measurable by measurable
  have low_weight_measurable:
      "?low_weight \<in> borel_measurable lborel"
    using low_measurable by measurable
  have high_majorant_integrable:
      "integrable lborel ?high_majorant"
    by (rule Bochner_Integration.integrable_mult_right)
       (rule p_weight_integrable)
  have low_majorant_integrable:
      "integrable lborel ?low_majorant"
    by (rule Bochner_Integration.integrable_mult_right)
       (rule p_weight_integrable)
  have high_weight_integrable:
      "integrable lborel ?high_weight"
  proof (rule Bochner_Integration.integrable_bound[OF high_majorant_integrable
        high_weight_measurable])
    show "AE x in lborel. norm (?high_weight x) \<le>
        norm (?high_majorant x)"
      by (rule AE_I2) (simp add: high_pointwise)
  qed
  have low_weight_integrable:
      "integrable lborel ?low_weight"
  proof (rule Bochner_Integration.integrable_bound[OF low_majorant_integrable
        low_weight_measurable])
    show "AE x in lborel. norm (?low_weight x) \<le>
        norm (?low_majorant x)"
      by (rule AE_I2) (simp add: low_pointwise)
  qed

  have high_lp: "aim_complex_lp_on_plane a ?high"
    unfolding aim_complex_lp_on_plane_def
    using high_measurable high_weight_integrable by blast
  have low_lp: "aim_complex_lp_on_plane b ?low"
    unfolding aim_complex_lp_on_plane_def
    using low_measurable low_weight_integrable by blast

  have high_integral_bound:
      "integral\<^sup>L lborel ?high_weight \<le>
        integral\<^sup>L lborel ?high_majorant"
    by (rule integral_mono_AE[OF high_weight_integrable
          high_majorant_integrable])
       (rule AE_I2, rule high_pointwise)
  have low_integral_bound:
      "integral\<^sup>L lborel ?low_weight \<le>
        integral\<^sup>L lborel ?low_majorant"
    by (rule integral_mono_AE[OF low_weight_integrable
          low_majorant_integrable])
       (rule AE_I2, rule low_pointwise)
  have high_moment_bound:
      "integral\<^sup>L lborel ?high_weight \<le>
        T powr (a - p) * integral\<^sup>L lborel ?p_weight"
    using high_integral_bound by simp
  have low_moment_bound:
      "integral\<^sup>L lborel ?low_weight \<le>
        T powr (b - p) * integral\<^sup>L lborel ?p_weight"
    using low_integral_bound by simp

  show ?thesis
    using split_identity high_lp low_lp high_moment_bound low_moment_bound
    by blast
qed

end
