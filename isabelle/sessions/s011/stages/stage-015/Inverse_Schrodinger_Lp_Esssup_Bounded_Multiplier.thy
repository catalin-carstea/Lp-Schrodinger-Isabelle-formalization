theory Inverse_Schrodinger_Lp_Esssup_Bounded_Multiplier
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_W1p_Rough_Zero_Extended_Esssup_Natural_Log_Bound"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Almost-everywhere bounded multipliers on complex planar Lp\<close>

theorem slp_complex_lp_AE_bounded_multiplier:
  fixes multiplier f :: slp_scalar_field
  assumes exponent_positive: "0 < p"
    and multiplier_measurable:
      "multiplier \<in> borel_measurable lborel"
    and multiplier_bound:
      "AE x in lborel. norm (multiplier x) \<le> C"
    and bound_nonnegative: "0 \<le> C"
    and function_lp: "aim_complex_lp_on_plane p f"
  shows AE_product_lp:
      "aim_complex_lp_on_plane p (\<lambda>x. multiplier x * f x)"
    and AE_product_norm_bound:
      "aim_complex_lp_norm p (\<lambda>x. multiplier x * f x) \<le>
        C * aim_complex_lp_norm p f"
proof -
  have function_measurable: "f \<in> borel_measurable lborel"
    and function_power_integrable:
      "integrable lborel (\<lambda>x. norm (f x) powr p)"
    using function_lp unfolding aim_complex_lp_on_plane_def by blast+
  let ?T = "\<lambda>x. multiplier x * f x"
  let ?u = "\<lambda>x. norm (?T x)"
  let ?v = "\<lambda>x. C * norm (f x)"
  have target_measurable: "?T \<in> borel_measurable lborel"
    using multiplier_measurable function_measurable by measurable
  have function_norm_measurable:
      "(\<lambda>x. norm (f x)) \<in> borel_measurable lborel"
    using function_measurable by measurable
  have function_norm_lp:
      "aim_real_lp_on_plane p (\<lambda>x. norm (f x))"
    unfolding aim_real_lp_on_plane_def
    using function_norm_measurable function_power_integrable by simp
  have scaled_data:
      "aim_real_lp_on_plane p ?v \<and>
        aim_real_lp_norm p ?v =
          C * aim_real_lp_norm p (\<lambda>x. norm (f x))"
    using slp_nonnegative_real_lp_scale[OF exponent_positive
        bound_nonnegative function_norm_lp] by blast
  have majorant_lp: "aim_real_lp_on_plane p ?v"
    using scaled_data by blast
  have majorant_norm:
      "aim_real_lp_norm p ?v =
        C * aim_real_lp_norm p (\<lambda>x. norm (f x))"
    using scaled_data by blast
  have target_norm_measurable: "?u \<in> borel_measurable lborel"
    using target_measurable by measurable
  have target_norm_nonnegative: "AE x in lborel. 0 \<le> ?u x"
    by simp
  have pointwise_bound: "AE x in lborel. ?u x \<le> ?v x"
    using multiplier_bound
  proof eventually_elim
    fix x
    assume multiplier_at_x: "norm (multiplier x) \<le> C"
    have multiplied:
        "norm (multiplier x) * norm (f x) \<le> C * norm (f x)"
      by (rule mult_right_mono[OF multiplier_at_x]) simp
    show "?u x \<le> ?v x"
      using multiplied by (simp only: norm_mult)
  qed
  have target_norm_lp: "aim_real_lp_on_plane p ?u"
    by (rule slp_nonnegative_real_lp_mono(1)[OF exponent_positive
          target_norm_measurable majorant_lp target_norm_nonnegative
          pointwise_bound])
  have target_norm_bound:
      "aim_real_lp_norm p ?u \<le> aim_real_lp_norm p ?v"
    by (rule slp_nonnegative_real_lp_mono(2)[OF exponent_positive
          target_norm_measurable majorant_lp target_norm_nonnegative
          pointwise_bound])
  have target_power_integrable:
      "integrable lborel (\<lambda>x. norm (?T x) powr p)"
    using target_norm_lp unfolding aim_real_lp_on_plane_def by simp
  show AE_product_lp: "aim_complex_lp_on_plane p ?T"
    unfolding aim_complex_lp_on_plane_def
    using target_measurable target_power_integrable by blast
  have target_norm_identity:
      "aim_complex_lp_norm p ?T = aim_real_lp_norm p ?u"
    unfolding aim_complex_lp_norm_def aim_real_lp_norm_def by simp
  have function_norm_identity:
      "aim_real_lp_norm p (\<lambda>x. norm (f x)) =
        aim_complex_lp_norm p f"
    unfolding aim_complex_lp_norm_def aim_real_lp_norm_def by simp
  show AE_product_norm_bound:
      "aim_complex_lp_norm p ?T \<le> C * aim_complex_lp_norm p f"
    using target_norm_bound majorant_norm
    unfolding target_norm_identity function_norm_identity by simp
qed

section \<open>Finite essential-supremum multiplier control\<close>

theorem slp_complex_lp_esssup_bounded_multiplier:
  fixes multiplier f :: slp_scalar_field
  assumes exponent_positive: "0 < p"
    and multiplier_measurable:
      "multiplier \<in> borel_measurable lborel"
    and esssup_bound:
      "esssup lborel (\<lambda>x. ereal (norm (multiplier x))) \<le> ereal C"
    and bound_nonnegative: "0 \<le> C"
    and function_lp: "aim_complex_lp_on_plane p f"
  shows esssup_product_lp:
      "aim_complex_lp_on_plane p (\<lambda>x. multiplier x * f x)"
    and esssup_product_norm_bound:
      "aim_complex_lp_norm p (\<lambda>x. multiplier x * f x) \<le>
        C * aim_complex_lp_norm p f"
proof -
  have below_esssup:
      "AE x in lborel.
        ereal (norm (multiplier x)) \<le>
          esssup lborel (\<lambda>y. ereal (norm (multiplier y)))"
    by (rule esssup_AE)
  have multiplier_bound:
      "AE x in lborel. norm (multiplier x) \<le> C"
    using below_esssup
  proof eventually_elim
    fix x
    assume at_x:
      "ereal (norm (multiplier x)) \<le>
        esssup lborel (\<lambda>y. ereal (norm (multiplier y)))"
    have "ereal (norm (multiplier x)) \<le> ereal C"
      by (rule order_trans[OF at_x esssup_bound])
    then show "norm (multiplier x) \<le> C"
      by simp
  qed
  note product = slp_complex_lp_AE_bounded_multiplier[
    OF exponent_positive multiplier_measurable multiplier_bound
      bound_nonnegative function_lp]
  show "aim_complex_lp_on_plane p (\<lambda>x. multiplier x * f x)"
    by (rule product(1))
  show "aim_complex_lp_norm p (\<lambda>x. multiplier x * f x) \<le>
      C * aim_complex_lp_norm p f"
    by (rule product(2))
qed

end
