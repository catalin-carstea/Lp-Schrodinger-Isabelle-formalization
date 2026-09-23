theory Inverse_Schrodinger_Lp_Bounded_Support_Lp_Norm
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Complex_Lp_Bounded_Multiplier"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Quantitative planar Lp bounds under bounded restriction\<close>

lemma slp_complex_indicator_lp_norm:
  fixes Y :: "slp_point set" and p :: real
  assumes exponent_positive: "0 < p"
    and set_measurable: "Y \<in> sets lborel"
    and set_bounded: "bounded Y"
  shows "aim_complex_lp_on_plane p (slp_restrict_field Y (\<lambda>_. 1))"
    "aim_complex_lp_norm p (slp_restrict_field Y (\<lambda>_. 1)) =
      measure lborel Y powr (1 / p)"
proof -
  have indicator_integrable:
      "integrable lborel (indicator Y :: slp_point \<Rightarrow> real)"
    using set_measurable emeasure_bounded_finite[OF set_bounded]
    by (simp add: integrable_indicator_iff)
  have field_measurable:
      "slp_restrict_field Y (\<lambda>_. 1) \<in> borel_measurable lborel"
    unfolding slp_restrict_field_def using set_measurable by measurable
  have power_function:
      "(\<lambda>x. norm (slp_restrict_field Y (\<lambda>_. 1) x) powr p) =
        (indicator Y :: slp_point \<Rightarrow> real)"
    by (rule ext) (simp add: slp_restrict_field_def indicator_def)
  show "aim_complex_lp_on_plane p (slp_restrict_field Y (\<lambda>_. 1))"
    unfolding aim_complex_lp_on_plane_def power_function
    using field_measurable indicator_integrable by simp
  show "aim_complex_lp_norm p (slp_restrict_field Y (\<lambda>_. 1)) =
      measure lborel Y powr (1 / p)"
    unfolding aim_complex_lp_norm_def power_function by simp
qed

lemma slp_bounded_restriction_lp_norm:
  fixes Y :: "slp_point set" and f :: slp_scalar_field and p A :: real
  assumes exponent_positive: "0 < p"
    and set_measurable: "Y \<in> sets lborel"
    and set_bounded: "bounded Y"
    and field_measurable: "f \<in> borel_measurable lborel"
    and bound_nonnegative: "0 \<le> A"
    and local_bound: "\<And>x. x \<in> Y \<Longrightarrow> norm (f x) \<le> A"
  shows "aim_complex_lp_on_plane p (slp_restrict_field Y f)"
    "aim_complex_lp_norm p (slp_restrict_field Y f) \<le>
      A * measure lborel Y powr (1 / p)"
proof -
  let ?M = "slp_restrict_field Y f"
  let ?I = "slp_restrict_field Y (\<lambda>_. 1)"
  have restricted_measurable: "?M \<in> borel_measurable lborel"
    unfolding slp_restrict_field_def
    using set_measurable field_measurable by measurable
  have restricted_bound: "norm (?M x) \<le> A" for x
    by (cases "x \<in> Y")
      (simp_all add: slp_restrict_field_def local_bound bound_nonnegative)
  have indicator_lp: "aim_complex_lp_on_plane p ?I"
    by (rule slp_complex_indicator_lp_norm(1)[OF
        exponent_positive set_measurable set_bounded])
  have indicator_norm: "aim_complex_lp_norm p ?I =
      measure lborel Y powr (1 / p)"
    by (rule slp_complex_indicator_lp_norm(2)[OF
        exponent_positive set_measurable set_bounded])
  have product_identity: "(\<lambda>x. ?M x * ?I x) = ?M"
    by (rule ext) (simp add: slp_restrict_field_def)
  show "aim_complex_lp_on_plane p ?M"
    using slp_complex_lp_bounded_multiplier(1)[OF exponent_positive
        restricted_measurable restricted_bound bound_nonnegative indicator_lp]
    by (simp only: product_identity)
  show "aim_complex_lp_norm p ?M \<le> A * measure lborel Y powr (1 / p)"
    using slp_complex_lp_bounded_multiplier(2)[OF exponent_positive
        restricted_measurable restricted_bound bound_nonnegative indicator_lp]
    by (simp only: product_identity indicator_norm)
qed

lemma slp_restriction_lp_norm_contraction:
  fixes Y :: "slp_point set" and f :: slp_scalar_field and p :: real
  assumes exponent_positive: "0 < p"
    and set_measurable: "Y \<in> sets lborel"
    and field_lp: "aim_complex_lp_on_plane p f"
  shows "aim_complex_lp_on_plane p (slp_restrict_field Y f)"
    "aim_complex_lp_norm p (slp_restrict_field Y f) \<le> aim_complex_lp_norm p f"
proof -
  let ?I = "slp_restrict_field Y (\<lambda>_. 1)"
  have indicator_measurable: "?I \<in> borel_measurable lborel"
    unfolding slp_restrict_field_def using set_measurable by measurable
  have indicator_bound: "norm (?I x) \<le> 1" for x
    by (simp add: slp_restrict_field_def)
  have one_nonnegative: "0 \<le> (1::real)" by simp
  have product_identity:
      "(\<lambda>x. ?I x * f x) = slp_restrict_field Y f"
    by (rule ext) (simp add: slp_restrict_field_def)
  show "aim_complex_lp_on_plane p (slp_restrict_field Y f)"
    using slp_complex_lp_bounded_multiplier(1)[OF exponent_positive
        indicator_measurable indicator_bound one_nonnegative field_lp]
    by (simp only: product_identity)
  show "aim_complex_lp_norm p (slp_restrict_field Y f) \<le> aim_complex_lp_norm p f"
    using slp_complex_lp_bounded_multiplier(2)[OF exponent_positive
        indicator_measurable indicator_bound one_nonnegative field_lp]
    by (simp only: product_identity mult.left_neutral)
qed

end
