theory Inverse_Schrodinger_Lp_Quantitative_Value_Split_Norms
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Quantitative_Value_Split_Moments"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Norm form of the quantitative coefficient value split\<close>

theorem slp_quantitative_value_split_norm_bounds:
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
      \<and> aim_complex_lp_norm a (slp_value_high_part T f)
        \<le> T powr (1 - p / a) * aim_complex_lp_norm p f powr (p / a)
      \<and> aim_complex_lp_norm b (slp_value_low_part T f)
        \<le> T powr (1 - p / b) * aim_complex_lp_norm p f powr (p / b)"
proof -
  have p_positive: "0 < p"
    using a_positive a_below_p by linarith
  have b_positive: "0 < b"
    using p_positive p_below_b by linarith
  have a_nonzero: "a \<noteq> 0"
    using a_positive by simp
  have p_nonzero: "p \<noteq> 0"
    using p_positive by simp
  have b_nonzero: "b \<noteq> 0"
    using b_positive by simp
  have reciprocal_a_nonnegative: "0 \<le> 1 / a"
    using a_positive by simp
  have reciprocal_b_nonnegative: "0 \<le> 1 / b"
    using b_positive by simp

  let ?low = "slp_value_low_part T f"
  let ?high = "slp_value_high_part T f"
  let ?I = "integral\<^sup>L lborel (\<lambda>x. norm (f x) powr p)"
  let ?Ihigh =
    "integral\<^sup>L lborel (\<lambda>x. norm (?high x) powr a)"
  let ?Ilow =
    "integral\<^sup>L lborel (\<lambda>x. norm (?low x) powr b)"

  note split = slp_quantitative_value_split_moment_bounds[
    OF a_positive a_below_p p_below_b threshold_positive field_lp]
  have split_identity: "\<forall>x. f x = ?low x + ?high x"
    using split by blast
  have high_lp: "aim_complex_lp_on_plane a ?high"
    using split by blast
  have low_lp: "aim_complex_lp_on_plane b ?low"
    using split by blast
  have high_moment:
      "?Ihigh \<le> T powr (a - p) * ?I"
    using split by blast
  have low_moment:
      "?Ilow \<le> T powr (b - p) * ?I"
    using split by blast

  have source_integral_nonnegative: "0 \<le> ?I"
    by (rule integral_nonneg_AE) simp
  have high_integral_nonnegative: "0 \<le> ?Ihigh"
    by (rule integral_nonneg_AE) simp
  have low_integral_nonnegative: "0 \<le> ?Ilow"
    by (rule integral_nonneg_AE) simp

  have high_rooted:
      "?Ihigh powr (1 / a) \<le>
        (T powr (a - p) * ?I) powr (1 / a)"
    by (rule powr_mono2[OF reciprocal_a_nonnegative
          high_integral_nonnegative high_moment])
  have low_rooted:
      "?Ilow powr (1 / b) \<le>
        (T powr (b - p) * ?I) powr (1 / b)"
    by (rule powr_mono2[OF reciprocal_b_nonnegative
          low_integral_nonnegative low_moment])

  have high_threshold_exponent:
      "(a - p) * (1 / a) = 1 - p / a"
    using a_nonzero by (simp add: field_simps)
  have low_threshold_exponent:
      "(b - p) * (1 / b) = 1 - p / b"
    using b_nonzero by (simp add: field_simps)
  have high_source_exponent:
      "(1 / p) * (p / a) = 1 / a"
    using p_nonzero by (simp add: field_simps)
  have low_source_exponent:
      "(1 / p) * (p / b) = 1 / b"
    using p_nonzero by (simp add: field_simps)

  have high_product_root:
      "(T powr (a - p) * ?I) powr (1 / a) =
        (T powr (a - p)) powr (1 / a) * ?I powr (1 / a)"
    by (rule powr_mult)
  have low_product_root:
      "(T powr (b - p) * ?I) powr (1 / b) =
        (T powr (b - p)) powr (1 / b) * ?I powr (1 / b)"
    by (rule powr_mult)
  have high_threshold_root:
      "(T powr (a - p)) powr (1 / a) =
        T powr (1 - p / a)"
    using high_threshold_exponent by (simp only: powr_powr)
  have low_threshold_root:
      "(T powr (b - p)) powr (1 / b) =
        T powr (1 - p / b)"
    using low_threshold_exponent by (simp only: powr_powr)
  have high_source_root:
      "?I powr (1 / a) = (?I powr (1 / p)) powr (p / a)"
    using high_source_exponent by (simp only: powr_powr)
  have low_source_root:
      "?I powr (1 / b) = (?I powr (1 / p)) powr (p / b)"
    using low_source_exponent by (simp only: powr_powr)

  have high_presentation:
      "(T powr (a - p) * ?I) powr (1 / a) =
        T powr (1 - p / a) *
          aim_complex_lp_norm p f powr (p / a)"
    using high_product_root high_threshold_root high_source_root
    unfolding aim_complex_lp_norm_def by simp
  have low_presentation:
      "(T powr (b - p) * ?I) powr (1 / b) =
        T powr (1 - p / b) *
          aim_complex_lp_norm p f powr (p / b)"
    using low_product_root low_threshold_root low_source_root
    unfolding aim_complex_lp_norm_def by simp

  have high_norm_bound:
      "aim_complex_lp_norm a ?high \<le>
        T powr (1 - p / a) * aim_complex_lp_norm p f powr (p / a)"
    using high_rooted high_presentation
    unfolding aim_complex_lp_norm_def by simp
  have low_norm_bound:
      "aim_complex_lp_norm b ?low \<le>
        T powr (1 - p / b) * aim_complex_lp_norm p f powr (p / b)"
    using low_rooted low_presentation
    unfolding aim_complex_lp_norm_def by simp

  show ?thesis
    using split_identity high_lp low_lp high_norm_bound low_norm_bound
    by blast
qed

end
