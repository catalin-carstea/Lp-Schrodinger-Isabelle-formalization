theory Inverse_Schrodinger_Lp_Quantitative_Complex_Lp_Product
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Quantitative_Complex_Holder"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Quantitative complex planar Lp product bound\<close>

theorem slp_aim_complex_lp_on_plane_product_norm_bound:
  fixes a q r :: real
    and f g :: "slp_point \<Rightarrow> complex"
  assumes a_positive: "0 < a"
    and q_scale: "1 < q / a"
    and r_scale: "1 < r / a"
    and conjugate_scales: "1 / (q / a) + 1 / (r / a) = 1"
    and f_lp: "aim_complex_lp_on_plane q f"
    and g_lp: "aim_complex_lp_on_plane r g"
  shows product_lp:
      "aim_complex_lp_on_plane a (\<lambda>x. f x * g x)"
    and product_norm:
      "aim_complex_lp_norm a (\<lambda>x. f x * g x) \<le>
        aim_complex_lp_norm q f * aim_complex_lp_norm r g"
proof -
  show product_lp:
      "aim_complex_lp_on_plane a (\<lambda>x. f x * g x)"
    by (rule slp_aim_complex_lp_on_plane_product[OF a_positive q_scale
          r_scale conjugate_scales f_lp g_lp])
  have f_measurable: "f \<in> borel_measurable lborel"
    and f_power_integrable:
      "integrable lborel (\<lambda>x. norm_class.norm (f x) powr q)"
    using f_lp unfolding aim_complex_lp_on_plane_def by blast+
  have g_measurable: "g \<in> borel_measurable lborel"
    and g_power_integrable:
      "integrable lborel (\<lambda>x. norm_class.norm (g x) powr r)"
    using g_lp unfolding aim_complex_lp_on_plane_def by blast+
  let ?Q = "q / a"
  let ?R = "r / a"
  let ?A = "integral\<^sup>L lborel
    (\<lambda>x. norm_class.norm (f x) powr q)"
  let ?B = "integral\<^sup>L lborel
    (\<lambda>x. norm_class.norm (g x) powr r)"
  let ?I = "integral\<^sup>L lborel
    (\<lambda>x. norm_class.norm (f x * g x) powr a)"
  have f_a_measurable:
      "(\<lambda>x. norm_class.norm (f x) powr a) \<in>
        borel_measurable lborel"
    using f_measurable by measurable
  have g_a_measurable:
      "(\<lambda>x. norm_class.norm (g x) powr a) \<in>
        borel_measurable lborel"
    using g_measurable by measurable
  have scale_products: "a * ?Q = q" "a * ?R = r"
    using a_positive by simp_all
  have f_scaled_power_integrable:
      "integrable lborel
        (\<lambda>x. (norm_class.norm (f x) powr a) powr ?Q)"
    using f_power_integrable a_positive scale_products(1)
    by (simp add: powr_powr)
  have g_scaled_power_integrable:
      "integrable lborel
        (\<lambda>x. (norm_class.norm (g x) powr a) powr ?R)"
    using g_power_integrable a_positive scale_products(2)
    by (simp add: powr_powr)
  have holder_bound:
      "integral\<^sup>L lborel
          (\<lambda>x. (norm_class.norm (f x) powr a) *
            (norm_class.norm (g x) powr a)) \<le>
        (integral\<^sup>L lborel
          (\<lambda>x. (norm_class.norm (f x) powr a) powr ?Q)) powr
            (1 / ?Q) *
        (integral\<^sup>L lborel
          (\<lambda>x. (norm_class.norm (g x) powr a) powr ?R)) powr
            (1 / ?R)"
    by (rule slp_nonnegative_holder_integral(2)[OF q_scale r_scale
          conjugate_scales f_a_measurable g_a_measurable])
      (simp_all add: f_scaled_power_integrable g_scaled_power_integrable)
  have product_power_bound:
      "?I \<le> ?A powr (1 / ?Q) * ?B powr (1 / ?R)"
    using holder_bound a_positive scale_products
    by (simp add: norm_mult powr_mult powr_powr)
  have I_nonnegative: "0 \<le> ?I"
    by (rule integral_nonneg_AE) simp
  have reciprocal_a_nonnegative: "0 \<le> 1 / a"
    using a_positive by simp
  have raised_bound:
      "?I powr (1 / a) \<le>
        (?A powr (1 / ?Q) * ?B powr (1 / ?R)) powr (1 / a)"
    by (rule powr_mono2[OF reciprocal_a_nonnegative I_nonnegative
          product_power_bound])
  have A_nonnegative: "0 \<le> ?A" and B_nonnegative: "0 \<le> ?B"
    by (rule integral_nonneg_AE, simp)+
  have Q_positive: "0 < ?Q" and R_positive: "0 < ?R"
    using q_scale r_scale by linarith+
  have q_positive: "0 < q"
    using mult_pos_pos[OF a_positive Q_positive] scale_products(1) by simp
  have r_positive: "0 < r"
    using mult_pos_pos[OF a_positive R_positive] scale_products(2) by simp
  have normalized_right:
      "(?A powr (1 / ?Q) * ?B powr (1 / ?R)) powr (1 / a) =
        ?A powr (1 / q) * ?B powr (1 / r)"
    using A_nonnegative B_nonnegative a_positive q_positive r_positive
      scale_products
    by (simp add: powr_mult powr_powr)
  show product_norm:
      "aim_complex_lp_norm a (\<lambda>x. f x * g x) \<le>
        aim_complex_lp_norm q f * aim_complex_lp_norm r g"
    using raised_bound
    unfolding aim_complex_lp_norm_def
    by (simp only: normalized_right)
qed

end
