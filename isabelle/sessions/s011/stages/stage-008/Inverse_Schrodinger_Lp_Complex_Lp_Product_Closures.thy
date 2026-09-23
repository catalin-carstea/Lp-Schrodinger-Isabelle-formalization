theory Inverse_Schrodinger_Lp_Complex_Lp_Product_Closures
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Oscillatory_Cross_Global_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Positive_Ennreal_Complex_Pairing"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_One_Sided_Zero_Finite_Lp"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Complex-valued Holder product closures\<close>

lemma slp_aim_complex_lp_on_plane_product:
  fixes a q r :: real
    and f g :: "slp_point \<Rightarrow> complex"
  assumes a_positive: "0 < a"
    and q_scale: "1 < q / a"
    and r_scale: "1 < r / a"
    and conjugate_scales: "1 / (q / a) + 1 / (r / a) = 1"
    and f_lp: "aim_complex_lp_on_plane q f"
    and g_lp: "aim_complex_lp_on_plane r g"
  shows
    "aim_complex_lp_on_plane a (\<lambda>x. f x * g x)"
proof -
  have f_norm_lp:
      "slp_positive_ennreal_lp_on_plane q
        (\<lambda>x. ennreal (norm_class.norm (f x)))"
    by (rule slp_positive_ennreal_lp_norm_of_complex[OF f_lp])
  have g_norm_lp:
      "slp_positive_ennreal_lp_on_plane r
        (\<lambda>x. ennreal (norm_class.norm (g x)))"
    by (rule slp_positive_ennreal_lp_norm_of_complex[OF g_lp])
  have product_norm_lp:
      "slp_positive_ennreal_lp_on_plane a
        (\<lambda>x. ennreal (norm_class.norm (f x)) *
          ennreal (norm_class.norm (g x)))"
    by (rule slp_positive_ennreal_lp_product[OF a_positive q_scale r_scale
          conjugate_scales f_norm_lp g_norm_lp])
  have f_measurable: "f \<in> borel_measurable lborel"
    and g_measurable: "g \<in> borel_measurable lborel"
    using f_lp g_lp unfolding aim_complex_lp_on_plane_def by blast+
  have product_measurable:
      "(\<lambda>x. f x * g x) \<in> borel_measurable lborel"
    using f_measurable g_measurable by measurable
  have product_power_integrable:
      "integrable lborel
        (\<lambda>x. norm_class.norm (f x * g x) powr a)"
  proof -
    have lifted_power_integrable:
        "integrable lborel
          (\<lambda>x. enn2real
            (ennreal (norm_class.norm (f x)) *
              ennreal (norm_class.norm (g x))) powr a)"
      using product_norm_lp
      unfolding slp_positive_ennreal_lp_on_plane_def by blast
    show ?thesis
      using lifted_power_integrable
      by (simp add: enn2real_mult norm_mult)
  qed
  show ?thesis
    unfolding aim_complex_lp_on_plane_def
    using product_measurable product_power_integrable by blast
qed

lemma slp_aim_complex_lp_on_plane_bounded_multiplier:
  fixes a C :: real
    and h f :: "slp_point \<Rightarrow> complex"
  assumes a_positive: "0 < a"
    and h_measurable: "h \<in> borel_measurable lborel"
    and h_bound: "\<And>x. norm_class.norm (h x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and f_lp: "aim_complex_lp_on_plane a f"
  shows
    "aim_complex_lp_on_plane a (\<lambda>x. h x * f x)"
proof -
  have h_norm_measurable:
      "(\<lambda>x. norm_class.norm (h x)) \<in> borel_measurable lborel"
    using h_measurable by measurable
  have h_norm_nonnegative: "0 \<le> norm_class.norm (h x)" for x
    by simp
  have f_norm_lp:
      "slp_positive_ennreal_lp_on_plane a
        (\<lambda>x. ennreal (norm_class.norm (f x)))"
    by (rule slp_positive_ennreal_lp_norm_of_complex[OF f_lp])
  have product_norm_lp:
      "slp_positive_ennreal_lp_on_plane a
        (\<lambda>x. ennreal (norm_class.norm (h x)) *
          ennreal (norm_class.norm (f x)))"
    by (rule slp_positive_ennreal_lp_bounded_multiplier[OF a_positive
          h_norm_measurable h_norm_nonnegative h_bound C_nonnegative f_norm_lp])
  have f_measurable: "f \<in> borel_measurable lborel"
    using f_lp unfolding aim_complex_lp_on_plane_def by blast
  have product_measurable:
      "(\<lambda>x. h x * f x) \<in> borel_measurable lborel"
    using h_measurable f_measurable by measurable
  have product_power_integrable:
      "integrable lborel
        (\<lambda>x. norm_class.norm (h x * f x) powr a)"
  proof -
    have lifted_power_integrable:
        "integrable lborel
          (\<lambda>x. enn2real
            (ennreal (norm_class.norm (h x)) *
              ennreal (norm_class.norm (f x))) powr a)"
      using product_norm_lp
      unfolding slp_positive_ennreal_lp_on_plane_def by blast
    show ?thesis
      using lifted_power_integrable
      by (simp add: enn2real_mult norm_mult)
  qed
  show ?thesis
    unfolding aim_complex_lp_on_plane_def
    using product_measurable product_power_integrable by blast
qed

end
