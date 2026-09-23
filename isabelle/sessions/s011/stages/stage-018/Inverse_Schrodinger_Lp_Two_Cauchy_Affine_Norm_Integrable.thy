theory Inverse_Schrodinger_Lp_Two_Cauchy_Affine_Norm_Integrable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Mixed_Product_Error_Integration_Data"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Integrability of the affine two-Cauchy center majorant\<close>

context aim_planar_hls_cauchy
begin

theorem slp_test_two_cauchy_affine_norm_product_integrable:
  fixes p a b :: real
    and q qt phi :: slp_scalar_field
    and lo ro :: slp_cauchy_orientation
  assumes p_lower: "1 < p"
    and p_upper: "p < 2"
    and q_lp: "aim_complex_lp_on_plane p q"
    and qt_lp: "aim_complex_lp_on_plane p qt"
    and phi_test: "slp_test_function_on UNIV phi"
  shows
    "integrable lborel (\<lambda>c.
      norm (phi c) *
        (a + norm (slp_cauchy_transform lo q c)) *
        (b + norm (slp_cauchy_transform ro qt c)))"
proof -
  let ?A = "slp_cauchy_transform lo q"
  let ?B = "slp_cauchy_transform ro qt"
  have phi_integrable: "integrable lborel phi"
    by (rule slp_test_function_integrable_bounded(1)[OF phi_test])
  have phi_norm_integrable: "integrable lborel (\<lambda>c. norm (phi c))"
    by (rule integrable_norm[OF phi_integrable])
  have phiA_integrable: "integrable lborel (\<lambda>c. phi c * ?A c)"
    by (rule slp_test_cauchy_product_integrable[OF
          p_lower p_upper q_lp phi_test])
  have phiB_integrable: "integrable lborel (\<lambda>c. phi c * ?B c)"
    by (rule slp_test_cauchy_product_integrable[OF
          p_lower p_upper qt_lp phi_test])
  have phiAB_integrable:
      "integrable lborel (\<lambda>c. phi c * (?A c * ?B c))"
    by (rule slp_test_two_cauchy_product_integrable[OF
          p_lower p_upper q_lp qt_lp phi_test])
  have left_integrable:
      "integrable lborel (\<lambda>c. norm (phi c) * norm (?A c))"
    using integrable_norm[OF phiA_integrable]
    by (simp only: norm_mult)
  have right_integrable:
      "integrable lborel (\<lambda>c. norm (phi c) * norm (?B c))"
    using integrable_norm[OF phiB_integrable]
    by (simp only: norm_mult)
  have cross_integrable:
      "integrable lborel
        (\<lambda>c. norm (phi c) * (norm (?A c) * norm (?B c)))"
    using integrable_norm[OF phiAB_integrable]
    by (simp only: norm_mult)
  have constant_term:
      "integrable lborel (\<lambda>c. (a * b) * norm (phi c))"
  proof (rule integrable_mult_right)
    assume "a * b \<noteq> 0"
    show "integrable lborel (\<lambda>c. norm (phi c))"
      by (rule phi_norm_integrable)
  qed
  have left_term:
      "integrable lborel (\<lambda>c. b * (norm (phi c) * norm (?A c)))"
  proof (rule integrable_mult_right)
    assume "b \<noteq> 0"
    show "integrable lborel (\<lambda>c. norm (phi c) * norm (?A c))"
      by (rule left_integrable)
  qed
  have right_term:
      "integrable lborel (\<lambda>c. a * (norm (phi c) * norm (?B c)))"
  proof (rule integrable_mult_right)
    assume "a \<noteq> 0"
    show "integrable lborel (\<lambda>c. norm (phi c) * norm (?B c))"
      by (rule right_integrable)
  qed
  have expanded_integrable:
      "integrable lborel (\<lambda>c.
        (a * b) * norm (phi c) +
        b * (norm (phi c) * norm (?A c)) +
        a * (norm (phi c) * norm (?B c)) +
        norm (phi c) * (norm (?A c) * norm (?B c)))"
    by (intro Bochner_Integration.integrable_add constant_term left_term
          right_term cross_integrable)
  have presentation:
      "(\<lambda>c.
        norm (phi c) * (a + norm (?A c)) * (b + norm (?B c))) =
       (\<lambda>c.
        (a * b) * norm (phi c) +
        b * (norm (phi c) * norm (?A c)) +
        a * (norm (phi c) * norm (?B c)) +
        norm (phi c) * (norm (?A c) * norm (?B c)))"
    by (simp add: fun_eq_iff algebra_simps)
  show ?thesis
    using expanded_integrable by (simp only: presentation)
qed

end

end
