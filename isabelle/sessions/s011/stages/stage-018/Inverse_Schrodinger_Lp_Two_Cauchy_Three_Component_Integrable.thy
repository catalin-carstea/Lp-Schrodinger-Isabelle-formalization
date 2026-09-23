theory Inverse_Schrodinger_Lp_Two_Cauchy_Three_Component_Integrable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_018.Inverse_Schrodinger_Lp_Two_Cauchy_Affine_Norm_Integrable"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Three-component tested Cauchy majorants\<close>

context aim_planar_hls_cauchy
begin

theorem slp_test_two_cauchy_three_component_majorant_integrable:
  fixes p a b k_left k_right k_cross :: real
    and q qt phi :: slp_scalar_field
    and lo ro :: slp_cauchy_orientation
  assumes p_lower: "1 < p"
    and p_upper: "p < 2"
    and q_lp: "aim_complex_lp_on_plane p q"
    and qt_lp: "aim_complex_lp_on_plane p qt"
    and phi_test: "slp_test_function_on UNIV phi"
  shows
    "integrable lborel (\<lambda>c. norm (phi c) *
      (k_left * (a + norm (slp_cauchy_transform lo q c)) +
       k_right * (b + norm (slp_cauchy_transform ro qt c)) +
       k_cross * (a + norm (slp_cauchy_transform lo q c)) *
         (b + norm (slp_cauchy_transform ro qt c))))"
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
  have left_norm_integrable:
      "integrable lborel (\<lambda>c. norm (phi c) * norm (?A c))"
    using integrable_norm[OF phiA_integrable]
    by (simp only: norm_mult)
  have right_norm_integrable:
      "integrable lborel (\<lambda>c. norm (phi c) * norm (?B c))"
    using integrable_norm[OF phiB_integrable]
    by (simp only: norm_mult)
  have a_phi_integrable:
      "integrable lborel (\<lambda>c. a * norm (phi c))"
  proof (rule integrable_mult_right)
    assume "a \<noteq> 0"
    show "integrable lborel (\<lambda>c. norm (phi c))"
      by (rule phi_norm_integrable)
  qed
  have b_phi_integrable:
      "integrable lborel (\<lambda>c. b * norm (phi c))"
  proof (rule integrable_mult_right)
    assume "b \<noteq> 0"
    show "integrable lborel (\<lambda>c. norm (phi c))"
      by (rule phi_norm_integrable)
  qed
  have left_affine_integrable:
      "integrable lborel (\<lambda>c.
        norm (phi c) * (a + norm (?A c)))"
  proof -
    have expanded:
        "integrable lborel (\<lambda>c.
          a * norm (phi c) + norm (phi c) * norm (?A c))"
      by (rule Bochner_Integration.integrable_add[OF
            a_phi_integrable left_norm_integrable])
    have presentation:
        "(\<lambda>c. norm (phi c) * (a + norm (?A c))) =
         (\<lambda>c. a * norm (phi c) + norm (phi c) * norm (?A c))"
      by (simp add: fun_eq_iff algebra_simps)
    show ?thesis using expanded by (simp only: presentation)
  qed
  have right_affine_integrable:
      "integrable lborel (\<lambda>c.
        norm (phi c) * (b + norm (?B c)))"
  proof -
    have expanded:
        "integrable lborel (\<lambda>c.
          b * norm (phi c) + norm (phi c) * norm (?B c))"
      by (rule Bochner_Integration.integrable_add[OF
            b_phi_integrable right_norm_integrable])
    have presentation:
        "(\<lambda>c. norm (phi c) * (b + norm (?B c))) =
         (\<lambda>c. b * norm (phi c) + norm (phi c) * norm (?B c))"
      by (simp add: fun_eq_iff algebra_simps)
    show ?thesis using expanded by (simp only: presentation)
  qed
  have cross_integrable:
      "integrable lborel (\<lambda>c.
        norm (phi c) * (a + norm (?A c)) * (b + norm (?B c)))"
    by (rule slp_test_two_cauchy_affine_norm_product_integrable[OF
          p_lower p_upper q_lp qt_lp phi_test])
  have left_term:
      "integrable lborel (\<lambda>c.
        k_left * (norm (phi c) * (a + norm (?A c))))"
  proof (rule integrable_mult_right)
    assume "k_left \<noteq> 0"
    show "integrable lborel (\<lambda>c.
      norm (phi c) * (a + norm (?A c)))"
      by (rule left_affine_integrable)
  qed
  have right_term:
      "integrable lborel (\<lambda>c.
        k_right * (norm (phi c) * (b + norm (?B c))))"
  proof (rule integrable_mult_right)
    assume "k_right \<noteq> 0"
    show "integrable lborel (\<lambda>c.
      norm (phi c) * (b + norm (?B c)))"
      by (rule right_affine_integrable)
  qed
  have cross_term:
      "integrable lborel (\<lambda>c.
        k_cross * (norm (phi c) * (a + norm (?A c)) *
          (b + norm (?B c))))"
  proof (rule integrable_mult_right)
    assume "k_cross \<noteq> 0"
    show "integrable lborel (\<lambda>c.
      norm (phi c) * (a + norm (?A c)) * (b + norm (?B c)))"
      by (rule cross_integrable)
  qed
  have expanded_integrable:
      "integrable lborel (\<lambda>c.
        k_left * (norm (phi c) * (a + norm (?A c))) +
        k_right * (norm (phi c) * (b + norm (?B c))) +
        k_cross * (norm (phi c) * (a + norm (?A c)) *
          (b + norm (?B c))))"
    by (intro Bochner_Integration.integrable_add left_term right_term
          cross_term)
  have presentation:
      "(\<lambda>c. norm (phi c) *
        (k_left * (a + norm (?A c)) +
         k_right * (b + norm (?B c)) +
         k_cross * (a + norm (?A c)) * (b + norm (?B c)))) =
       (\<lambda>c.
        k_left * (norm (phi c) * (a + norm (?A c))) +
        k_right * (norm (phi c) * (b + norm (?B c))) +
        k_cross * (norm (phi c) * (a + norm (?A c)) *
          (b + norm (?B c))))"
    by (simp add: fun_eq_iff algebra_simps)
  show ?thesis using expanded_integrable by (simp only: presentation)
qed

end

end
