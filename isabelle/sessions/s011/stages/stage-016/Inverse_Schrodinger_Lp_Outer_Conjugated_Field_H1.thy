theory Inverse_Schrodinger_Lp_Outer_Conjugated_Field_H1
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Outer_Conjugated_Source_Local_W1pstar"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Local_W1s_Cutoff_Zero_Pair"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Finite-measure descent from local W1s to the project H1 carrier\<close>

lemma slp_complex_lp_on_measurable_restrict_space:
  assumes X_measurable: "X \<in> sets lborel"
    and f_lp: "slp_complex_lp_on p X f"
  shows "f \<in> borel_measurable (restrict_space lborel X)"
proof -
  have restrict_measurable:
      "slp_restrict_field X f \<in> borel_measurable lborel"
    using f_lp
    unfolding slp_complex_lp_on_def aim_complex_lp_on_plane_def by blast
  have indicator_restriction:
      "(\<lambda>x. indicator X x *\<^sub>R f x) = slp_restrict_field X f"
  proof (rule ext)
    fix x
    show "indicator X x *\<^sub>R f x = slp_restrict_field X f x"
      by (cases "x \<in> X")
         (simp_all add: indicator_def slp_restrict_field_def)
  qed
  show ?thesis
    apply (subst borel_measurable_restrict_space_iff)
     apply (use X_measurable in simp)
    using restrict_measurable
    by (simp only: indicator_restriction)
qed

lemma slp_complex_lp_on_two_set_integrable_norm_square:
  assumes f_lp: "slp_complex_lp_on 2 X f"
  shows "set_integrable lborel X (\<lambda>x. Real_Vector_Spaces.norm (f x) ^ 2)"
proof -
  have restricted_power_integrable:
      "integrable lborel
        (\<lambda>x. Real_Vector_Spaces.norm (slp_restrict_field X f x) powr 2)"
    using f_lp
    unfolding slp_complex_lp_on_def aim_complex_lp_on_plane_def by blast
  have indicator_power:
      "(\<lambda>x. indicator X x *\<^sub>R
          (Real_Vector_Spaces.norm (f x) ^ 2)) =
        (\<lambda>x. Real_Vector_Spaces.norm
          (slp_restrict_field X f x) powr 2)"
    by (rule ext)
       (auto simp: indicator_def slp_restrict_field_def powr_nat)
  show ?thesis
    using restricted_power_integrable
    unfolding set_integrable_def indicator_power .
qed

lemma slp_gradient_norm_square_components:
  fixes v :: "complex ^ 2"
  shows "Real_Vector_Spaces.norm v ^ 2 =
    Real_Vector_Spaces.norm (v $ 0) ^ 2 +
      Real_Vector_Spaces.norm (v $ 1) ^ 2"
proof -
  have universe_two: "(UNIV :: 2 set) = {0, 1}"
    using UNIV_2 by auto
  have sum_nonnegative:
      "0 \<le> (\<Sum>i\<in>(UNIV::2 set).
        Real_Vector_Spaces.norm (v $ i) ^ 2)"
    by (rule sum_nonneg) simp
  show ?thesis
    by (simp add: norm_vec_def L2_set_def universe_two
        real_sqrt_pow2[OF sum_nonnegative])
qed

lemma slp_w1p_pair_on_two_h1_pair_on:
  assumes X_measurable: "X \<in> sets lborel"
    and pair: "slp_w1p_pair_on 2 X u Du"
  shows "slp_h1_pair_on X u Du"
proof -
  have weak: "slp_weak_gradient_on X u Du"
    and u_l2: "slp_complex_lp_on 2 X u"
    and D0_l2: "slp_complex_lp_on 2 X (\<lambda>x. Du x $ 0)"
    and D1_l2: "slp_complex_lp_on 2 X (\<lambda>x. Du x $ 1)"
    using pair unfolding slp_w1p_pair_on_def by blast+
  have u_measurable:
      "u \<in> borel_measurable (restrict_space lborel X)"
    by (rule slp_complex_lp_on_measurable_restrict_space[OF
          X_measurable u_l2])
  have D0_measurable:
      "(\<lambda>x. Du x $ 0) \<in>
        borel_measurable (restrict_space lborel X)"
    by (rule slp_complex_lp_on_measurable_restrict_space[OF
          X_measurable D0_l2])
  have D1_measurable:
      "(\<lambda>x. Du x $ 1) \<in>
        borel_measurable (restrict_space lborel X)"
    by (rule slp_complex_lp_on_measurable_restrict_space[OF
          X_measurable D1_l2])
  have coordinate_cases: "i = 0 \<or> i = 1" for i :: 2
  proof -
    have two_is_zero: "(2 :: 2) = 0"
      by simp
    have raw_cases: "i = 1 \<or> i = (2 :: 2)"
      by (rule exhaust_2)
    show ?thesis
      using raw_cases two_is_zero by blast
  qed
  have component_measurable:
      "(\<lambda>x. Du x $ i) \<in>
        borel_measurable (restrict_space lborel X)" for i :: 2
    using coordinate_cases[of i] D0_measurable D1_measurable by blast
  have Du_measurable:
      "Du \<in> borel_measurable (restrict_space lborel X)"
  proof -
    have coordinates_measurable:
        "(\<lambda>x i. Du x $ i) \<in> borel_measurable
          (restrict_space lborel X)"
    proof (rule measurable_coordinatewise_then_product)
      fix i :: 2
      show "(\<lambda>x. Du x $ i) \<in>
          borel_measurable (restrict_space lborel X)"
        by (rule component_measurable)
    qed
    have vec_measurable:
        "vec_lambda \<in> borel_measurable
          (borel :: (2 \<Rightarrow> complex) measure)"
      by (rule borel_measurable_continuous_onI)
        (intro continuous_on_vec_lambda, simp)
    show ?thesis
      using measurable_compose[OF coordinates_measurable vec_measurable]
      by (simp only: comp_def vec_lambda_eta)
  qed
  have u_square_integrable:
      "set_integrable lborel X
        (\<lambda>x. Real_Vector_Spaces.norm (u x) ^ 2)"
    by (rule slp_complex_lp_on_two_set_integrable_norm_square[OF u_l2])
  have D0_square_integrable:
      "set_integrable lborel X
        (\<lambda>x. Real_Vector_Spaces.norm (Du x $ 0) ^ 2)"
    by (rule slp_complex_lp_on_two_set_integrable_norm_square[OF D0_l2])
  have D1_square_integrable:
      "set_integrable lborel X
        (\<lambda>x. Real_Vector_Spaces.norm (Du x $ 1) ^ 2)"
    by (rule slp_complex_lp_on_two_set_integrable_norm_square[OF D1_l2])
  have gradient_square_integrable:
      "set_integrable lborel X
        (\<lambda>x. Real_Vector_Spaces.norm (Du x) ^ 2)"
  proof -
    have sum_integrable:
        "set_integrable lborel X
          (\<lambda>x. Real_Vector_Spaces.norm (Du x $ 0) ^ 2 +
            Real_Vector_Spaces.norm (Du x $ 1) ^ 2)"
    proof -
      have indicator_add:
          "(\<lambda>x. indicator X x *\<^sub>R
              (Real_Vector_Spaces.norm (Du x $ 0) ^ 2 +
                Real_Vector_Spaces.norm (Du x $ 1) ^ 2)) =
            (\<lambda>x. indicator X x *\<^sub>R
                Real_Vector_Spaces.norm (Du x $ 0) ^ 2 +
              indicator X x *\<^sub>R
                Real_Vector_Spaces.norm (Du x $ 1) ^ 2)"
        by (simp add: fun_eq_iff algebra_simps)
      show ?thesis
        unfolding set_integrable_def indicator_add
        by (rule Bochner_Integration.integrable_add[OF
              D0_square_integrable[unfolded set_integrable_def]
              D1_square_integrable[unfolded set_integrable_def]])
    qed
    show ?thesis
      using sum_integrable
      by (simp only: slp_gradient_norm_square_components)
  qed
  show ?thesis
    unfolding slp_h1_pair_on_def
    using u_measurable Du_measurable weak u_square_integrable
      gradient_square_integrable by blast
qed

lemma slp_local_w1s_certificate_above_two_h1_pair_on:
  assumes exponent_above_two: "2 < s"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and certificate: "slp_local_w1s_certificate s X u Du"
  shows "slp_h1_pair_on X u Du"
proof -
  have pair_s: "slp_w1p_pair_on s X u Du"
    by (rule slp_local_w1s_certificate_w1p_pair_on[OF certificate])
  have weak: "slp_weak_gradient_on X u Du"
    and u_ls: "slp_complex_lp_on s X u"
    and D0_ls: "slp_complex_lp_on s X (\<lambda>x. Du x $ 0)"
    and D1_ls: "slp_complex_lp_on s X (\<lambda>x. Du x $ 1)"
    using pair_s unfolding slp_w1p_pair_on_def by blast+
  have exponent_order: "2 \<le> s"
    using exponent_above_two by linarith
  have u_l2: "slp_complex_lp_on 2 X u"
    by (rule slp_complex_lp_on_mono_exponent_bounded[OF
          _ exponent_order X_measurable X_bounded u_ls]) simp
  have D0_l2: "slp_complex_lp_on 2 X (\<lambda>x. Du x $ 0)"
    by (rule slp_complex_lp_on_mono_exponent_bounded[OF
          _ exponent_order X_measurable X_bounded D0_ls]) simp
  have D1_l2: "slp_complex_lp_on 2 X (\<lambda>x. Du x $ 1)"
    by (rule slp_complex_lp_on_mono_exponent_bounded[OF
          _ exponent_order X_measurable X_bounded D1_ls]) simp
  have pair_two: "slp_w1p_pair_on 2 X u Du"
    unfolding slp_w1p_pair_on_def
    using weak u_l2 D0_l2 D1_l2 by blast
  show ?thesis
    by (rule slp_w1p_pair_on_two_h1_pair_on[OF X_measurable pair_two])
qed

section \<open>Exact outer conjugated fields in project H1\<close>

context slp_cauchy_outer_fixed_point
begin

theorem slp_both_outer_conjugated_fields_h1:
  fixes p M tau :: real
    and c :: slp_point
    and X Omega :: "slp_point set"
    and cutoff coefficient W :: slp_scalar_field
  assumes exponent_lower: "1 < p"
    and exponent_upper: "p < 2"
    and X_open: "open X"
    and X_bounded: "bounded X"
    and cutoff_test: "slp_test_function_on X cutoff"
    and coefficient_lp: "aim_complex_lp_on_plane p coefficient"
    and coefficient_support: "{x. coefficient x \<noteq> 0} \<subseteq> X"
    and W_admissible: "slp_ae_bounded_measurable lborel M W"
    and Omega_measurable: "Omega \<in> sets (lborel :: slp_point measure)"
    and Omega_bounded: "bounded Omega"
  shows
    "slp_h1_pair_on Omega
        (slp_left_outer_conjugated_field tau c cutoff coefficient W)
        (slp_left_outer_conjugated_gradient tau c cutoff coefficient W)
      \<and>
      slp_h1_pair_on Omega
        (slp_right_outer_conjugated_field tau c cutoff coefficient W)
        (slp_right_outer_conjugated_gradient tau c cutoff coefficient W)"
proof -
  have target_above_two: "2 < aim_hls_target_exponent p"
    by (rule slp_qstar_exponent_relations(1)[OF
          exponent_lower exponent_upper])
  note certificates = slp_both_outer_conjugated_fields_local_w1pstar[OF
    exponent_lower exponent_upper X_open X_bounded cutoff_test coefficient_lp
    coefficient_support W_admissible Omega_measurable Omega_bounded]
  have left:
      "slp_h1_pair_on Omega
        (slp_left_outer_conjugated_field tau c cutoff coefficient W)
        (slp_left_outer_conjugated_gradient tau c cutoff coefficient W)"
    by (rule slp_local_w1s_certificate_above_two_h1_pair_on[OF
          target_above_two Omega_measurable Omega_bounded])
       (use certificates in blast)
  have right:
      "slp_h1_pair_on Omega
        (slp_right_outer_conjugated_field tau c cutoff coefficient W)
        (slp_right_outer_conjugated_gradient tau c cutoff coefficient W)"
    by (rule slp_local_w1s_certificate_above_two_h1_pair_on[OF
          target_above_two Omega_measurable Omega_bounded])
       (use certificates in blast)
  show ?thesis
    using left right by blast
qed

end

end
