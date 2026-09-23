theory Inverse_Schrodinger_Lp_Conjugated_Cauchy_Source_Weak_Wirtinger
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_Test_Derivative_Integral"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Pair_Difference"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cauchy_Weak_Wirtinger"
begin

section \<open>Whole-plane linearity of recorded weak gradients\<close>

lemma slp_weak_gradient_on_UNIV_const:
  "slp_weak_gradient_on UNIV (\<lambda>_. k) (\<lambda>_. 0)"
  unfolding slp_weak_gradient_on_def
proof (intro allI impI)
  fix phi i
  assume phi_test: "slp_test_function_on UNIV phi"
  let ?dphi = "slp_complex_partial_derivative phi i"
  have dphi_test: "slp_test_function_on UNIV ?dphi"
    by (rule slp_test_function_on_partial_derivative[OF phi_test])
  have dphi_integrable: "integrable lborel ?dphi"
    by (rule slp_test_function_integrable_bounded(1)[OF dphi_test])
  have dphi_zero: "integral\<^sup>L lborel ?dphi = 0"
    by (rule slp_test_function_partial_integral_zero[OF phi_test])
  have scaled_integrable: "integrable lborel (\<lambda>x. k * ?dphi x)"
    by (rule Bochner_Integration.integrable_mult_right[OF dphi_integrable])
  have scaled_zero: "integral\<^sup>L lborel (\<lambda>x. k * ?dphi x) = 0"
    by (simp only: Bochner_Integration.integral_mult_right[OF dphi_integrable]
        dphi_zero mult_zero_right)
  have left_integrable:
      "set_integrable lborel UNIV (\<lambda>x. k * ?dphi x)"
    unfolding set_integrable_def
    by (simp only: indicator_UNIV scaleR_one scaled_integrable)
  have right_integrable:
      "set_integrable lborel UNIV
        (\<lambda>x. (0 :: complex ^ 2) $ i * phi x)"
    unfolding set_integrable_def by simp
  have left_zero:
      "set_lebesgue_integral lborel UNIV (\<lambda>x. k * ?dphi x) = 0"
    unfolding set_lebesgue_integral_def
    by (simp only: indicator_UNIV scaleR_one scaled_zero)
  have right_zero:
      "set_lebesgue_integral lborel UNIV
        (\<lambda>x. (0 :: complex ^ 2) $ i * phi x) = 0"
    unfolding set_lebesgue_integral_def by simp
  show "set_integrable lborel UNIV (\<lambda>x. k * ?dphi x) \<and>
      set_integrable lborel UNIV (\<lambda>x. (0 :: complex ^ 2) $ i * phi x) \<and>
      set_lebesgue_integral lborel UNIV (\<lambda>x. k * ?dphi x) =
        - set_lebesgue_integral lborel UNIV
          (\<lambda>x. (0 :: complex ^ 2) $ i * phi x)"
    using left_integrable right_integrable left_zero right_zero by simp
qed

lemma slp_weak_gradient_on_UNIV_neg:
  assumes weak: "slp_weak_gradient_on UNIV u Du"
  shows "slp_weak_gradient_on UNIV (\<lambda>x. - u x) (\<lambda>x. - Du x)"
proof -
  have difference:
      "slp_weak_gradient_on UNIV
        (\<lambda>x. (0::complex) - u x)
        (\<lambda>x. (0::complex ^ 2) - Du x)"
    by (rule slp_weak_gradient_on_diff[OF
          slp_weak_gradient_on_UNIV_const[of 0] weak])
  show ?thesis
    using difference by simp
qed

lemma slp_weak_gradient_on_UNIV_add:
  assumes first: "slp_weak_gradient_on UNIV u Du"
    and second: "slp_weak_gradient_on UNIV v Dv"
  shows "slp_weak_gradient_on UNIV
    (\<lambda>x. u x + v x) (\<lambda>x. Du x + Dv x)"
proof -
  have negative:
      "slp_weak_gradient_on UNIV (\<lambda>x. - v x) (\<lambda>x. - Dv x)"
    by (rule slp_weak_gradient_on_UNIV_neg[OF second])
  have difference:
      "slp_weak_gradient_on UNIV
        (\<lambda>x. u x - (- v x)) (\<lambda>x. Du x - (- Dv x))"
    by (rule slp_weak_gradient_on_diff[OF first negative])
  show ?thesis
    using difference by simp
qed

lemma slp_gradient_wirtinger_dbar_add:
  "slp_gradient_wirtinger_dbar (\<lambda>x. Du x + Dv x) =
    (\<lambda>x. slp_gradient_wirtinger_dbar Du x +
      slp_gradient_wirtinger_dbar Dv x)"
  by (rule ext)
    (simp add: slp_gradient_wirtinger_dbar_def divide_simps algebra_simps)

lemma slp_gradient_wirtinger_partial_add:
  "slp_gradient_wirtinger_partial (\<lambda>x. Du x + Dv x) =
    (\<lambda>x. slp_gradient_wirtinger_partial Du x +
      slp_gradient_wirtinger_partial Dv x)"
  by (rule ext)
    (simp add: slp_gradient_wirtinger_partial_def divide_simps algebra_simps)

section \<open>Exact conjugated Cauchy sources\<close>

definition slp_left_conjugated_cauchy_source ::
    "real \<Rightarrow> slp_point \<Rightarrow> slp_scalar_field \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_scalar_field"
where
  "slp_left_conjugated_cauchy_source tau c coefficient source x =
    (slp_dbar_inverse coefficient x - slp_dbar_inverse coefficient c) +
      slp_dbar_psi_inverse tau c source x"

definition slp_left_conjugated_cauchy_source_gradient ::
    "real \<Rightarrow> slp_point \<Rightarrow> slp_scalar_field \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_gradient_field"
where
  "slp_left_conjugated_cauchy_source_gradient tau c coefficient source x =
    slp_dbar_inverse_gradient coefficient x +
      slp_dbar_inverse_gradient
        (slp_oscillatory_modulation (- tau) c source) x"

definition slp_right_conjugated_cauchy_source ::
    "real \<Rightarrow> slp_point \<Rightarrow> slp_scalar_field \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_scalar_field"
where
  "slp_right_conjugated_cauchy_source tau c coefficient source x =
    (slp_partial_inverse coefficient x - slp_partial_inverse coefficient c) +
      slp_partial_psi_inverse (- tau) c source x"

definition slp_right_conjugated_cauchy_source_gradient ::
    "real \<Rightarrow> slp_point \<Rightarrow> slp_scalar_field \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_gradient_field"
where
  "slp_right_conjugated_cauchy_source_gradient tau c coefficient source x =
    slp_partial_inverse_gradient coefficient x +
      slp_partial_inverse_gradient
        (slp_oscillatory_modulation (- tau) c source) x"

context aim_planar_cauchy_beurling_derivatives
begin

theorem slp_both_conjugated_cauchy_sources_weak_wirtinger:
  assumes exponent_lower: "1 < (p::real)"
    and coefficient_lp: "aim_complex_lp_on_plane p coefficient"
    and coefficient_support: "bounded {x. coefficient x \<noteq> 0}"
    and source_lp: "aim_complex_lp_on_plane p source"
    and source_support: "bounded {x. source x \<noteq> 0}"
  shows
    "slp_weak_gradient_on UNIV
        (slp_left_conjugated_cauchy_source tau c coefficient source)
        (slp_left_conjugated_cauchy_source_gradient tau c coefficient source)
      \<and>
      slp_gradient_wirtinger_dbar
        (slp_left_conjugated_cauchy_source_gradient tau c coefficient source) =
        (\<lambda>x. coefficient x +
          slp_oscillatory_modulation (- tau) c source x)
      \<and>
      slp_weak_gradient_on UNIV
        (slp_right_conjugated_cauchy_source tau c coefficient source)
        (slp_right_conjugated_cauchy_source_gradient tau c coefficient source)
      \<and>
      slp_gradient_wirtinger_partial
        (slp_right_conjugated_cauchy_source_gradient tau c coefficient source) =
        (\<lambda>x. coefficient x +
          slp_oscillatory_modulation (- tau) c source x)"
proof -
  let ?modulated = "slp_oscillatory_modulation (- tau) c source"
  have modulated_lp: "aim_complex_lp_on_plane p ?modulated"
    using source_lp by simp
  have modulated_support: "bounded {x. ?modulated x \<noteq> 0}"
    using source_support by simp
  note coefficient_data = slp_both_cauchy_weak_wirtinger_right_inverse[OF
    exponent_lower coefficient_lp coefficient_support]
  have coefficient_dbar_weak:
      "slp_weak_gradient_on UNIV
        (slp_dbar_inverse coefficient)
        (slp_dbar_inverse_gradient coefficient)"
    using coefficient_data by blast
  have coefficient_dbar_id:
      "slp_gradient_wirtinger_dbar
        (slp_dbar_inverse_gradient coefficient) = coefficient"
    using coefficient_data by blast
  have coefficient_partial_weak:
      "slp_weak_gradient_on UNIV
        (slp_partial_inverse coefficient)
        (slp_partial_inverse_gradient coefficient)"
    using coefficient_data by blast
  have coefficient_partial_id:
      "slp_gradient_wirtinger_partial
        (slp_partial_inverse_gradient coefficient) = coefficient"
    using coefficient_data by blast
  note source_data = slp_both_cauchy_weak_wirtinger_right_inverse[OF
    exponent_lower modulated_lp modulated_support]
  have source_dbar_weak:
      "slp_weak_gradient_on UNIV
        (slp_dbar_inverse ?modulated)
        (slp_dbar_inverse_gradient ?modulated)"
    using source_data by blast
  have source_dbar_id:
      "slp_gradient_wirtinger_dbar
        (slp_dbar_inverse_gradient ?modulated) = ?modulated"
    using source_data by blast
  have source_partial_weak:
      "slp_weak_gradient_on UNIV
        (slp_partial_inverse ?modulated)
        (slp_partial_inverse_gradient ?modulated)"
    using source_data by blast
  have source_partial_id:
      "slp_gradient_wirtinger_partial
        (slp_partial_inverse_gradient ?modulated) = ?modulated"
    using source_data by blast

  have left_centered:
      "slp_weak_gradient_on UNIV
        (\<lambda>x. slp_dbar_inverse coefficient x -
          slp_dbar_inverse coefficient c)
        (slp_dbar_inverse_gradient coefficient)"
  proof -
    have difference:
        "slp_weak_gradient_on UNIV
          (\<lambda>x. slp_dbar_inverse coefficient x -
            slp_dbar_inverse coefficient c)
          (\<lambda>x. slp_dbar_inverse_gradient coefficient x - 0)"
      by (rule slp_weak_gradient_on_diff[OF coefficient_dbar_weak
            slp_weak_gradient_on_UNIV_const])
    show ?thesis using difference by simp
  qed
  have left_weak:
      "slp_weak_gradient_on UNIV
        (slp_left_conjugated_cauchy_source tau c coefficient source)
        (slp_left_conjugated_cauchy_source_gradient tau c coefficient source)"
    using slp_weak_gradient_on_UNIV_add[OF left_centered source_dbar_weak]
    unfolding slp_left_conjugated_cauchy_source_def
      slp_left_conjugated_cauchy_source_gradient_def
      slp_dbar_psi_inverse_def .
  have left_identity:
      "slp_gradient_wirtinger_dbar
          (slp_left_conjugated_cauchy_source_gradient tau c coefficient source) =
        (\<lambda>x. coefficient x + ?modulated x)"
    unfolding slp_left_conjugated_cauchy_source_gradient_def
    using coefficient_dbar_id source_dbar_id
    by (simp only: slp_gradient_wirtinger_dbar_add)

  have right_centered:
      "slp_weak_gradient_on UNIV
        (\<lambda>x. slp_partial_inverse coefficient x -
          slp_partial_inverse coefficient c)
        (slp_partial_inverse_gradient coefficient)"
  proof -
    have difference:
        "slp_weak_gradient_on UNIV
          (\<lambda>x. slp_partial_inverse coefficient x -
            slp_partial_inverse coefficient c)
          (\<lambda>x. slp_partial_inverse_gradient coefficient x - 0)"
      by (rule slp_weak_gradient_on_diff[OF coefficient_partial_weak
            slp_weak_gradient_on_UNIV_const])
    show ?thesis using difference by simp
  qed
  have right_weak:
      "slp_weak_gradient_on UNIV
        (slp_right_conjugated_cauchy_source tau c coefficient source)
        (slp_right_conjugated_cauchy_source_gradient tau c coefficient source)"
    using slp_weak_gradient_on_UNIV_add[OF right_centered source_partial_weak]
    unfolding slp_right_conjugated_cauchy_source_def
      slp_right_conjugated_cauchy_source_gradient_def
      slp_partial_psi_inverse_def .
  have right_identity:
      "slp_gradient_wirtinger_partial
          (slp_right_conjugated_cauchy_source_gradient tau c coefficient source) =
        (\<lambda>x. coefficient x + ?modulated x)"
    unfolding slp_right_conjugated_cauchy_source_gradient_def
    using coefficient_partial_id source_partial_id
    by (simp only: slp_gradient_wirtinger_partial_add)

  show ?thesis
    using left_weak left_identity right_weak right_identity by blast
qed

end

end
