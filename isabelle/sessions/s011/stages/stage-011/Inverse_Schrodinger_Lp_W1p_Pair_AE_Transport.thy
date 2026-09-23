theory Inverse_Schrodinger_Lp_W1p_Pair_AE_Transport
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Norm_AE_Congruence"
begin

section \<open>Restricted almost-everywhere transport of valid Sobolev pairs\<close>

lemma slp_set_integrable_transfer_restrict_AE:
  fixes f g :: "slp_point \<Rightarrow> complex"
  assumes X_measurable: "X \<in> sets lborel"
    and source_integrable: "set_integrable lborel X f"
    and target_indicator_measurable:
      "(\<lambda>x. indicator X x *\<^sub>R g x) \<in> borel_measurable lborel"
    and equality_AE: "AE x in restrict_space lborel X. f x = g x"
  shows "set_integrable lborel X g"
proof -
  have source_indicator_integrable:
      "integrable lborel (\<lambda>x. indicator X x *\<^sub>R f x)"
    using source_integrable unfolding set_integrable_def .
  have equality_lborel: "AE x in lborel. x \<in> X \<longrightarrow> f x = g x"
    using equality_AE X_measurable by (simp add: AE_restrict_space_iff)
  have indicator_AE:
      "AE x in lborel.
        indicator X x *\<^sub>R f x = indicator X x *\<^sub>R g x"
    using equality_lborel by eventually_elim auto
  show ?thesis
    unfolding set_integrable_def
    by (rule integrable_cong_AE_imp[
          OF source_indicator_integrable target_indicator_measurable
            indicator_AE])
qed

theorem slp_weak_gradient_on_cong_restrict_AE:
  assumes X_measurable: "X \<in> sets lborel"
    and source_weak: "slp_weak_gradient_on X u Du"
    and function_AE: "AE x in restrict_space lborel X. u x = v x"
    and gradient_AE: "AE x in restrict_space lborel X. Du x = Dv x"
    and target_left_measurable:
      "\<And>phi i. slp_test_function_on X phi \<Longrightarrow>
        (\<lambda>x. indicator X x *\<^sub>R
          (v x * slp_complex_partial_derivative phi i x))
          \<in> borel_measurable lborel"
    and target_right_measurable:
      "\<And>phi i. slp_test_function_on X phi \<Longrightarrow>
        (\<lambda>x. indicator X x *\<^sub>R (Dv x $ i * phi x))
          \<in> borel_measurable lborel"
  shows "slp_weak_gradient_on X v Dv"
  unfolding slp_weak_gradient_on_def
proof (intro allI impI)
  fix phi i
  assume phi_test: "slp_test_function_on X phi"
  have source:
      "set_integrable lborel X
          (\<lambda>x. u x * slp_complex_partial_derivative phi i x) \<and>
       set_integrable lborel X (\<lambda>x. Du x $ i * phi x) \<and>
       set_lebesgue_integral lborel X
          (\<lambda>x. u x * slp_complex_partial_derivative phi i x) =
        - set_lebesgue_integral lborel X (\<lambda>x. Du x $ i * phi x)"
    using source_weak phi_test unfolding slp_weak_gradient_on_def by blast
  have left_AE:
      "AE x in restrict_space lborel X.
        u x * slp_complex_partial_derivative phi i x =
          v x * slp_complex_partial_derivative phi i x"
    using function_AE by eventually_elim simp
  have right_AE:
      "AE x in restrict_space lborel X.
        Du x $ i * phi x = Dv x $ i * phi x"
    using gradient_AE by eventually_elim simp
  have source_left_integrable:
      "set_integrable lborel X
        (\<lambda>x. u x * slp_complex_partial_derivative phi i x)"
    using source by blast
  have source_right_integrable:
      "set_integrable lborel X (\<lambda>x. Du x $ i * phi x)"
    using source by blast
  have source_integral:
      "set_lebesgue_integral lborel X
          (\<lambda>x. u x * slp_complex_partial_derivative phi i x) =
        - set_lebesgue_integral lborel X (\<lambda>x. Du x $ i * phi x)"
    using source by blast
  have target_left_integrable:
      "set_integrable lborel X
        (\<lambda>x. v x * slp_complex_partial_derivative phi i x)"
    by (rule slp_set_integrable_transfer_restrict_AE[
          OF X_measurable source_left_integrable
            target_left_measurable[OF phi_test]
            left_AE])
  have target_right_integrable:
      "set_integrable lborel X (\<lambda>x. Dv x $ i * phi x)"
    by (rule slp_set_integrable_transfer_restrict_AE[
          OF X_measurable source_right_integrable
            target_right_measurable[OF phi_test]
            right_AE])
  have left_integral:
      "set_lebesgue_integral lborel X
          (\<lambda>x. u x * slp_complex_partial_derivative phi i x) =
        set_lebesgue_integral lborel X
          (\<lambda>x. v x * slp_complex_partial_derivative phi i x)"
    by (rule slp_set_lebesgue_integral_cong_restrict_AE[
          OF X_measurable left_AE source_left_integrable
            target_left_integrable])
  have right_integral:
      "set_lebesgue_integral lborel X (\<lambda>x. Du x $ i * phi x) =
        set_lebesgue_integral lborel X (\<lambda>x. Dv x $ i * phi x)"
    by (rule slp_set_lebesgue_integral_cong_restrict_AE[
          OF X_measurable right_AE source_right_integrable
            target_right_integrable])
  show "set_integrable lborel X
          (\<lambda>x. v x * slp_complex_partial_derivative phi i x) \<and>
        set_integrable lborel X (\<lambda>x. Dv x $ i * phi x) \<and>
        set_lebesgue_integral lborel X
          (\<lambda>x. v x * slp_complex_partial_derivative phi i x) =
          - set_lebesgue_integral lborel X (\<lambda>x. Dv x $ i * phi x)"
    using source_integral target_left_integrable target_right_integrable
      left_integral right_integral
    by simp
qed

theorem slp_w1p_pair_on_cong_restrict_AE:
  assumes X_measurable: "X \<in> sets lborel"
    and source_pair: "slp_w1p_pair_on p X u Du"
    and target_function_lp: "slp_complex_lp_on p X v"
    and target_derivative_zero_lp:
      "slp_complex_lp_on p X (\<lambda>x. Dv x $ 0)"
    and target_derivative_one_lp:
      "slp_complex_lp_on p X (\<lambda>x. Dv x $ 1)"
    and function_AE: "AE x in restrict_space lborel X. u x = v x"
    and gradient_AE: "AE x in restrict_space lborel X. Du x = Dv x"
  shows "slp_w1p_pair_on p X v Dv"
proof -
  have v_restrict_measurable:
      "slp_restrict_field X v \<in> borel_measurable lborel"
    using target_function_lp
    unfolding slp_complex_lp_on_def aim_complex_lp_on_plane_def by blast
  have derivative_zero_restrict_measurable:
      "slp_restrict_field X (\<lambda>x. Dv x $ 0)
        \<in> borel_measurable lborel"
    using target_derivative_zero_lp
    unfolding slp_complex_lp_on_def aim_complex_lp_on_plane_def by blast
  have derivative_one_restrict_measurable:
      "slp_restrict_field X (\<lambda>x. Dv x $ 1)
        \<in> borel_measurable lborel"
    using target_derivative_one_lp
    unfolding slp_complex_lp_on_def aim_complex_lp_on_plane_def by blast
  have target_left_measurable:
      "(\<lambda>x. indicator X x *\<^sub>R
        (v x * slp_complex_partial_derivative phi i x))
        \<in> borel_measurable lborel"
    if phi_test: "slp_test_function_on X phi" for phi i
  proof -
    have phi_smooth: "smooth_on UNIV phi"
      using phi_test unfolding slp_test_function_on_def by blast
    have derivative_smooth:
        "smooth_on UNIV (slp_complex_partial_derivative phi i)"
      by (rule slp_complex_partial_derivative_smooth[OF phi_smooth])
    have derivative_measurable:
        "slp_complex_partial_derivative phi i \<in> borel_measurable lborel"
      using borel_measurable_continuous_onI[
          OF smooth_on_imp_continuous_on[OF derivative_smooth]]
      by simp
    have product_measurable:
        "(\<lambda>x. slp_restrict_field X v x *
          slp_complex_partial_derivative phi i x)
          \<in> borel_measurable lborel"
      using v_restrict_measurable derivative_measurable by measurable
    have indicator_product:
        "(\<lambda>x. indicator X x *\<^sub>R
          (v x * slp_complex_partial_derivative phi i x)) =
        (\<lambda>x. slp_restrict_field X v x *
          slp_complex_partial_derivative phi i x)"
      by (rule ext) (simp add: indicator_def slp_restrict_field_def)
    show ?thesis
      using product_measurable
      unfolding indicator_product .
  qed
  have target_right_measurable:
      "(\<lambda>x. indicator X x *\<^sub>R (Dv x $ i * phi x))
        \<in> borel_measurable lborel"
    if phi_test: "slp_test_function_on X phi" for phi i
  proof -
    have phi_smooth: "smooth_on UNIV phi"
      using phi_test unfolding slp_test_function_on_def by blast
    have phi_measurable: "phi \<in> borel_measurable lborel"
      using borel_measurable_continuous_onI[
          OF smooth_on_imp_continuous_on[OF phi_smooth]]
      by simp
    have two_eq_zero: "(2 :: 2) = 0"
      by (simp add: of_nat_eq_0_iff_char_dvd)
    have coordinate_restrict_measurable:
        "slp_restrict_field X (\<lambda>x. Dv x $ i)
          \<in> borel_measurable lborel"
      using derivative_zero_restrict_measurable
        derivative_one_restrict_measurable exhaust_2[of i] two_eq_zero
      by auto
    have product_measurable:
        "(\<lambda>x. slp_restrict_field X (\<lambda>y. Dv y $ i) x * phi x)
          \<in> borel_measurable lborel"
      using coordinate_restrict_measurable phi_measurable by measurable
    have indicator_product:
        "(\<lambda>x. indicator X x *\<^sub>R (Dv x $ i * phi x)) =
        (\<lambda>x. slp_restrict_field X (\<lambda>y. Dv y $ i) x * phi x)"
      by (rule ext) (simp add: indicator_def slp_restrict_field_def)
    show ?thesis
      using product_measurable
      unfolding indicator_product .
  qed
  have target_weak: "slp_weak_gradient_on X v Dv"
    by (rule slp_weak_gradient_on_cong_restrict_AE[
          OF X_measurable slp_w1p_pair_onD(1)[OF source_pair]
            function_AE gradient_AE target_left_measurable
            target_right_measurable])
  show ?thesis
    unfolding slp_w1p_pair_on_def
    using target_weak target_function_lp target_derivative_zero_lp
      target_derivative_one_lp
    by blast
qed

end
