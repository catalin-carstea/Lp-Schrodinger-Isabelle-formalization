theory Inverse_Schrodinger_Lp_W1p_Rough_Far_Target_Integrability
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Rough_Far_Product"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cauchy_Holder_Continuity"
begin

section \<open>Cauchy integrability of the two rough far-product sources\<close>

theorem slp_w1p_rough_far_target_cauchy_integrable:
  fixes p R :: real
  assumes exponent_above_two: "2 < p"
    and radius_nonnegative: "0 \<le> R"
    and pair: "slp_w1p_pair_on p X u Du"
    and X_radius: "\<And>y. y \<in> X \<Longrightarrow> norm (z - y) \<le> R"
  shows base_target_integrable:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (\<lambda>x. (slp_point_as_complex (x - c) *
          slp_center_kernel tau c x) * slp_restrict_field X u x) z"
    and derivative_target_integrable:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (\<lambda>x. slp_center_kernel tau c x *
          slp_restrict_field X (slp_gradient_wirtinger_partial Du) x) z"
proof -
  have exponent_positive: "0 < p"
    using exponent_above_two by linarith
  have exponent_one_le: "1 \<le> p"
    using exponent_above_two by linarith
  have value_lp:
      "aim_complex_lp_on_plane p (slp_restrict_field X u)"
    using slp_w1p_pair_onD(2)[OF pair]
    unfolding slp_complex_lp_on_def .
  have value_support:
      "slp_restrict_field X u y \<noteq> 0 \<Longrightarrow> norm (z - y) \<le> R"
      for y
  proof -
    assume nonzero: "slp_restrict_field X u y \<noteq> 0"
    have "y \<in> X"
      using nonzero unfolding slp_restrict_field_def
      by (cases "y \<in> X") auto
    then show "norm (z - y) \<le> R" by (rule X_radius)
  qed
  let ?zero_sequence = "\<lambda>_::nat. \<lambda>_::slp_point. 0::complex"
  let ?negative_value = "\<lambda>x. - slp_restrict_field X u x"
  have raw_value_presentation:
      "slp_raw_value_approximation_error ?zero_sequence ?negative_value 0 =
        slp_restrict_field X u"
    by (rule ext)
      (simp add: slp_raw_value_approximation_error_def)
  have raw_value_lp:
      "aim_complex_lp_on_plane p
        (slp_raw_value_approximation_error ?zero_sequence ?negative_value 0)"
    unfolding raw_value_presentation by (rule value_lp)
  have raw_value_support:
      "slp_raw_value_approximation_error ?zero_sequence ?negative_value 0 y
          \<noteq> 0 \<Longrightarrow> norm (z - y) \<le> R" for y
    unfolding slp_raw_value_approximation_error_def
    by (rule value_support) simp
  have base_lp:
      "aim_complex_lp_on_plane p
        (\<lambda>x. (slp_point_as_complex (x - c) *
          slp_center_kernel tau c x) * slp_restrict_field X u x)"
  proof -
    have base_presentation:
        "slp_oscillatory_base_approximation_error tau c
            ?zero_sequence ?negative_value 0 =
          (\<lambda>x. (slp_point_as_complex (x - c) *
            slp_center_kernel tau c x) * slp_restrict_field X u x)"
      by (rule ext)
        (simp only: slp_oscillatory_base_approximation_error_factorization
          raw_value_presentation)
    have dummy:
        "aim_complex_lp_on_plane p
          (slp_oscillatory_base_approximation_error tau c
            ?zero_sequence ?negative_value 0)"
      by (rule slp_oscillatory_base_approximation_error_lp[OF
            exponent_positive radius_nonnegative raw_value_lp
            raw_value_support])
    show ?thesis unfolding base_presentation[symmetric] by (rule dummy)
  qed
  have base_support:
      "(slp_point_as_complex (y - c) * slp_center_kernel tau c y) *
          slp_restrict_field X u y \<noteq> 0 \<Longrightarrow>
        norm (z - y) \<le> R" for y
  proof (rule value_support)
    assume product_nonzero:
      "(slp_point_as_complex (y - c) * slp_center_kernel tau c y) *
        slp_restrict_field X u y \<noteq> 0"
    show "slp_restrict_field X u y \<noteq> 0"
    proof
      assume field_zero: "slp_restrict_field X u y = 0"
      have product_zero:
          "(slp_point_as_complex (y - c) * slp_center_kernel tau c y) *
            slp_restrict_field X u y = 0"
        by (simp only: field_zero mult_zero_right)
      show False by (rule notE[OF product_nonzero product_zero])
    qed
  qed
  show "slp_cauchy_integrable_at SLP_Partial_Inverse
      (\<lambda>x. (slp_point_as_complex (x - c) *
        slp_center_kernel tau c x) * slp_restrict_field X u x) z"
    using slp_cauchy_scaled_young_bound_on_bounded_support[OF
      exponent_above_two radius_nonnegative zero_less_one base_lp
      base_support, where orientation=SLP_Partial_Inverse]
    by blast

  have derivative_lp:
      "aim_complex_lp_on_plane p
        (slp_restrict_field X (slp_gradient_wirtinger_partial Du))"
    using slp_w1p_restricted_gradient_wirtinger_partial_data(1)[OF
      exponent_one_le pair]
    by (simp only: slp_gradient_wirtinger_partial_restrict_gradient)
  have center_measurable:
      "slp_center_kernel tau c \<in> borel_measurable lborel"
    by (rule slp_center_kernel_measurable)
  have center_bound:
      "\<And>x. norm (slp_center_kernel tau c x) \<le> (1::real)"
    by simp
  have derivative_source_lp:
      "aim_complex_lp_on_plane p
        (\<lambda>x. slp_center_kernel tau c x *
          slp_restrict_field X (slp_gradient_wirtinger_partial Du) x)"
    by (rule slp_complex_lp_bounded_multiplier(1)[OF exponent_positive
          center_measurable center_bound zero_le_one derivative_lp])
  have derivative_support:
      "slp_center_kernel tau c y *
          slp_restrict_field X (slp_gradient_wirtinger_partial Du) y \<noteq> 0
        \<Longrightarrow> norm (z - y) \<le> R" for y
  proof -
    assume nonzero:
      "slp_center_kernel tau c y *
        slp_restrict_field X (slp_gradient_wirtinger_partial Du) y \<noteq> 0"
    have restricted_nonzero:
        "slp_restrict_field X (slp_gradient_wirtinger_partial Du) y \<noteq> 0"
    proof
      assume field_zero:
        "slp_restrict_field X (slp_gradient_wirtinger_partial Du) y = 0"
      have product_zero:
          "slp_center_kernel tau c y *
            slp_restrict_field X (slp_gradient_wirtinger_partial Du) y = 0"
        by (simp only: field_zero mult_zero_right)
      show False by (rule notE[OF nonzero product_zero])
    qed
    have "y \<in> X"
      using restricted_nonzero unfolding slp_restrict_field_def
      by (cases "y \<in> X") auto
    then show "norm (z - y) \<le> R" by (rule X_radius)
  qed
  show "slp_cauchy_integrable_at SLP_Partial_Inverse
      (\<lambda>x. slp_center_kernel tau c x *
        slp_restrict_field X (slp_gradient_wirtinger_partial Du) x) z"
    using slp_cauchy_scaled_young_bound_on_bounded_support[OF
      exponent_above_two radius_nonnegative zero_less_one
      derivative_source_lp derivative_support,
      where orientation=SLP_Partial_Inverse]
    by blast
qed

context aim_planar_cauchy_test_left_inverse
begin

theorem slp_w1p_partial_inverse_oscillatory_divided_rough_far_product_of_pair:
  fixes p R :: real
  assumes tau_positive: "0 < tau"
    and exponent_above_two: "2 < p"
    and radius_nonnegative: "0 \<le> R"
    and phi_test: "\<And>n. slp_test_function_on X (phi n)"
    and error_pairs:
      "\<And>n. slp_w1p_pair_on p X
        (\<lambda>x. phi n x - u x)
        (\<lambda>x. slp_classical_gradient (phi n) x - Du x)"
    and error_norm_tends:
      "((\<lambda>n. slp_w1p_norm_on p X
          (\<lambda>x. phi n x - u x)
          (\<lambda>x. slp_classical_gradient (phi n) x - Du x))
        \<longlongrightarrow> 0) sequentially"
    and pair: "slp_w1p_pair_on p X u Du"
    and X_radius: "\<And>y. y \<in> X \<Longrightarrow> norm (z - y) \<le> R"
    and pointwise_limit:
      "((\<lambda>n. phi n z) \<longlongrightarrow> slp_restrict_field X u z)
        sequentially"
  shows "slp_partial_inverse
      (\<lambda>x. (slp_point_as_complex (x - c) *
        slp_center_kernel tau c x) * slp_restrict_field X u x) z =
    (1 / (\<i> * of_real tau)) *
      (slp_center_kernel tau c z * slp_restrict_field X u z -
        slp_partial_inverse
          (\<lambda>x. slp_center_kernel tau c x *
            slp_restrict_field X
              (slp_gradient_wirtinger_partial Du) x) z)"
proof -
  note targets = slp_w1p_rough_far_target_cauchy_integrable[OF
    exponent_above_two radius_nonnegative pair X_radius,
    where tau=tau and c=c]
  show ?thesis
    by (rule slp_w1p_partial_inverse_oscillatory_divided_rough_far_product[OF
          tau_positive exponent_above_two radius_nonnegative phi_test
          error_pairs error_norm_tends X_radius targets(1) targets(2)
          pointwise_limit])
qed

end

end
