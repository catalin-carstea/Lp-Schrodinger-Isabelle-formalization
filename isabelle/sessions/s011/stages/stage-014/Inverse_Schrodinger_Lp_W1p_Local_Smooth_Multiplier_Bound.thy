theory Inverse_Schrodinger_Lp_W1p_Local_Smooth_Multiplier_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Local_Smooth_Multiplier"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Coarse_Triangle"
begin

section \<open>Quantitative local Sobolev multiplication\<close>

lemma slp_complex_lp_on_bounded_multiplier_norm:
  assumes exponent_positive: "0 < p"
    and X_measurable: "X \<in> sets lborel"
    and multiplier_measurable: "a \<in> borel_measurable lborel"
    and multiplier_bound:
      "\<And>x. x \<in> X \<Longrightarrow> Real_Vector_Spaces.norm (a x) \<le> A"
    and bound_nonnegative: "0 \<le> A"
    and function_lp: "slp_complex_lp_on p X f"
  shows product_lp: "slp_complex_lp_on p X (\<lambda>x. a x * f x)"
    and product_norm_bound:
      "slp_complex_lp_norm_on p X (\<lambda>x. a x * f x) \<le>
        A * slp_complex_lp_norm_on p X f"
proof -
  let ?ra = "slp_restrict_field X a"
  have restricted_multiplier_measurable:
      "?ra \<in> borel_measurable lborel"
    by (rule slp_restrict_field_measurable[OF
      X_measurable multiplier_measurable])
  have restricted_multiplier_bound:
      "Real_Vector_Spaces.norm (?ra x) \<le> A" for x
    using multiplier_bound[of x] bound_nonnegative
    by (cases "x \<in> X") (simp_all add: slp_restrict_field_def)
  have restricted_function_lp:
      "aim_complex_lp_on_plane p (slp_restrict_field X f)"
    using function_lp unfolding slp_complex_lp_on_def .
  note product = slp_complex_lp_bounded_multiplier[
    OF exponent_positive restricted_multiplier_measurable
      restricted_multiplier_bound bound_nonnegative restricted_function_lp]
  have product_presentation:
      "slp_restrict_field X (\<lambda>x. a x * f x) =
        (\<lambda>x. ?ra x * slp_restrict_field X f x)"
    by (rule ext) (simp add: slp_restrict_field_def)
  show "slp_complex_lp_on p X (\<lambda>x. a x * f x)"
    unfolding slp_complex_lp_on_def product_presentation
    by (rule product(1))
  show "slp_complex_lp_norm_on p X (\<lambda>x. a x * f x) \<le>
      A * slp_complex_lp_norm_on p X f"
    unfolding slp_complex_lp_norm_on_def product_presentation
    by (rule product(2))
qed

lemma slp_complex_lp_on_add_norm_triangle:
  assumes exponent_one_le: "1 \<le> p"
    and first_lp: "slp_complex_lp_on p X f"
    and second_lp: "slp_complex_lp_on p X g"
  shows sum_lp: "slp_complex_lp_on p X (\<lambda>x. f x + g x)"
    and sum_norm_bound:
      "slp_complex_lp_norm_on p X (\<lambda>x. f x + g x) \<le>
        4 * (slp_complex_lp_norm_on p X f +
          slp_complex_lp_norm_on p X g)"
proof -
  have first_plane:
      "aim_complex_lp_on_plane p (slp_restrict_field X f)"
    using first_lp unfolding slp_complex_lp_on_def .
  have second_plane:
      "aim_complex_lp_on_plane p (slp_restrict_field X g)"
    using second_lp unfolding slp_complex_lp_on_def .
  note sum_data = slp_complex_lp_add_norm_coarse_triangle[
    OF exponent_one_le first_plane second_plane]
  have sum_presentation:
      "slp_restrict_field X (\<lambda>x. f x + g x) =
        (\<lambda>x. slp_restrict_field X f x + slp_restrict_field X g x)"
    by (rule ext) (simp add: slp_restrict_field_def)
  show "slp_complex_lp_on p X (\<lambda>x. f x + g x)"
    unfolding slp_complex_lp_on_def sum_presentation
    by (rule sum_data(1))
  show "slp_complex_lp_norm_on p X (\<lambda>x. f x + g x) \<le>
      4 * (slp_complex_lp_norm_on p X f +
        slp_complex_lp_norm_on p X g)"
    unfolding slp_complex_lp_norm_on_def sum_presentation
    by (rule sum_data(2))
qed

theorem slp_w1p_norm_on_mult_smooth_bounded:
  assumes exponent_one_le: "1 \<le> p"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and pair: "slp_w1p_pair_on p X u Du"
    and multiplier_smooth: "smooth_on UNIV a"
    and value_bound:
      "\<And>x. x \<in> X \<Longrightarrow> Real_Vector_Spaces.norm (a x) \<le> A"
    and derivative_zero_bound:
      "\<And>x. x \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm (slp_complex_partial_derivative a 0 x) \<le> B0"
    and derivative_one_bound:
      "\<And>x. x \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm (slp_complex_partial_derivative a 1 x) \<le> B1"
    and A_nonnegative: "0 \<le> A"
    and B0_nonnegative: "0 \<le> B0"
    and B1_nonnegative: "0 \<le> B1"
  shows "slp_w1p_norm_on p X
      (\<lambda>x. a x * u x)
      (\<lambda>x. \<chi> i. a x * Du x $ i +
        u x * slp_complex_partial_derivative a i x)
    \<le> 4 * (9 * A + 4 * B0 + 4 * B1) *
      slp_w1p_norm_on p X u Du"
proof -
  have exponent_positive: "0 < p"
    using exponent_one_le by linarith
  let ?v = "\<lambda>x. a x * u x"
  let ?Dv = "\<lambda>x. \<chi> i. a x * Du x $ i +
    u x * slp_complex_partial_derivative a i x"
  let ?W = "slp_w1p_norm_on p X u Du"
  let ?F = "slp_complex_lp_norm_on p X u"
  let ?D0 = "slp_complex_lp_norm_on p X (\<lambda>x. Du x $ 0)"
  let ?D1 = "slp_complex_lp_norm_on p X (\<lambda>x. Du x $ 1)"
  have output_pair: "slp_w1p_pair_on p X ?v ?Dv"
    by (rule slp_w1p_pair_on_mult_smooth_bounded[OF
      exponent_one_le X_measurable X_bounded pair multiplier_smooth])
  have multiplier_measurable: "a \<in> borel_measurable lborel"
    using borel_measurable_continuous_onI[
      OF smooth_on_imp_continuous_on[OF multiplier_smooth]] by simp
  have value_data:
      "slp_complex_lp_on p X ?v \<and>
        slp_complex_lp_norm_on p X ?v \<le> A * ?F"
    using slp_complex_lp_on_bounded_multiplier_norm[
      OF exponent_positive X_measurable multiplier_measurable value_bound
        A_nonnegative slp_w1p_pair_onD(2)[OF pair]] by blast
  have derivative_data:
      "slp_complex_lp_norm_on p X (\<lambda>x. ?Dv x $ i) \<le>
        4 * (A * slp_complex_lp_norm_on p X (\<lambda>x. Du x $ i) +
          (if i = 0 then B0 else B1) * ?F)" for i
  proof -
    have derivative_smooth:
        "smooth_on UNIV (slp_complex_partial_derivative a i)"
      by (rule slp_complex_partial_derivative_smooth[OF multiplier_smooth])
    have derivative_measurable:
        "slp_complex_partial_derivative a i \<in> borel_measurable lborel"
      using borel_measurable_continuous_onI[
        OF smooth_on_imp_continuous_on[OF derivative_smooth]] by simp
    have two_eq_zero: "(2 :: 2) = 0"
      by (simp add: of_nat_eq_0_iff_char_dvd)
    have component_lp: "slp_complex_lp_on p X (\<lambda>x. Du x $ i)"
      using slp_w1p_pair_onD(3)[OF pair]
        slp_w1p_pair_onD(4)[OF pair] exhaust_2[of i] two_eq_zero
      by auto
    have derivative_bound:
        "Real_Vector_Spaces.norm
          (slp_complex_partial_derivative a i x) \<le>
          (if i = 0 then B0 else B1)" if "x \<in> X" for x
      using derivative_zero_bound[OF that] derivative_one_bound[OF that]
        exhaust_2[of i] two_eq_zero by auto
    have derivative_constant_nonnegative:
        "0 \<le> (if i = 0 then B0 else B1)"
      using B0_nonnegative B1_nonnegative by simp
    note first_data = slp_complex_lp_on_bounded_multiplier_norm[
      OF exponent_positive X_measurable multiplier_measurable value_bound
        A_nonnegative component_lp]
    note second_data = slp_complex_lp_on_bounded_multiplier_norm[
      OF exponent_positive X_measurable derivative_measurable derivative_bound
        derivative_constant_nonnegative slp_w1p_pair_onD(2)[OF pair]]
    have second_commuted_lp:
        "slp_complex_lp_on p X
          (\<lambda>x. u x * slp_complex_partial_derivative a i x)"
      using second_data(1) by (simp add: mult.commute)
    have second_commuted_norm:
        "slp_complex_lp_norm_on p X
            (\<lambda>x. u x * slp_complex_partial_derivative a i x) =
          slp_complex_lp_norm_on p X
            (\<lambda>x. slp_complex_partial_derivative a i x * u x)"
      by (simp add: mult.commute)
    note sum_data = slp_complex_lp_on_add_norm_triangle[
      OF exponent_one_le first_data(1) second_commuted_lp]
    have sum_presentation:
        "(\<lambda>x. ?Dv x $ i) =
          (\<lambda>x. a x * Du x $ i +
            u x * slp_complex_partial_derivative a i x)"
      by simp
    have norm_bound:
        "slp_complex_lp_norm_on p X (\<lambda>x. ?Dv x $ i) \<le>
          4 * (slp_complex_lp_norm_on p X (\<lambda>x. a x * Du x $ i) +
          slp_complex_lp_norm_on p X
            (\<lambda>x. u x * slp_complex_partial_derivative a i x))"
      unfolding sum_presentation by (rule sum_data(2))
    have first_norm:
        "slp_complex_lp_norm_on p X (\<lambda>x. a x * Du x $ i) \<le>
          A * slp_complex_lp_norm_on p X (\<lambda>x. Du x $ i)"
      by (rule first_data(2))
    have second_norm:
        "slp_complex_lp_norm_on p X
            (\<lambda>x. u x * slp_complex_partial_derivative a i x) \<le>
          (if i = 0 then B0 else B1) * ?F"
      unfolding second_commuted_norm by (rule second_data(2))
    have scaled_norm_bound:
        "4 * (slp_complex_lp_norm_on p X (\<lambda>x. a x * Du x $ i) +
          slp_complex_lp_norm_on p X
            (\<lambda>x. u x * slp_complex_partial_derivative a i x)) \<le>
          4 * (A * slp_complex_lp_norm_on p X (\<lambda>x. Du x $ i) +
            (if i = 0 then B0 else B1) * ?F)"
      by (rule mult_left_mono[OF add_mono[OF first_norm second_norm]]) simp
    show ?thesis
      by (rule order_trans[OF norm_bound scaled_norm_bound])
  qed
  have component_sum_bound:
      "slp_w1p_norm_on p X ?v ?Dv \<le>
        4 * (slp_complex_lp_norm_on p X ?v +
          slp_complex_lp_norm_on p X (\<lambda>x. ?Dv x $ 0) +
          slp_complex_lp_norm_on p X (\<lambda>x. ?Dv x $ 1))"
    using slp_w1p_norm_on_component_sum_bound[
      OF exponent_one_le output_pair]
    unfolding slp_complex_lp_norm_on_def .
  have value_norm: "slp_complex_lp_norm_on p X ?v \<le> A * ?F"
    using value_data by blast
  have derivative_zero_norm:
      "slp_complex_lp_norm_on p X (\<lambda>x. ?Dv x $ 0) \<le>
        4 * (A * ?D0 + B0 * ?F)"
    using derivative_data[of 0] by simp
  have derivative_one_norm:
      "slp_complex_lp_norm_on p X (\<lambda>x. ?Dv x $ 1) \<le>
        4 * (A * ?D1 + B1 * ?F)"
    using derivative_data[of 1] by simp
  have component_total_bound:
      "slp_complex_lp_norm_on p X ?v +
          slp_complex_lp_norm_on p X (\<lambda>x. ?Dv x $ 0) +
          slp_complex_lp_norm_on p X (\<lambda>x. ?Dv x $ 1) \<le>
        A * ?F + 4 * (A * ?D0 + B0 * ?F) +
          4 * (A * ?D1 + B1 * ?F)"
    by (rule add_mono[OF add_mono[OF value_norm derivative_zero_norm]
      derivative_one_norm])
  have raw_bound:
      "slp_w1p_norm_on p X ?v ?Dv \<le>
        4 * (A * ?F + 4 * (A * ?D0 + B0 * ?F) +
          4 * (A * ?D1 + B1 * ?F))"
    by (rule order_trans[OF component_sum_bound
      mult_left_mono[OF component_total_bound]]) simp
  note input_components = slp_w1p_norm_on_component_bounds[
    OF exponent_positive pair]
  have F_bound: "?F \<le> ?W"
    using input_components(1)
    unfolding slp_complex_lp_norm_on_def by blast
  have D0_bound: "?D0 \<le> ?W"
    using input_components(2)
    unfolding slp_complex_lp_norm_on_def by blast
  have D1_bound: "?D1 \<le> ?W"
    using input_components(3)
    unfolding slp_complex_lp_norm_on_def by blast
  have AF_bound: "A * ?F \<le> A * ?W"
    by (rule mult_left_mono[OF F_bound A_nonnegative])
  have AD0_bound: "A * ?D0 \<le> A * ?W"
    by (rule mult_left_mono[OF D0_bound A_nonnegative])
  have AD1_bound: "A * ?D1 \<le> A * ?W"
    by (rule mult_left_mono[OF D1_bound A_nonnegative])
  have B0F_bound: "B0 * ?F \<le> B0 * ?W"
    by (rule mult_left_mono[OF F_bound B0_nonnegative])
  have B1F_bound: "B1 * ?F \<le> B1 * ?W"
    by (rule mult_left_mono[OF F_bound B1_nonnegative])
  show ?thesis
    using raw_bound AF_bound AD0_bound AD1_bound B0F_bound B1F_bound
    by (simp add: algebra_simps)
qed

end
