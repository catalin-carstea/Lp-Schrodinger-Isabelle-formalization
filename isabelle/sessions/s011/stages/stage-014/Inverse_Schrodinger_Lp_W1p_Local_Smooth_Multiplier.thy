theory Inverse_Schrodinger_Lp_W1p_Local_Smooth_Multiplier
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Pair_AE_Transport"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Weak_Product_Rule"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Complex_Lp_Bounded_Multiplier"
begin

section \<open>Local Sobolev pairs under smooth multiplication\<close>

lemma slp_complex_lp_on_mult_smooth_bounded:
  assumes exponent_positive: "0 < p"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and function_lp: "slp_complex_lp_on p X f"
    and multiplier_smooth: "smooth_on UNIV a"
  shows "slp_complex_lp_on p X (\<lambda>x. a x * f x)"
proof -
  have closure_compact: "compact (closure X)"
    using X_bounded by simp
  have multiplier_continuous: "continuous_on UNIV a"
    by (rule smooth_on_imp_continuous_on[OF multiplier_smooth])
  have multiplier_continuous_closure: "continuous_on (closure X) a"
    by (rule continuous_on_subset[OF multiplier_continuous]) simp
  obtain C where C_nonnegative: "0 \<le> C"
    and multiplier_bound:
      "\<And>x. x \<in> closure X \<Longrightarrow>
        Real_Vector_Spaces.norm (a x) \<le> C"
    using continuous_on_compact_bound[OF
      closure_compact multiplier_continuous_closure]
    by blast
  have multiplier_measurable: "a \<in> borel_measurable lborel"
    using borel_measurable_continuous_onI[OF multiplier_continuous]
    by simp
  let ?ra = "slp_restrict_field X a"
  have restricted_multiplier_measurable:
      "?ra \<in> borel_measurable lborel"
    using X_measurable multiplier_measurable
    unfolding slp_restrict_field_def by measurable
  have restricted_multiplier_bound:
      "Real_Vector_Spaces.norm (?ra x) \<le> C" for x
  proof (cases "x \<in> X")
    case True
    then have "x \<in> closure X" by simp
    then show ?thesis
      using multiplier_bound[of x] True
      by (simp add: slp_restrict_field_def)
  next
    case False
    then show ?thesis
      using C_nonnegative by (simp add: slp_restrict_field_def)
  qed
  have restricted_function_lp:
      "aim_complex_lp_on_plane p (slp_restrict_field X f)"
    using function_lp unfolding slp_complex_lp_on_def .
  have product_lp:
      "aim_complex_lp_on_plane p
        (\<lambda>x. ?ra x * slp_restrict_field X f x)"
    by (rule slp_complex_lp_bounded_multiplier(1)[OF
      exponent_positive restricted_multiplier_measurable
      restricted_multiplier_bound C_nonnegative restricted_function_lp])
  have product_presentation:
      "slp_restrict_field X (\<lambda>x. a x * f x) =
        (\<lambda>x. ?ra x * slp_restrict_field X f x)"
    by (rule ext) (simp add: slp_restrict_field_def)
  show ?thesis
    unfolding slp_complex_lp_on_def product_presentation
    by (rule product_lp)
qed

theorem slp_w1p_pair_on_mult_smooth_bounded:
  assumes exponent_one_le: "1 \<le> p"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and pair: "slp_w1p_pair_on p X u Du"
    and multiplier_smooth: "smooth_on UNIV a"
  shows "slp_w1p_pair_on p X
    (\<lambda>x. a x * u x)
    (\<lambda>x. \<chi> i. a x * Du x $ i +
      u x * slp_complex_partial_derivative a i x)"
proof -
  have exponent_positive: "0 < p"
    using exponent_one_le by linarith
  let ?ru = "slp_restrict_field X u"
  let ?rDu = "\<lambda>x. \<chi> i.
    slp_restrict_field X (\<lambda>y. Du y $ i) x"
  let ?v = "\<lambda>x. a x * u x"
  let ?Dv = "\<lambda>x. \<chi> i. a x * Du x $ i +
    u x * slp_complex_partial_derivative a i x"
  let ?rv = "\<lambda>x. a x * ?ru x"
  let ?rDv = "\<lambda>x. \<chi> i. a x * ?rDu x $ i +
    ?ru x * slp_complex_partial_derivative a i x"

  have ru_lp: "aim_complex_lp_on_plane p ?ru"
    using slp_w1p_pair_onD(2)[OF pair]
    unfolding slp_complex_lp_on_def .
  have rDu_zero_lp:
      "aim_complex_lp_on_plane p (\<lambda>x. ?rDu x $ 0)"
    using slp_w1p_pair_onD(3)[OF pair]
    unfolding slp_complex_lp_on_def by simp
  have rDu_one_lp:
      "aim_complex_lp_on_plane p (\<lambda>x. ?rDu x $ 1)"
    using slp_w1p_pair_onD(4)[OF pair]
    unfolding slp_complex_lp_on_def by simp
  have rDu_lp: "slp_gradient_components_lp p ?rDu"
    unfolding slp_gradient_components_lp_def
    using rDu_zero_lp rDu_one_lp by blast

  have ru_local_lp: "slp_complex_lp_on p X ?ru"
  proof -
    have presentation: "slp_restrict_field X ?ru = ?ru"
      by (rule ext) (simp add: slp_restrict_field_def)
    show ?thesis
      unfolding slp_complex_lp_on_def presentation
      by (rule ru_lp)
  qed
  have rDu_zero_local_lp:
      "slp_complex_lp_on p X (\<lambda>x. ?rDu x $ 0)"
  proof -
    have presentation:
        "slp_restrict_field X (\<lambda>x. ?rDu x $ 0) =
          (\<lambda>x. ?rDu x $ 0)"
      by (rule ext) (simp add: slp_restrict_field_def)
    show ?thesis
      unfolding slp_complex_lp_on_def presentation
      by (rule rDu_zero_lp)
  qed
  have rDu_one_local_lp:
      "slp_complex_lp_on p X (\<lambda>x. ?rDu x $ 1)"
  proof -
    have presentation:
        "slp_restrict_field X (\<lambda>x. ?rDu x $ 1) =
          (\<lambda>x. ?rDu x $ 1)"
      by (rule ext) (simp add: slp_restrict_field_def)
    show ?thesis
      unfolding slp_complex_lp_on_def presentation
      by (rule rDu_one_lp)
  qed
  have function_AE:
      "AE x in restrict_space lborel X. u x = ?ru x"
    using X_measurable
    by (simp add: AE_restrict_space_iff slp_restrict_field_def)
  have gradient_AE:
      "AE x in restrict_space lborel X. Du x = ?rDu x"
    using X_measurable
    by (simp add: AE_restrict_space_iff slp_restrict_field_def vec_eq_iff)
  have restricted_pair: "slp_w1p_pair_on p X ?ru ?rDu"
    by (rule slp_w1p_pair_on_cong_restrict_AE[OF
      X_measurable pair ru_local_lp rDu_zero_local_lp rDu_one_local_lp
      function_AE gradient_AE])
  have restricted_product_weak: "slp_weak_gradient_on X ?rv ?rDv"
    by (rule slp_weak_gradient_on_mult_smooth[OF
      exponent_one_le X_measurable X_bounded ru_lp rDu_lp
      multiplier_smooth slp_w1p_pair_onD(1)[OF restricted_pair]])

  have function_lp: "slp_complex_lp_on p X ?v"
    by (rule slp_complex_lp_on_mult_smooth_bounded[OF
      exponent_positive X_measurable X_bounded
      slp_w1p_pair_onD(2)[OF pair] multiplier_smooth])
  have derivative_lp:
      "slp_complex_lp_on p X (\<lambda>x. ?Dv x $ i)" for i
  proof -
    have derivative_smooth:
        "smooth_on UNIV (slp_complex_partial_derivative a i)"
      by (rule slp_complex_partial_derivative_smooth[OF multiplier_smooth])
    have first_lp:
        "slp_complex_lp_on p X (\<lambda>x. a x * Du x $ i)"
    proof -
      have two_eq_zero: "(2 :: 2) = 0"
        by (simp add: of_nat_eq_0_iff_char_dvd)
      have component_lp: "slp_complex_lp_on p X (\<lambda>x. Du x $ i)"
        using slp_w1p_pair_onD(3)[OF pair]
          slp_w1p_pair_onD(4)[OF pair] exhaust_2[of i] two_eq_zero
        by auto
      show ?thesis
        by (rule slp_complex_lp_on_mult_smooth_bounded[OF
          exponent_positive X_measurable X_bounded component_lp
          multiplier_smooth])
    qed
    have second_lp:
        "slp_complex_lp_on p X
          (\<lambda>x. slp_complex_partial_derivative a i x * u x)"
      by (rule slp_complex_lp_on_mult_smooth_bounded[OF
        exponent_positive X_measurable X_bounded
        slp_w1p_pair_onD(2)[OF pair] derivative_smooth])
    have second_lp_commuted:
        "slp_complex_lp_on p X
          (\<lambda>x. u x * slp_complex_partial_derivative a i x)"
      using second_lp by (simp add: mult.commute)
    have first_plane:
        "aim_complex_lp_on_plane p
          (slp_restrict_field X (\<lambda>x. a x * Du x $ i))"
      using first_lp unfolding slp_complex_lp_on_def .
    have second_plane:
        "aim_complex_lp_on_plane p
          (slp_restrict_field X
            (\<lambda>x. u x * slp_complex_partial_derivative a i x))"
      using second_lp_commuted unfolding slp_complex_lp_on_def .
    have sum_plane:
        "aim_complex_lp_on_plane p
          (\<lambda>x. slp_restrict_field X
              (\<lambda>y. a y * Du y $ i) x +
            slp_restrict_field X
              (\<lambda>y. u y * slp_complex_partial_derivative a i y) x)"
      by (rule aim_complex_lp_on_plane_add[OF
        exponent_positive first_plane second_plane])
    have sum_presentation:
        "slp_restrict_field X (\<lambda>x. ?Dv x $ i) =
          (\<lambda>x. slp_restrict_field X
              (\<lambda>y. a y * Du y $ i) x +
            slp_restrict_field X
              (\<lambda>y. u y * slp_complex_partial_derivative a i y) x)"
      by (rule ext) (simp add: slp_restrict_field_def)
    show ?thesis
      unfolding slp_complex_lp_on_def sum_presentation
      by (rule sum_plane)
  qed

  have restricted_product_function_lp: "slp_complex_lp_on p X ?rv"
  proof -
    have presentation:
        "slp_restrict_field X ?rv = slp_restrict_field X ?v"
      by (rule ext) (simp add: slp_restrict_field_def)
    show ?thesis
      using function_lp unfolding slp_complex_lp_on_def presentation .
  qed
  have restricted_product_derivative_lp:
      "slp_complex_lp_on p X (\<lambda>x. ?rDv x $ i)" for i
  proof -
    have presentation:
        "slp_restrict_field X (\<lambda>x. ?rDv x $ i) =
          slp_restrict_field X (\<lambda>x. ?Dv x $ i)"
      by (rule ext) (simp add: slp_restrict_field_def)
    show ?thesis
      using derivative_lp[of i]
      unfolding slp_complex_lp_on_def presentation .
  qed
  have restricted_product_pair: "slp_w1p_pair_on p X ?rv ?rDv"
    unfolding slp_w1p_pair_on_def
    using restricted_product_weak restricted_product_function_lp
      restricted_product_derivative_lp[of 0]
      restricted_product_derivative_lp[of 1]
    by blast
  have product_function_AE:
      "AE x in restrict_space lborel X. ?rv x = ?v x"
    using X_measurable
    by (simp add: AE_restrict_space_iff slp_restrict_field_def)
  have product_gradient_AE:
      "AE x in restrict_space lborel X. ?rDv x = ?Dv x"
    using X_measurable
    by (simp add: AE_restrict_space_iff slp_restrict_field_def vec_eq_iff)
  show ?thesis
    by (rule slp_w1p_pair_on_cong_restrict_AE[OF
      X_measurable restricted_product_pair function_lp
      derivative_lp[of 0] derivative_lp[of 1]
      product_function_AE product_gradient_AE])
qed

end
