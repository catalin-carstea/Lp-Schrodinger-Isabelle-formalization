theory Inverse_Schrodinger_Lp_CGO_Second_Weak_Wirtinger
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_CGO_Wirtinger_Projection"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_W1p_Zero_Pair_Exponent_Descent"
begin

section \<open>Opposite Wirtinger projection of a smooth weak product\<close>

definition slp_classical_wirtinger_dbar ::
  "slp_scalar_field \<Rightarrow> slp_scalar_field"
where
  "slp_classical_wirtinger_dbar a x =
    (slp_complex_partial_derivative a 0 x +
      \<i> * slp_complex_partial_derivative a 1 x) / 2"

lemma slp_wirtinger_dbar_product_algebra:
  "((a * d0 + u * e0) + \<i> * (a * d1 + u * e1)) / 2 =
    a * ((d0 + \<i> * d1) / 2) +
      u * ((e0 + \<i> * e1) / 2)"
proof -
  have numerator:
      "(a * d0 + u * e0) + \<i> * (a * d1 + u * e1) =
        a * (d0 + \<i> * d1) + u * (e0 + \<i> * e1)"
    by (simp add: algebra_simps)
  have first:
      "((a * d0 + u * e0) + \<i> * (a * d1 + u * e1)) / 2 =
        (a * (d0 + \<i> * d1) + u * (e0 + \<i> * e1)) / 2"
    by (simp only: numerator)
  have second:
      "(a * (d0 + \<i> * d1) + u * (e0 + \<i> * e1)) / 2 =
        (a * (d0 + \<i> * d1)) / 2 +
          (u * (e0 + \<i> * e1)) / 2"
    by (rule add_divide_distrib)
  have third:
      "(a * (d0 + \<i> * d1)) / 2 +
          (u * (e0 + \<i> * e1)) / 2 =
        a * ((d0 + \<i> * d1) / 2) +
          u * ((e0 + \<i> * e1) / 2)"
    by simp
  show ?thesis
    by (rule trans[OF first trans[OF second third]])
qed

lemma slp_product_gradient_wirtinger_dbar:
  "slp_gradient_wirtinger_dbar
      (\<lambda>x. \<chi> i. a x * Du x $ i +
        u x * slp_complex_partial_derivative a i x) =
    (\<lambda>x. a x * slp_gradient_wirtinger_dbar Du x +
      u x * slp_classical_wirtinger_dbar a x)"
  unfolding slp_gradient_wirtinger_dbar_def
    slp_classical_wirtinger_dbar_def
  by (rule ext) (simp only: vec_lambda_beta
      slp_wirtinger_dbar_product_algebra)

lemma slp_weak_gradient_on_cong_on:
  assumes X_measurable: "X \<in> sets lborel"
    and source: "slp_weak_gradient_on X u Du"
    and equality: "\<And>x. x \<in> X \<Longrightarrow> u x = v x"
  shows "slp_weak_gradient_on X v Du"
  unfolding slp_weak_gradient_on_def
proof (intro allI impI)
  fix phi i
  assume phi_test: "slp_test_function_on X phi"
  have source_data:
      "set_integrable lborel X
          (\<lambda>x. u x * slp_complex_partial_derivative phi i x) \<and>
       set_integrable lborel X (\<lambda>x. Du x $ i * phi x) \<and>
       set_lebesgue_integral lborel X
          (\<lambda>x. u x * slp_complex_partial_derivative phi i x) =
        - set_lebesgue_integral lborel X (\<lambda>x. Du x $ i * phi x)"
    using source phi_test unfolding slp_weak_gradient_on_def by blast
  have left_integrable_equality:
      "set_integrable lborel X
          (\<lambda>x. u x * slp_complex_partial_derivative phi i x) =
       set_integrable lborel X
          (\<lambda>x. v x * slp_complex_partial_derivative phi i x)"
  proof (rule set_integrable_cong)
    show "lborel = lborel" by (rule refl)
    show "X = X" by (rule refl)
    fix x
    assume x_in: "x \<in> X"
    show "u x * slp_complex_partial_derivative phi i x =
        v x * slp_complex_partial_derivative phi i x"
      by (simp only: equality[OF x_in])
  qed
  have left_integral_equality:
      "set_lebesgue_integral lborel X
          (\<lambda>x. u x * slp_complex_partial_derivative phi i x) =
       set_lebesgue_integral lborel X
          (\<lambda>x. v x * slp_complex_partial_derivative phi i x)"
  proof (rule set_lebesgue_integral_cong[OF X_measurable])
    show "\<forall>x. x \<in> X \<longrightarrow>
        u x * slp_complex_partial_derivative phi i x =
          v x * slp_complex_partial_derivative phi i x"
      by (intro allI impI) (simp only: equality)
  qed
  have target_left_integrable:
      "set_integrable lborel X
        (\<lambda>x. v x * slp_complex_partial_derivative phi i x)"
  proof -
    have source_left_integrable:
        "set_integrable lborel X
          (\<lambda>x. u x * slp_complex_partial_derivative phi i x)"
      using source_data by blast
    show ?thesis
      using source_left_integrable left_integrable_equality by simp
  qed
  have target_right_integrable:
      "set_integrable lborel X (\<lambda>x. Du x $ i * phi x)"
    using source_data by blast
  have target_integral:
      "set_lebesgue_integral lborel X
          (\<lambda>x. v x * slp_complex_partial_derivative phi i x) =
        - set_lebesgue_integral lborel X (\<lambda>x. Du x $ i * phi x)"
  proof -
    have source_integral:
        "set_lebesgue_integral lborel X
            (\<lambda>x. u x * slp_complex_partial_derivative phi i x) =
          - set_lebesgue_integral lborel X (\<lambda>x. Du x $ i * phi x)"
      using source_data by blast
    show ?thesis
      by (rule trans[OF sym[OF left_integral_equality] source_integral])
  qed
  show
      "set_integrable lborel X
          (\<lambda>x. v x * slp_complex_partial_derivative phi i x) \<and>
       set_integrable lborel X (\<lambda>x. Du x $ i * phi x) \<and>
       set_lebesgue_integral lborel X
          (\<lambda>x. v x * slp_complex_partial_derivative phi i x) =
        - set_lebesgue_integral lborel X (\<lambda>x. Du x $ i * phi x)"
    using target_left_integrable target_right_integrable target_integral
    by blast
qed

lemma slp_gradient_components_lp_add_fields:
  assumes exponent_positive: "0 < p"
    and first: "slp_gradient_components_lp p Du"
    and second: "slp_gradient_components_lp p Dv"
  shows "slp_gradient_components_lp p (\<lambda>x. Du x + Dv x)"
  unfolding slp_gradient_components_lp_def
proof (intro conjI)
  have first_zero:
      "aim_complex_lp_on_plane p (\<lambda>x. Du x $ 0)"
    using first unfolding slp_gradient_components_lp_def by blast
  have first_one:
      "aim_complex_lp_on_plane p (\<lambda>x. Du x $ 1)"
    using first unfolding slp_gradient_components_lp_def by blast
  have second_zero:
      "aim_complex_lp_on_plane p (\<lambda>x. Dv x $ 0)"
    using second unfolding slp_gradient_components_lp_def by blast
  have second_one:
      "aim_complex_lp_on_plane p (\<lambda>x. Dv x $ 1)"
    using second unfolding slp_gradient_components_lp_def by blast
  show "aim_complex_lp_on_plane p (\<lambda>x. (Du x + Dv x) $ 0)"
    unfolding vector_add_component
    by (rule aim_complex_lp_on_plane_add[OF
          exponent_positive first_zero second_zero])
  show "aim_complex_lp_on_plane p (\<lambda>x. (Du x + Dv x) $ 1)"
    unfolding vector_add_component
    by (rule aim_complex_lp_on_plane_add[OF
          exponent_positive first_one second_one])
qed

lemma slp_w1p_pair_on_add_fields:
  assumes exponent_one_le: "1 \<le> p"
    and first: "slp_w1p_pair_on p X u Du"
    and second: "slp_w1p_pair_on p X v Dv"
  shows "slp_w1p_pair_on p X
    (\<lambda>x. u x + v x) (\<lambda>x. Du x + Dv x)"
proof -
  have zero_raw:
      "slp_w1p_pair_on p X
        (\<lambda>x. u x - u x) (\<lambda>x. Du x - Du x)"
    by (rule slp_w1p_pair_on_diff[OF exponent_one_le first first])
  have zero:
      "slp_w1p_pair_on p X
        (\<lambda>_. (0::complex)) (\<lambda>_. (0::complex ^ 2))"
    using zero_raw by simp
  have negative_raw:
      "slp_w1p_pair_on p X
        (\<lambda>x. (0::complex) - v x)
        (\<lambda>x. (0::complex ^ 2) - Dv x)"
    by (rule slp_w1p_pair_on_diff[OF exponent_one_le zero second])
  have negative:
      "slp_w1p_pair_on p X
        (\<lambda>x. - v x) (\<lambda>x. - Dv x)"
    using negative_raw by simp
  have sum_raw:
      "slp_w1p_pair_on p X
        (\<lambda>x. u x - (- v x)) (\<lambda>x. Du x - (- Dv x))"
    by (rule slp_w1p_pair_on_diff[OF exponent_one_le first negative])
  show ?thesis
    using sum_raw by simp
qed

section \<open>Affine factors and their exact Cartesian gradients\<close>

definition slp_left_cgo_affine_factor ::
  "real \<Rightarrow> slp_point \<Rightarrow> slp_scalar_field"
where
  "slp_left_cgo_affine_factor tau c z =
    \<i> * of_real tau * slp_point_as_complex (z - c)"

definition slp_left_cgo_affine_gradient ::
  "real \<Rightarrow> slp_gradient_field"
where
  "slp_left_cgo_affine_gradient tau z =
    (\<chi> i. \<i> * of_real tau * slp_point_as_complex (axis i 1))"

definition slp_right_cgo_affine_factor ::
  "real \<Rightarrow> slp_point \<Rightarrow> slp_scalar_field"
where
  "slp_right_cgo_affine_factor tau c z =
    \<i> * of_real tau * cnj (slp_point_as_complex (z - c))"

definition slp_right_cgo_affine_gradient ::
  "real \<Rightarrow> slp_gradient_field"
where
  "slp_right_cgo_affine_gradient tau z =
    (\<chi> i. \<i> * of_real tau * cnj (slp_point_as_complex (axis i 1)))"

lemma slp_left_cgo_affine_factor_smooth:
  "smooth_on UNIV (slp_left_cgo_affine_factor tau c)"
  unfolding slp_left_cgo_affine_factor_def
  by (rule smooth_on_mult[OF smooth_on_const
        slp_shifted_point_as_complex_smooth open_UNIV])

lemma slp_right_cgo_affine_factor_smooth:
  "smooth_on UNIV (slp_right_cgo_affine_factor tau c)"
proof -
  have conjugated_smooth:
      "smooth_on UNIV
        (\<lambda>z :: slp_point. cnj (slp_point_as_complex (z - c)))"
    by (rule slp_smooth_on_cnj[OF slp_shifted_point_as_complex_smooth])
  show ?thesis
    unfolding slp_right_cgo_affine_factor_def
    by (rule smooth_on_mult[OF smooth_on_const
          conjugated_smooth open_UNIV])
qed

lemma slp_left_cgo_affine_factor_partial_derivative:
  "slp_complex_partial_derivative
      (slp_left_cgo_affine_factor tau c) i z =
    slp_left_cgo_affine_gradient tau z $ i"
proof -
  have shifted:
      "((\<lambda>y :: slp_point. slp_point_as_complex (y - c)) has_derivative
        slp_point_as_complex) (at z)"
  proof -
    have shift:
        "((\<lambda>y :: slp_point. y - c) has_derivative id) (at z)"
      by (auto intro!: derivative_eq_intros)
    have coordinate:
        "(slp_point_as_complex has_derivative slp_point_as_complex)
          (at (z - c))"
      using bounded_linear.has_derivative[OF
          slp_point_as_complex_bounded_linear has_derivative_id]
      by (simp only: id_apply)
    show ?thesis
      using has_derivative_compose[OF shift coordinate]
      by (simp only: id_apply)
  qed
  have scaled:
      "((\<lambda>u :: complex. \<i> * of_real tau * u) has_derivative
        (\<lambda>h. \<i> * of_real tau * h))
        (at (slp_point_as_complex (z - c)))"
    using bounded_linear.has_derivative[OF
        bounded_linear_mult_right has_derivative_id]
    by (simp only: id_apply)
  have derivative:
      "((slp_left_cgo_affine_factor tau c) has_derivative
        (\<lambda>h. \<i> * of_real tau * slp_point_as_complex h)) (at z)"
    unfolding slp_left_cgo_affine_factor_def
    by (rule has_derivative_compose[OF shifted scaled])
  have frechet:
      "frechet_derivative (slp_left_cgo_affine_factor tau c) (at z) =
        (\<lambda>h. \<i> * of_real tau * slp_point_as_complex h)"
    by (rule sym, rule frechet_derivative_at[OF derivative])
  show ?thesis
    unfolding slp_complex_partial_derivative_def
      slp_left_cgo_affine_gradient_def frechet
    by (simp only: vec_lambda_beta)
qed

lemma slp_right_cgo_affine_factor_partial_derivative:
  "slp_complex_partial_derivative
      (slp_right_cgo_affine_factor tau c) i z =
    slp_right_cgo_affine_gradient tau z $ i"
proof -
  have shifted:
      "((\<lambda>y :: slp_point. slp_point_as_complex (y - c)) has_derivative
        slp_point_as_complex) (at z)"
  proof -
    have shift:
        "((\<lambda>y :: slp_point. y - c) has_derivative id) (at z)"
      by (auto intro!: derivative_eq_intros)
    have coordinate:
        "(slp_point_as_complex has_derivative slp_point_as_complex)
          (at (z - c))"
      using bounded_linear.has_derivative[OF
          slp_point_as_complex_bounded_linear has_derivative_id]
      by (simp only: id_apply)
    show ?thesis
      using has_derivative_compose[OF shift coordinate]
      by (simp only: id_apply)
  qed
  have conjugated:
      "((\<lambda>y :: slp_point. cnj (slp_point_as_complex (y - c)))
        has_derivative (\<lambda>h. cnj (slp_point_as_complex h))) (at z)"
    by (rule has_derivative_cnj[OF shifted])
  have scaled:
      "((\<lambda>u :: complex. \<i> * of_real tau * u) has_derivative
        (\<lambda>h. \<i> * of_real tau * h))
        (at (cnj (slp_point_as_complex (z - c))))"
    using bounded_linear.has_derivative[OF
        bounded_linear_mult_right has_derivative_id]
    by (simp only: id_apply)
  have derivative:
      "((slp_right_cgo_affine_factor tau c) has_derivative
        (\<lambda>h. \<i> * of_real tau * cnj (slp_point_as_complex h)))
        (at z)"
    unfolding slp_right_cgo_affine_factor_def
    by (rule has_derivative_compose[OF conjugated scaled])
  have frechet:
      "frechet_derivative (slp_right_cgo_affine_factor tau c) (at z) =
        (\<lambda>h. \<i> * of_real tau * cnj (slp_point_as_complex h))"
    by (rule sym, rule frechet_derivative_at[OF derivative])
  show ?thesis
    unfolding slp_complex_partial_derivative_def
      slp_right_cgo_affine_gradient_def frechet
    by (simp only: vec_lambda_beta)
qed

lemma slp_point_as_complex_axis_zero:
  "slp_point_as_complex (axis (0 :: 2) (1 :: real)) = 1"
  unfolding slp_point_as_complex_def
  by (rule complex_eqI; simp)

lemma slp_point_as_complex_axis_one:
  "slp_point_as_complex (axis (1 :: 2) (1 :: real)) = \<i>"
  unfolding slp_point_as_complex_def
  by (rule complex_eqI; simp)

lemma slp_holomorphic_scalar_dbar_zero:
  "(a + \<i> * (a * \<i>)) / 2 = 0"
  by (simp add: algebra_simps)

lemma slp_antiholomorphic_scalar_partial_zero:
  "(a - \<i> * (a * (- \<i>))) / 2 = 0"
  by (simp add: algebra_simps)

lemma slp_left_cgo_affine_gradient_dbar:
  "slp_gradient_wirtinger_dbar (slp_left_cgo_affine_gradient tau) =
    (\<lambda>_. 0)"
proof (rule ext)
  fix x
  let ?a = "\<i> * of_real tau"
  have component_zero:
      "slp_left_cgo_affine_gradient tau x $ 0 = ?a"
    unfolding slp_left_cgo_affine_gradient_def
    by (simp only: vec_lambda_beta slp_point_as_complex_axis_zero
          mult.right_neutral)
  have component_one:
      "slp_left_cgo_affine_gradient tau x $ 1 = ?a * \<i>"
    unfolding slp_left_cgo_affine_gradient_def
    by (simp only: vec_lambda_beta slp_point_as_complex_axis_one)
  show "slp_gradient_wirtinger_dbar
      (slp_left_cgo_affine_gradient tau) x = (\<lambda>_. 0) x"
    unfolding slp_gradient_wirtinger_dbar_def
    by (simp only: component_zero component_one
          slp_holomorphic_scalar_dbar_zero)
qed

lemma slp_right_cgo_affine_gradient_partial:
  "slp_gradient_wirtinger_partial (slp_right_cgo_affine_gradient tau) =
    (\<lambda>_. 0)"
proof (rule ext)
  fix x
  let ?a = "\<i> * of_real tau"
  have component_zero:
      "slp_right_cgo_affine_gradient tau x $ 0 = ?a"
    unfolding slp_right_cgo_affine_gradient_def
    by (simp only: vec_lambda_beta slp_point_as_complex_axis_zero
          complex_cnj_one mult.right_neutral)
  have component_one:
      "slp_right_cgo_affine_gradient tau x $ 1 = ?a * (- \<i>)"
    unfolding slp_right_cgo_affine_gradient_def
    by (simp only: vec_lambda_beta slp_point_as_complex_axis_one
          complex_cnj_i)
  show "slp_gradient_wirtinger_partial
      (slp_right_cgo_affine_gradient tau) x = (\<lambda>_. 0) x"
    unfolding slp_gradient_wirtinger_partial_def
    by (simp only: component_zero component_one
          slp_antiholomorphic_scalar_partial_zero)
qed

lemma slp_holomorphic_quadratic_phase_classical_dbar:
  "slp_classical_wirtinger_dbar
      (slp_holomorphic_quadratic_phase_multiplier tau c) =
    (\<lambda>_. 0)"
proof (rule ext)
  fix x
  let ?a = "slp_holomorphic_quadratic_phase_multiplier tau c x *
    (\<i> * of_real tau * slp_point_as_complex (x - c))"
  have component_zero:
      "slp_complex_partial_derivative
          (slp_holomorphic_quadratic_phase_multiplier tau c) 0 x = ?a"
    by (simp only:
          slp_holomorphic_quadratic_phase_multiplier_partial_derivative
          slp_point_as_complex_axis_zero mult.right_neutral)
  have component_one:
      "slp_complex_partial_derivative
          (slp_holomorphic_quadratic_phase_multiplier tau c) 1 x = ?a * \<i>"
    by (simp only:
          slp_holomorphic_quadratic_phase_multiplier_partial_derivative
          slp_point_as_complex_axis_one mult.assoc)
  show "slp_classical_wirtinger_dbar
      (slp_holomorphic_quadratic_phase_multiplier tau c) x =
        (\<lambda>_. 0) x"
    unfolding slp_classical_wirtinger_dbar_def
    by (simp only: component_zero component_one
          slp_holomorphic_scalar_dbar_zero)
qed

lemma slp_antiholomorphic_quadratic_phase_classical_partial:
  "slp_classical_wirtinger_partial
      (slp_antiholomorphic_quadratic_phase_multiplier tau c) =
    (\<lambda>_. 0)"
proof (rule ext)
  fix x
  let ?a = "slp_antiholomorphic_quadratic_phase_multiplier tau c x *
    (\<i> * of_real tau * cnj (slp_point_as_complex (x - c)))"
  have component_zero:
      "slp_complex_partial_derivative
          (slp_antiholomorphic_quadratic_phase_multiplier tau c) 0 x = ?a"
    by (simp only:
          slp_antiholomorphic_quadratic_phase_multiplier_partial_derivative
          slp_point_as_complex_axis_zero complex_cnj_one mult.right_neutral)
  have component_one:
      "slp_complex_partial_derivative
          (slp_antiholomorphic_quadratic_phase_multiplier tau c) 1 x =
        ?a * (- \<i>)"
    by (simp only:
          slp_antiholomorphic_quadratic_phase_multiplier_partial_derivative
          slp_point_as_complex_axis_one complex_cnj_i mult.assoc)
  show "slp_classical_wirtinger_partial
      (slp_antiholomorphic_quadratic_phase_multiplier tau c) x =
        (\<lambda>_. 0) x"
    unfolding slp_classical_wirtinger_partial_def
    by (simp only: component_zero component_one
          slp_antiholomorphic_scalar_partial_zero)
qed

section \<open>Named second Cartesian gradients\<close>

definition slp_left_cgo_partial_second_gradient ::
    "real \<Rightarrow> slp_point \<Rightarrow> slp_scalar_field \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_gradient_field"
where
  "slp_left_cgo_partial_second_gradient tau c coefficient W z =
    (\<chi> i.
      slp_holomorphic_quadratic_phase_multiplier tau c z *
        (slp_left_cgo_affine_gradient tau z $ i +
          slp_left_conjugated_cauchy_source_gradient tau c coefficient
            (\<lambda>y. coefficient y * W y) z $ i) +
      (slp_left_cgo_affine_factor tau c z +
        slp_left_conjugated_cauchy_source tau c coefficient
          (\<lambda>y. coefficient y * W y) z) *
        slp_complex_partial_derivative
          (slp_holomorphic_quadratic_phase_multiplier tau c) i z)"

definition slp_right_cgo_dbar_second_gradient ::
    "real \<Rightarrow> slp_point \<Rightarrow> slp_scalar_field \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_gradient_field"
where
  "slp_right_cgo_dbar_second_gradient tau c coefficient W z =
    (\<chi> i.
      slp_antiholomorphic_quadratic_phase_multiplier tau c z *
        (slp_right_cgo_affine_gradient tau z $ i +
          slp_right_conjugated_cauchy_source_gradient tau c coefficient
            (\<lambda>y. coefficient y * W y) z $ i) +
      (slp_right_cgo_affine_factor tau c z +
        slp_right_conjugated_cauchy_source tau c coefficient
          (\<lambda>y. coefficient y * W y) z) *
        slp_complex_partial_derivative
          (slp_antiholomorphic_quadratic_phase_multiplier tau c) i z)"

context slp_cauchy_outer_fixed_point
begin

theorem slp_both_cgo_projection_second_weak_wirtinger_on_cutoff_one:
  fixes p M tau :: real
    and c :: slp_point
    and X Omega :: "slp_point set"
    and cutoff coefficient W :: slp_scalar_field
  assumes exponent_lower: "1 < (p::real)"
    and exponent_upper: "p < 2"
    and X_open: "open X"
    and X_bounded: "bounded X"
    and cutoff_test: "slp_test_function_on X cutoff"
    and coefficient_lp: "aim_complex_lp_on_plane p coefficient"
    and coefficient_support: "{x. coefficient x \<noteq> 0} \<subseteq> X"
    and W_admissible: "slp_ae_bounded_measurable lborel M W"
    and Omega_measurable: "Omega \<in> sets (lborel :: slp_point measure)"
    and Omega_bounded: "bounded Omega"
    and cutoff_one: "\<And>z. z \<in> Omega \<Longrightarrow> cutoff z = 1"
  shows
    "slp_weak_gradient_on Omega
        (slp_gradient_wirtinger_partial
          (slp_left_cgo_gradient tau c W
            (slp_left_outer_conjugated_gradient
              tau c cutoff coefficient W)))
        (slp_left_cgo_partial_second_gradient tau c coefficient W)
      \<and>
      slp_gradient_wirtinger_dbar
          (slp_left_cgo_partial_second_gradient tau c coefficient W) =
        (\<lambda>z. coefficient z * slp_left_cgo_field tau c W z)
      \<and>
      slp_weak_gradient_on Omega
        (slp_gradient_wirtinger_dbar
          (slp_right_cgo_gradient tau c W
            (slp_right_outer_conjugated_gradient
              tau c cutoff coefficient W)))
        (slp_right_cgo_dbar_second_gradient tau c coefficient W)
      \<and>
      slp_gradient_wirtinger_partial
          (slp_right_cgo_dbar_second_gradient tau c coefficient W) =
        (\<lambda>z. coefficient z * slp_right_cgo_field tau c W z)"
proof -
  let ?source = "\<lambda>x. coefficient x * W x"
  let ?modulated = "slp_oscillatory_modulation (- tau) c ?source"
  let ?left =
    "slp_left_conjugated_cauchy_source tau c coefficient ?source"
  let ?Dleft =
    "slp_left_conjugated_cauchy_source_gradient tau c coefficient ?source"
  let ?right =
    "slp_right_conjugated_cauchy_source tau c coefficient ?source"
  let ?Dright =
    "slp_right_conjugated_cauchy_source_gradient tau c coefficient ?source"

  have exponent_positive: "0 < p" and exponent_one_le: "1 \<le> p"
    using exponent_lower by linarith+
  have M_nonnegative: "0 \<le> M"
    and W_measurable: "W \<in> borel_measurable lborel"
    and W_bound:
      "AE x in lborel. Real_Vector_Spaces.norm (W x) \<le> M"
    using W_admissible unfolding slp_ae_bounded_measurable_def by blast+
  have source_lp: "aim_complex_lp_on_plane p ?source"
  proof -
    have raw:
        "aim_complex_lp_on_plane p (\<lambda>x. W x * coefficient x)"
      by (rule slp_complex_lp_AE_bounded_multiplier(1)[OF
            exponent_positive W_measurable W_bound M_nonnegative
            coefficient_lp])
    show ?thesis
      using raw by (simp only: mult.commute)
  qed
  have source_support_subset:
      "{x. ?source x \<noteq> 0} \<subseteq> {x. coefficient x \<noteq> 0}"
    by auto
  have coefficient_support_bounded:
      "bounded {x. coefficient x \<noteq> 0}"
    by (rule bounded_subset[OF X_bounded coefficient_support])
  have source_support_bounded: "bounded {x. ?source x \<noteq> 0}"
    by (rule bounded_subset[OF coefficient_support_bounded
          source_support_subset])
  have modulated_lp: "aim_complex_lp_on_plane p ?modulated"
    using source_lp by simp

  note inner_data = slp_both_conjugated_cauchy_sources_weak_wirtinger[OF
    exponent_lower coefficient_lp coefficient_support_bounded source_lp
    source_support_bounded]
  have left_weak_UNIV: "slp_weak_gradient_on UNIV ?left ?Dleft"
    using inner_data by blast
  have right_weak_UNIV: "slp_weak_gradient_on UNIV ?right ?Dright"
    using inner_data by blast
  have left_inner_projection:
      "slp_gradient_wirtinger_dbar ?Dleft =
        (\<lambda>x. coefficient x + ?modulated x)"
    using inner_data by blast
  have right_inner_projection:
      "slp_gradient_wirtinger_partial ?Dright =
        (\<lambda>x. coefficient x + ?modulated x)"
    using inner_data by blast

  note cutoff_data = slp_both_cutoff_conjugated_sources_lp_support[OF
    exponent_lower X_open X_bounded cutoff_test coefficient_lp
    coefficient_support W_admissible]
  have left_cutoff_plane:
      "aim_complex_lp_on_plane p (\<lambda>x. cutoff x * ?left x)"
    using cutoff_data by blast
  have right_cutoff_plane:
      "aim_complex_lp_on_plane p (\<lambda>x. cutoff x * ?right x)"
    using cutoff_data by blast
  have left_cutoff_local:
      "slp_complex_lp_on p Omega (\<lambda>x. cutoff x * ?left x)"
    by (rule aim_complex_lp_on_plane_restrict[OF
          exponent_positive Omega_measurable left_cutoff_plane])
  have right_cutoff_local:
      "slp_complex_lp_on p Omega (\<lambda>x. cutoff x * ?right x)"
    by (rule aim_complex_lp_on_plane_restrict[OF
          exponent_positive Omega_measurable right_cutoff_plane])
  have left_restrict:
      "slp_restrict_field Omega ?left =
        slp_restrict_field Omega (\<lambda>x. cutoff x * ?left x)"
    by (rule ext) (simp add: slp_restrict_field_def cutoff_one)
  have right_restrict:
      "slp_restrict_field Omega ?right =
        slp_restrict_field Omega (\<lambda>x. cutoff x * ?right x)"
    by (rule ext) (simp add: slp_restrict_field_def cutoff_one)
  have left_local: "slp_complex_lp_on p Omega ?left"
    using left_cutoff_local unfolding slp_complex_lp_on_def left_restrict .
  have right_local: "slp_complex_lp_on p Omega ?right"
    using right_cutoff_local unfolding slp_complex_lp_on_def right_restrict .

  note coefficient_components =
    slp_both_cauchy_gradient_components_lp[OF exponent_lower coefficient_lp]
  note modulated_components =
    slp_both_cauchy_gradient_components_lp[OF exponent_lower modulated_lp]
  have left_components_global: "slp_gradient_components_lp p ?Dleft"
    unfolding slp_left_conjugated_cauchy_source_gradient_def
    by (rule slp_gradient_components_lp_add_fields[OF exponent_positive])
       (use coefficient_components modulated_components in blast)+
  have right_components_global: "slp_gradient_components_lp p ?Dright"
    unfolding slp_right_conjugated_cauchy_source_gradient_def
    by (rule slp_gradient_components_lp_add_fields[OF exponent_positive])
       (use coefficient_components modulated_components in blast)+
  have left_components_local:
      "slp_complex_lp_on p Omega (\<lambda>x. ?Dleft x $ 0) \<and>
       slp_complex_lp_on p Omega (\<lambda>x. ?Dleft x $ 1)"
    by (rule slp_gradient_components_lp_restrict[OF
          exponent_positive Omega_measurable left_components_global])
  have right_components_local:
      "slp_complex_lp_on p Omega (\<lambda>x. ?Dright x $ 0) \<and>
       slp_complex_lp_on p Omega (\<lambda>x. ?Dright x $ 1)"
    by (rule slp_gradient_components_lp_restrict[OF
          exponent_positive Omega_measurable right_components_global])
  have left_source_pair: "slp_w1p_pair_on p Omega ?left ?Dleft"
    unfolding slp_w1p_pair_on_def
    using slp_weak_gradient_on_UNIV_imp_on[OF left_weak_UNIV]
      left_local left_components_local by blast
  have right_source_pair: "slp_w1p_pair_on p Omega ?right ?Dright"
    unfolding slp_w1p_pair_on_def
    using slp_weak_gradient_on_UNIV_imp_on[OF right_weak_UNIV]
      right_local right_components_local by blast

  have one_h1:
      "slp_h1_pair_on Omega
        (\<lambda>_. (1::complex)) (\<lambda>_. (0::complex ^ 2))"
    by (rule slp_h1_pair_on_const_bounded[OF
          Omega_measurable Omega_bounded])
  have left_affine_h1_raw:
      "slp_h1_pair_on Omega
        (\<lambda>x. slp_left_cgo_affine_factor tau c x * 1)
        (\<lambda>x. \<chi> i.
          slp_left_cgo_affine_factor tau c x * (0::complex ^ 2) $ i +
          1 * slp_complex_partial_derivative
            (slp_left_cgo_affine_factor tau c) i x)"
    by (rule slp_h1_pair_on_mult_smooth_bounded[OF
          Omega_measurable Omega_bounded one_h1
          slp_left_cgo_affine_factor_smooth])
  have left_affine_h1:
      "slp_h1_pair_on Omega
        (slp_left_cgo_affine_factor tau c)
        (slp_left_cgo_affine_gradient tau)"
    using left_affine_h1_raw
    by (simp only: zero_index mult_zero_right add_0 mult.left_neutral
          mult.right_neutral
          slp_left_cgo_affine_factor_partial_derivative vec_lambda_eta)
  have right_affine_h1_raw:
      "slp_h1_pair_on Omega
        (\<lambda>x. slp_right_cgo_affine_factor tau c x * 1)
        (\<lambda>x. \<chi> i.
          slp_right_cgo_affine_factor tau c x * (0::complex ^ 2) $ i +
          1 * slp_complex_partial_derivative
            (slp_right_cgo_affine_factor tau c) i x)"
    by (rule slp_h1_pair_on_mult_smooth_bounded[OF
          Omega_measurable Omega_bounded one_h1
          slp_right_cgo_affine_factor_smooth])
  have right_affine_h1:
      "slp_h1_pair_on Omega
        (slp_right_cgo_affine_factor tau c)
        (slp_right_cgo_affine_gradient tau)"
    using right_affine_h1_raw
    by (simp only: zero_index mult_zero_right add_0 mult.left_neutral
          mult.right_neutral
          slp_right_cgo_affine_factor_partial_derivative vec_lambda_eta)
  have left_affine_two:
      "slp_w1p_pair_on 2 Omega
        (slp_left_cgo_affine_factor tau c)
        (slp_left_cgo_affine_gradient tau)"
    by (rule slp_h1_pair_on_w1p_pair_on_two[OF
          Omega_measurable left_affine_h1])
  have right_affine_two:
      "slp_w1p_pair_on 2 Omega
        (slp_right_cgo_affine_factor tau c)
        (slp_right_cgo_affine_gradient tau)"
    by (rule slp_h1_pair_on_w1p_pair_on_two[OF
          Omega_measurable right_affine_h1])
  have left_affine_pair:
      "slp_w1p_pair_on p Omega
        (slp_left_cgo_affine_factor tau c)
        (slp_left_cgo_affine_gradient tau)"
    by (rule slp_w1p_norm_on_mono_exponent_bounded(1)[OF
          exponent_one_le exponent_upper Omega_measurable Omega_bounded
          left_affine_two])
  have right_affine_pair:
      "slp_w1p_pair_on p Omega
        (slp_right_cgo_affine_factor tau c)
        (slp_right_cgo_affine_gradient tau)"
    by (rule slp_w1p_norm_on_mono_exponent_bounded(1)[OF
          exponent_one_le exponent_upper Omega_measurable Omega_bounded
          right_affine_two])

  have left_bracket_pair:
      "slp_w1p_pair_on p Omega
        (\<lambda>x. slp_left_cgo_affine_factor tau c x + ?left x)
        (\<lambda>x. slp_left_cgo_affine_gradient tau x + ?Dleft x)"
    by (rule slp_w1p_pair_on_add_fields[OF
          exponent_one_le left_affine_pair left_source_pair])
  have right_bracket_pair:
      "slp_w1p_pair_on p Omega
        (\<lambda>x. slp_right_cgo_affine_factor tau c x + ?right x)
        (\<lambda>x. slp_right_cgo_affine_gradient tau x + ?Dright x)"
    by (rule slp_w1p_pair_on_add_fields[OF
          exponent_one_le right_affine_pair right_source_pair])
  have left_product_pair:
      "slp_w1p_pair_on p Omega
        (\<lambda>x. slp_holomorphic_quadratic_phase_multiplier tau c x *
          (slp_left_cgo_affine_factor tau c x + ?left x))
        (slp_left_cgo_partial_second_gradient tau c coefficient W)"
  proof -
    have raw:
        "slp_w1p_pair_on p Omega
          (\<lambda>x. slp_holomorphic_quadratic_phase_multiplier tau c x *
            (slp_left_cgo_affine_factor tau c x + ?left x))
          (\<lambda>x. \<chi> i.
            slp_holomorphic_quadratic_phase_multiplier tau c x *
              (slp_left_cgo_affine_gradient tau x + ?Dleft x) $ i +
            (slp_left_cgo_affine_factor tau c x + ?left x) *
              slp_complex_partial_derivative
                (slp_holomorphic_quadratic_phase_multiplier tau c) i x)"
      by (rule slp_w1p_pair_on_mult_smooth_bounded[OF
            exponent_one_le Omega_measurable Omega_bounded left_bracket_pair
            slp_holomorphic_quadratic_phase_multiplier_has_derivative(2)])
    show ?thesis
      using raw
      unfolding slp_left_cgo_partial_second_gradient_def
      by (simp only: vector_add_component)
  qed
  have right_product_pair:
      "slp_w1p_pair_on p Omega
        (\<lambda>x. slp_antiholomorphic_quadratic_phase_multiplier tau c x *
          (slp_right_cgo_affine_factor tau c x + ?right x))
        (slp_right_cgo_dbar_second_gradient tau c coefficient W)"
  proof -
    have raw:
        "slp_w1p_pair_on p Omega
          (\<lambda>x. slp_antiholomorphic_quadratic_phase_multiplier tau c x *
            (slp_right_cgo_affine_factor tau c x + ?right x))
          (\<lambda>x. \<chi> i.
            slp_antiholomorphic_quadratic_phase_multiplier tau c x *
              (slp_right_cgo_affine_gradient tau x + ?Dright x) $ i +
            (slp_right_cgo_affine_factor tau c x + ?right x) *
              slp_complex_partial_derivative
                (slp_antiholomorphic_quadratic_phase_multiplier tau c) i x)"
      by (rule slp_w1p_pair_on_mult_smooth_bounded[OF
            exponent_one_le Omega_measurable Omega_bounded right_bracket_pair
            slp_antiholomorphic_quadratic_phase_multiplier_has_derivative(2)])
    show ?thesis
      using raw
      unfolding slp_right_cgo_dbar_second_gradient_def
      by (simp only: vector_add_component)
  qed

  have left_product_weak:
      "slp_weak_gradient_on Omega
        (\<lambda>x. slp_holomorphic_quadratic_phase_multiplier tau c x *
          (slp_left_cgo_affine_factor tau c x + ?left x))
        (slp_left_cgo_partial_second_gradient tau c coefficient W)"
    using left_product_pair unfolding slp_w1p_pair_on_def by blast
  have right_product_weak:
      "slp_weak_gradient_on Omega
        (\<lambda>x. slp_antiholomorphic_quadratic_phase_multiplier tau c x *
          (slp_right_cgo_affine_factor tau c x + ?right x))
        (slp_right_cgo_dbar_second_gradient tau c coefficient W)"
    using right_product_pair unfolding slp_w1p_pair_on_def by blast

  have left_actual:
      "slp_gradient_wirtinger_partial
          (slp_left_cgo_gradient tau c W
            (slp_left_outer_conjugated_gradient
              tau c cutoff coefficient W)) =
        (\<lambda>z. slp_holomorphic_quadratic_phase_multiplier tau c z *
          (slp_left_cgo_affine_factor tau c z + cutoff z * ?left z))"
    using slp_left_cgo_gradient_wirtinger_partial[OF
      exponent_lower X_open X_bounded cutoff_test coefficient_lp
      coefficient_support W_admissible]
    unfolding slp_left_cgo_affine_factor_def .
  have right_actual:
      "slp_gradient_wirtinger_dbar
          (slp_right_cgo_gradient tau c W
            (slp_right_outer_conjugated_gradient
              tau c cutoff coefficient W)) =
        (\<lambda>z. slp_antiholomorphic_quadratic_phase_multiplier tau c z *
          (slp_right_cgo_affine_factor tau c z + cutoff z * ?right z))"
    using slp_right_cgo_gradient_wirtinger_dbar[OF
      exponent_lower X_open X_bounded cutoff_test coefficient_lp
      coefficient_support W_admissible]
    unfolding slp_right_cgo_affine_factor_def .
  have left_actual_at:
      "slp_gradient_wirtinger_partial
          (slp_left_cgo_gradient tau c W
            (slp_left_outer_conjugated_gradient
              tau c cutoff coefficient W)) z =
        slp_holomorphic_quadratic_phase_multiplier tau c z *
          (slp_left_cgo_affine_factor tau c z + cutoff z * ?left z)" for z
    by (rule fun_cong[OF left_actual])
  have right_actual_at:
      "slp_gradient_wirtinger_dbar
          (slp_right_cgo_gradient tau c W
            (slp_right_outer_conjugated_gradient
              tau c cutoff coefficient W)) z =
        slp_antiholomorphic_quadratic_phase_multiplier tau c z *
          (slp_right_cgo_affine_factor tau c z + cutoff z * ?right z)" for z
    by (rule fun_cong[OF right_actual])
  have left_weak:
      "slp_weak_gradient_on Omega
        (slp_gradient_wirtinger_partial
          (slp_left_cgo_gradient tau c W
            (slp_left_outer_conjugated_gradient
              tau c cutoff coefficient W)))
        (slp_left_cgo_partial_second_gradient tau c coefficient W)"
    by (rule slp_weak_gradient_on_cong_on[OF Omega_measurable
          left_product_weak])
       (use left_actual_at cutoff_one in simp)
  have right_weak:
      "slp_weak_gradient_on Omega
        (slp_gradient_wirtinger_dbar
          (slp_right_cgo_gradient tau c W
            (slp_right_outer_conjugated_gradient
              tau c cutoff coefficient W)))
        (slp_right_cgo_dbar_second_gradient tau c coefficient W)"
    by (rule slp_weak_gradient_on_cong_on[OF Omega_measurable
          right_product_weak])
       (use right_actual_at cutoff_one in simp)

  have left_second_projection:
      "slp_gradient_wirtinger_dbar
          (slp_left_cgo_partial_second_gradient tau c coefficient W) =
        (\<lambda>z. coefficient z * slp_left_cgo_field tau c W z)"
  proof -
    have raw:
        "slp_gradient_wirtinger_dbar
            (slp_left_cgo_partial_second_gradient tau c coefficient W) =
          (\<lambda>z.
            slp_holomorphic_quadratic_phase_multiplier tau c z *
              slp_gradient_wirtinger_dbar
                (\<lambda>x. slp_left_cgo_affine_gradient tau x + ?Dleft x) z +
            (slp_left_cgo_affine_factor tau c z + ?left z) *
              slp_classical_wirtinger_dbar
                (slp_holomorphic_quadratic_phase_multiplier tau c) z)"
    proof -
      have native:
          "slp_gradient_wirtinger_dbar
              (\<lambda>z. \<chi> i.
                slp_holomorphic_quadratic_phase_multiplier tau c z *
                  (slp_left_cgo_affine_gradient tau z + ?Dleft z) $ i +
                (slp_left_cgo_affine_factor tau c z + ?left z) *
                  slp_complex_partial_derivative
                    (slp_holomorphic_quadratic_phase_multiplier tau c) i z) =
            (\<lambda>z.
              slp_holomorphic_quadratic_phase_multiplier tau c z *
                slp_gradient_wirtinger_dbar
                  (\<lambda>x. slp_left_cgo_affine_gradient tau x + ?Dleft x) z +
              (slp_left_cgo_affine_factor tau c z + ?left z) *
                slp_classical_wirtinger_dbar
                  (slp_holomorphic_quadratic_phase_multiplier tau c) z)"
        by (rule slp_product_gradient_wirtinger_dbar)
      show ?thesis
        using native
        unfolding slp_left_cgo_partial_second_gradient_def
        by (simp only: vector_add_component)
    qed
    have bracket_projection:
        "slp_gradient_wirtinger_dbar
            (\<lambda>x. slp_left_cgo_affine_gradient tau x + ?Dleft x) =
          (\<lambda>x. coefficient x + ?modulated x)"
      using left_inner_projection
      by (simp only: slp_gradient_wirtinger_dbar_add
            slp_left_cgo_affine_gradient_dbar add.left_neutral)
    show ?thesis
    proof (rule ext)
      fix z
      have factorized:
          "slp_left_cgo_field tau c W z =
            slp_holomorphic_quadratic_phase_multiplier tau c z *
              (1 + slp_center_kernel (- tau) c z * W z)"
        using slp_cgo_fields_factorized by blast
      show
          "slp_gradient_wirtinger_dbar
              (slp_left_cgo_partial_second_gradient tau c coefficient W) z =
            coefficient z * slp_left_cgo_field tau c W z"
        using fun_cong[OF raw, of z]
        unfolding bracket_projection
          slp_holomorphic_quadratic_phase_classical_dbar
          slp_oscillatory_modulation_def factorized
        by (simp add: algebra_simps)
    qed
  qed

  have right_second_projection:
      "slp_gradient_wirtinger_partial
          (slp_right_cgo_dbar_second_gradient tau c coefficient W) =
        (\<lambda>z. coefficient z * slp_right_cgo_field tau c W z)"
  proof -
    have raw:
        "slp_gradient_wirtinger_partial
            (slp_right_cgo_dbar_second_gradient tau c coefficient W) =
          (\<lambda>z.
            slp_antiholomorphic_quadratic_phase_multiplier tau c z *
              slp_gradient_wirtinger_partial
                (\<lambda>x. slp_right_cgo_affine_gradient tau x + ?Dright x) z +
            (slp_right_cgo_affine_factor tau c z + ?right z) *
              slp_classical_wirtinger_partial
                (slp_antiholomorphic_quadratic_phase_multiplier tau c) z)"
    proof -
      have native:
          "slp_gradient_wirtinger_partial
              (\<lambda>z. \<chi> i.
                slp_antiholomorphic_quadratic_phase_multiplier tau c z *
                  (slp_right_cgo_affine_gradient tau z + ?Dright z) $ i +
                (slp_right_cgo_affine_factor tau c z + ?right z) *
                  slp_complex_partial_derivative
                    (slp_antiholomorphic_quadratic_phase_multiplier tau c) i z) =
            (\<lambda>z.
              slp_antiholomorphic_quadratic_phase_multiplier tau c z *
                slp_gradient_wirtinger_partial
                  (\<lambda>x. slp_right_cgo_affine_gradient tau x + ?Dright x) z +
              (slp_right_cgo_affine_factor tau c z + ?right z) *
                slp_classical_wirtinger_partial
                  (slp_antiholomorphic_quadratic_phase_multiplier tau c) z)"
        by (rule slp_product_gradient_wirtinger_partial)
      show ?thesis
        using native
        unfolding slp_right_cgo_dbar_second_gradient_def
        by (simp only: vector_add_component)
    qed
    have bracket_projection:
        "slp_gradient_wirtinger_partial
            (\<lambda>x. slp_right_cgo_affine_gradient tau x + ?Dright x) =
          (\<lambda>x. coefficient x + ?modulated x)"
      using right_inner_projection
      by (simp only: slp_gradient_wirtinger_partial_add
            slp_right_cgo_affine_gradient_partial add.left_neutral)
    show ?thesis
    proof (rule ext)
      fix z
      have factorized:
          "slp_right_cgo_field tau c W z =
            slp_antiholomorphic_quadratic_phase_multiplier tau c z *
              (1 + slp_center_kernel (- tau) c z * W z)"
        using slp_cgo_fields_factorized by blast
      show
          "slp_gradient_wirtinger_partial
              (slp_right_cgo_dbar_second_gradient tau c coefficient W) z =
            coefficient z * slp_right_cgo_field tau c W z"
        using fun_cong[OF raw, of z]
        unfolding bracket_projection
          slp_antiholomorphic_quadratic_phase_classical_partial
          slp_oscillatory_modulation_def factorized
        by (simp add: algebra_simps)
    qed
  qed

  show ?thesis
    using left_weak left_second_projection right_weak right_second_projection
    by blast
qed

end

end
