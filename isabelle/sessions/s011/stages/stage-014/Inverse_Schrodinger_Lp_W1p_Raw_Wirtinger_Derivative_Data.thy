theory Inverse_Schrodinger_Lp_W1p_Raw_Wirtinger_Derivative_Data
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Derivative_Power_Convergence"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Wirtinger_Coordinate_Bound"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Approximation_Error_Factorization"
begin

section \<open>Restriction of a recorded weak gradient\<close>

definition slp_restrict_gradient ::
    "slp_point set \<Rightarrow> slp_gradient_field \<Rightarrow> slp_gradient_field"
where
  "slp_restrict_gradient X Du x =
    (\<chi> i. slp_restrict_field X (\<lambda>y. Du y $ i) x)"

lemma slp_restrict_gradient_component [simp]:
  "slp_restrict_gradient X Du x $ i =
    slp_restrict_field X (\<lambda>y. Du y $ i) x"
  by (simp add: slp_restrict_gradient_def)

lemma slp_gradient_wirtinger_partial_restrict_gradient:
  "slp_gradient_wirtinger_partial (slp_restrict_gradient X Du) =
    slp_restrict_field X (slp_gradient_wirtinger_partial Du)"
  by (rule ext)
    (simp add: slp_gradient_wirtinger_partial_def slp_restrict_field_def)

lemma slp_restrict_gradient_diff:
  "slp_restrict_gradient X (\<lambda>x. Du x - Dv x) =
    (\<lambda>x. slp_restrict_gradient X Du x - slp_restrict_gradient X Dv x)"
  by (rule ext)
    (simp add: slp_restrict_gradient_def slp_restrict_field_def vec_eq_iff)

lemma slp_restrict_gradient_classical_gradient:
  assumes phi_test: "slp_test_function_on X phi"
  shows "slp_restrict_gradient X (slp_classical_gradient phi) =
    slp_classical_gradient phi"
proof (rule ext)
  fix x :: slp_point
  show "slp_restrict_gradient X (slp_classical_gradient phi) x =
      slp_classical_gradient phi x"
    using slp_test_function_partial_restrict_field_eq[OF phi_test]
    by (simp add: slp_restrict_gradient_def slp_classical_gradient_def
      vec_eq_iff)
qed

lemma slp_gradient_wirtinger_partial_diff:
  "slp_gradient_wirtinger_partial (\<lambda>x. Du x - Dv x) =
    (\<lambda>x. slp_gradient_wirtinger_partial Du x -
      slp_gradient_wirtinger_partial Dv x)"
  by (rule ext)
    (simp add: slp_gradient_wirtinger_partial_def divide_simps algebra_simps)

lemma slp_gradient_wirtinger_partial_classical_gradient:
  "slp_gradient_wirtinger_partial (slp_classical_gradient phi) =
    slp_classical_wirtinger_partial phi"
  by (rule ext)
    (simp add: slp_gradient_wirtinger_partial_def
      slp_classical_gradient_def slp_classical_wirtinger_partial_def)

section \<open>Cartesian-to-Wirtinger comparison for recorded gradients\<close>

theorem slp_gradient_wirtinger_partial_lp_coordinate_bound:
  assumes exponent_one_le: "1 \<le> p"
    and component_zero_lp:
      "aim_complex_lp_on_plane p (\<lambda>x. Du x $ 0)"
    and component_one_lp:
      "aim_complex_lp_on_plane p (\<lambda>x. Du x $ 1)"
  shows gradient_partial_lp:
      "aim_complex_lp_on_plane p (slp_gradient_wirtinger_partial Du)"
    and gradient_partial_norm_bound:
      "aim_complex_lp_norm p (slp_gradient_wirtinger_partial Du) \<le>
        2 *
          (aim_complex_lp_norm p (\<lambda>x. Du x $ 0) +
            aim_complex_lp_norm p (\<lambda>x. Du x $ 1))"
proof -
  let ?d0 = "\<lambda>x. Du x $ 0"
  let ?d1 = "\<lambda>x. Du x $ 1"
  let ?rotated = "\<lambda>x. (- \<i>) * ?d1 x"
  let ?sum = "\<lambda>x. ?d0 x + ?rotated x"
  let ?halved = "\<lambda>x. (of_real (1 / 2) :: complex) * ?sum x"
  have exponent_positive: "0 < p"
    using exponent_one_le by linarith
  note rotated = slp_complex_lp_bounded_multiplier[
      where p = p and multiplier = "\<lambda>_::slp_point. - \<i>"
        and C = 1 and f = ?d1,
      OF exponent_positive _ _ _ component_one_lp]
  have rotated_measurable:
      "(\<lambda>_::slp_point. - \<i>) \<in> borel_measurable lborel"
    by measurable
  have rotated_bound: "\<And>x::slp_point. norm (- \<i>) \<le> (1::real)"
    by simp
  have rotated_nonnegative: "0 \<le> (1::real)"
    by simp
  note rotated_data = rotated[OF rotated_measurable rotated_bound
      rotated_nonnegative]
  note summed = slp_complex_lp_add_norm_coarse_triangle[OF exponent_one_le
      component_zero_lp rotated_data(1)]
  have half_measurable:
      "(\<lambda>_::slp_point. (of_real (1 / 2) :: complex))
        \<in> borel_measurable lborel"
    by measurable
  have half_bound:
      "\<And>x::slp_point. norm (of_real (1 / 2) :: complex) \<le> (1 / 2::real)"
    by simp
  have half_nonnegative: "0 \<le> (1 / 2::real)"
    by simp
  note halved = slp_complex_lp_bounded_multiplier[
      where p = p
        and multiplier = "\<lambda>_::slp_point. (of_real (1 / 2) :: complex)"
        and C = "1 / 2" and f = ?sum,
      OF exponent_positive half_measurable half_bound half_nonnegative
        summed(1)]
  have presentation: "?halved = slp_gradient_wirtinger_partial Du"
  proof (rule ext)
    fix x :: slp_point
    show "?halved x = slp_gradient_wirtinger_partial Du x"
      unfolding slp_gradient_wirtinger_partial_def
      by (simp add: field_simps)
  qed
  show "aim_complex_lp_on_plane p (slp_gradient_wirtinger_partial Du)"
    unfolding presentation[symmetric] by (rule halved(1))
  have rotated_norm_bound:
      "aim_complex_lp_norm p ?rotated \<le>
        aim_complex_lp_norm p ?d1"
    using rotated_data(2) by simp
  have sum_norm_bound:
      "aim_complex_lp_norm p ?sum \<le>
        4 * (aim_complex_lp_norm p ?d0 + aim_complex_lp_norm p ?d1)"
  proof (rule order_trans[OF summed(2)])
    show "4 * (aim_complex_lp_norm p ?d0 +
          aim_complex_lp_norm p ?rotated) \<le>
        4 * (aim_complex_lp_norm p ?d0 + aim_complex_lp_norm p ?d1)"
      by (intro mult_left_mono add_left_mono rotated_norm_bound) simp
  qed
  have halved_norm_bound:
      "aim_complex_lp_norm p ?halved \<le>
        (1 / 2) * aim_complex_lp_norm p ?sum"
    using halved(2) by simp
  have scaled_sum_bound:
      "(1 / 2) * aim_complex_lp_norm p ?sum \<le>
        (1 / 2) *
          (4 * (aim_complex_lp_norm p ?d0 + aim_complex_lp_norm p ?d1))"
    by (rule mult_left_mono[OF sum_norm_bound]) simp
  show "aim_complex_lp_norm p (slp_gradient_wirtinger_partial Du) \<le>
      2 *
        (aim_complex_lp_norm p (\<lambda>x. Du x $ 0) +
          aim_complex_lp_norm p (\<lambda>x. Du x $ 1))"
    unfolding presentation[symmetric]
    using order_trans[OF halved_norm_bound scaled_sum_bound] by simp
qed

theorem slp_w1p_restricted_gradient_wirtinger_partial_data:
  assumes exponent_one_le: "1 \<le> p"
    and pair: "slp_w1p_pair_on p X u Du"
  shows restricted_partial_lp:
      "aim_complex_lp_on_plane p
        (slp_gradient_wirtinger_partial (slp_restrict_gradient X Du))"
    and restricted_partial_norm_bound:
      "aim_complex_lp_norm p
          (slp_gradient_wirtinger_partial (slp_restrict_gradient X Du))
        \<le> 4 * slp_w1p_norm_on p X u Du"
proof -
  have exponent_positive: "0 < p"
    using exponent_one_le by linarith
  note components = slp_w1p_norm_on_component_bounds[OF exponent_positive pair]
  have restricted_zero_lp:
      "aim_complex_lp_on_plane p
        (\<lambda>x. slp_restrict_gradient X Du x $ 0)"
    using conjunct1[OF components(2)] by simp
  have restricted_one_lp:
      "aim_complex_lp_on_plane p
        (\<lambda>x. slp_restrict_gradient X Du x $ 1)"
    using conjunct1[OF components(3)] by simp
  note partial = slp_gradient_wirtinger_partial_lp_coordinate_bound[
    OF exponent_one_le restricted_zero_lp restricted_one_lp]
  show "aim_complex_lp_on_plane p
      (slp_gradient_wirtinger_partial (slp_restrict_gradient X Du))"
    by (rule partial(1))
  have coordinate_sum_bound:
      "aim_complex_lp_norm p
          (\<lambda>x. slp_restrict_gradient X Du x $ 0) +
        aim_complex_lp_norm p
          (\<lambda>x. slp_restrict_gradient X Du x $ 1)
        \<le> slp_w1p_norm_on p X u Du + slp_w1p_norm_on p X u Du"
    using add_mono[OF conjunct2[OF components(2)]
          conjunct2[OF components(3)]] by simp
  have scaled_coordinate_sum_bound:
      "2 *
          (aim_complex_lp_norm p
              (\<lambda>x. slp_restrict_gradient X Du x $ 0) +
            aim_complex_lp_norm p
              (\<lambda>x. slp_restrict_gradient X Du x $ 1))
        \<le> 2 *
          (slp_w1p_norm_on p X u Du + slp_w1p_norm_on p X u Du)"
    by (rule mult_left_mono[OF coordinate_sum_bound]) simp
  show "aim_complex_lp_norm p
        (slp_gradient_wirtinger_partial (slp_restrict_gradient X Du))
      \<le> 4 * slp_w1p_norm_on p X u Du"
    using order_trans[OF partial(2) scaled_coordinate_sum_bound] by simp
qed

section \<open>Power convergence and the raw derivative error\<close>

theorem slp_w1p_restricted_wirtinger_power_integral_tendsto_zero:
  assumes exponent_one_le: "1 \<le> p"
    and error_pairs: "\<And>n. slp_w1p_pair_on p X (e n) (De n)"
    and error_norm_tends:
      "((\<lambda>n. slp_w1p_norm_on p X (e n) (De n)) \<longlongrightarrow> 0)
        sequentially"
  shows sequence_partial_lp:
      "\<And>n. aim_complex_lp_on_plane p
        (slp_gradient_wirtinger_partial (slp_restrict_gradient X (De n)))"
    and sequence_partial_power:
      "((\<lambda>n. integral\<^sup>L lborel
        (\<lambda>x. Real_Vector_Spaces.norm
          (slp_gradient_wirtinger_partial
            (slp_restrict_gradient X (De n)) x) powr p))
        \<longlongrightarrow> 0) sequentially"
proof -
  let ?G = "\<lambda>n. slp_gradient_wirtinger_partial
    (slp_restrict_gradient X (De n))"
  let ?N = "\<lambda>n. aim_complex_lp_norm p (?G n)"
  let ?W = "\<lambda>n. slp_w1p_norm_on p X (e n) (De n)"
  have exponent_positive: "0 < p"
    using exponent_one_le by linarith
  have data:
      "aim_complex_lp_on_plane p (?G n) \<and> ?N n \<le> 4 * ?W n" for n
    using slp_w1p_restricted_gradient_wirtinger_partial_data[
      OF exponent_one_le error_pairs[of n]] by blast
  show "aim_complex_lp_on_plane p (?G n)" for n
    by (rule conjunct1[OF data])
  have N_nonnegative: "0 \<le> ?N n" for n
    unfolding aim_complex_lp_norm_def by simp
  have scaled_error_tends: "((\<lambda>n. 4 * ?W n) \<longlongrightarrow> 0) sequentially"
    using tendsto_mult[OF tendsto_const error_norm_tends] by simp
  have N_tends: "(?N \<longlongrightarrow> 0) sequentially"
    by (rule tendsto_sandwich[where f = "\<lambda>_. 0" and h = "\<lambda>n. 4 * ?W n"])
      (use N_nonnegative data scaled_error_tends in auto)
  have N_power_tends:
      "((\<lambda>n. ?N n powr p) \<longlongrightarrow> 0) sequentially"
  proof -
    have "((\<lambda>n. ?N n powr p) \<longlongrightarrow> 0 powr p) sequentially"
      by (rule tendsto_powr2[OF N_tends tendsto_const])
        (use N_nonnegative exponent_positive in auto)
    then show ?thesis using exponent_positive by simp
  qed
  have integral_nonnegative:
      "0 \<le> integral\<^sup>L lborel
        (\<lambda>x. Real_Vector_Spaces.norm (?G n x) powr p)" for n
    by (rule Bochner_Integration.integral_nonneg) simp
  have norm_power:
      "?N n powr p = integral\<^sup>L lborel
        (\<lambda>x. Real_Vector_Spaces.norm (?G n x) powr p)" for n
    unfolding aim_complex_lp_norm_def
    using exponent_positive integral_nonnegative[of n]
    by (simp add: powr_powr)
  show "((\<lambda>n. integral\<^sup>L lborel
      (\<lambda>x. Real_Vector_Spaces.norm (?G n x) powr p))
      \<longlongrightarrow> 0) sequentially"
    using N_power_tends by (simp only: norm_power)
qed

lemma slp_raw_partial_approximation_error_restricted_wirtinger:
  assumes phi_test: "slp_test_function_on X (phi n)"
  shows "slp_raw_partial_approximation_error phi
      (slp_restrict_field X (slp_gradient_wirtinger_partial Du)) n =
    slp_gradient_wirtinger_partial
      (slp_restrict_gradient X
        (\<lambda>x. slp_classical_gradient (phi n) x - Du x))"
  unfolding slp_raw_partial_approximation_error_def
  by (simp only:
        slp_gradient_wirtinger_partial_restrict_gradient[symmetric]
        slp_gradient_wirtinger_partial_classical_gradient[symmetric]
        slp_restrict_gradient_diff
        slp_restrict_gradient_classical_gradient[OF phi_test]
        slp_gradient_wirtinger_partial_diff)

theorem slp_raw_partial_approximation_error_restricted_wirtinger_data:
  assumes exponent_one_le: "1 \<le> p"
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
  shows raw_partial_lp:
      "\<And>n. aim_complex_lp_on_plane p
        (slp_raw_partial_approximation_error phi
          (slp_restrict_field X (slp_gradient_wirtinger_partial Du)) n)"
    and raw_partial_power:
      "((\<lambda>n. integral\<^sup>L lborel
        (\<lambda>x. Real_Vector_Spaces.norm
          (slp_raw_partial_approximation_error phi
            (slp_restrict_field X
              (slp_gradient_wirtinger_partial Du)) n x) powr p))
        \<longlongrightarrow> 0) sequentially"
proof -
  let ?e = "\<lambda>n x. phi n x - u x"
  let ?De = "\<lambda>n x. slp_classical_gradient (phi n) x - Du x"
  have presentation:
      "slp_raw_partial_approximation_error phi
          (slp_restrict_field X (slp_gradient_wirtinger_partial Du)) n =
        slp_gradient_wirtinger_partial (slp_restrict_gradient X (?De n))"
    for n
    by (rule slp_raw_partial_approximation_error_restricted_wirtinger[
          OF phi_test])
  note data = slp_w1p_restricted_wirtinger_power_integral_tendsto_zero[
    OF exponent_one_le error_pairs error_norm_tends]
  show "aim_complex_lp_on_plane p
      (slp_raw_partial_approximation_error phi
        (slp_restrict_field X (slp_gradient_wirtinger_partial Du)) n)" for n
    unfolding presentation[of n]
    by (rule data(1))
  show "((\<lambda>n. integral\<^sup>L lborel
      (\<lambda>x. Real_Vector_Spaces.norm
        (slp_raw_partial_approximation_error phi
          (slp_restrict_field X
            (slp_gradient_wirtinger_partial Du)) n x) powr p))
      \<longlongrightarrow> 0) sequentially"
    using data(2) by (simp only: presentation)
qed

end
