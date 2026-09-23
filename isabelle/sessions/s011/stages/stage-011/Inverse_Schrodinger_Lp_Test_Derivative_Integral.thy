theory Inverse_Schrodinger_Lp_Test_Derivative_Integral
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_All_Orientation_Gain"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cartesian_Lebesgue_Reindex"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_One_Sided_Smooth_Error_Limits"
begin

section \<open>Compactly supported line derivatives have zero integral\<close>

lemma slp_compact_line_derivative_integral_zero:
  fixes F G :: "real \<Rightarrow> complex"
  assumes R_positive: "0 < R"
    and derivative: "\<And>x. (F has_vector_derivative G x) (at x)"
    and continuous: "continuous_on UNIV G"
    and F_zero: "\<And>x. R \<le> abs x \<Longrightarrow> F x = 0"
    and G_zero: "\<And>x. R \<le> abs x \<Longrightarrow> G x = 0"
  shows "integral\<^sup>L lborel G = 0"
proof -
  have interval_order: "- R \<le> R" using R_positive by linarith
  have within_derivative:
      "(F has_vector_derivative G x) (at x within {- R .. R})"
    if "- R \<le> x" "x \<le> R" for x
    by (rule has_vector_derivative_at_within[OF derivative])
  have interval_continuous: "continuous_on {- R .. R} G"
    by (rule continuous_on_subset[OF continuous]) simp
  have restricted: "(\<lambda>x. indicator {- R .. R} x *\<^sub>R G x) = G"
  proof (rule ext)
    fix x :: real
    show "indicator {- R .. R} x *\<^sub>R G x = G x"
    proof (cases "x \<in> {- R .. R}")
      case True
      then show ?thesis by simp
    next
      case False
      have outside: "R \<le> abs x" using False by auto
      have value_zero: "G x = 0" by (rule G_zero[OF outside])
      show ?thesis by (simp only: value_zero scaleR_zero_right)
    qed
  qed
  have F_left: "F (- R) = 0" and F_right: "F R = 0"
    using F_zero[of "- R"] F_zero[of R] R_positive by simp_all
  note ftc = integral_FTC_Icc[OF interval_order within_derivative interval_continuous]
  show ?thesis using ftc
    by (simp only: restricted F_left F_right diff_self)
qed

section \<open>Cartesian derivatives of planar test functions integrate to zero\<close>

theorem slp_test_function_partial_integral_zero:
  fixes f :: slp_scalar_field and i :: 2
  assumes f_test: "slp_test_function_on UNIV f"
  shows "integral\<^sup>L lborel (slp_complex_partial_derivative f i) = 0"
proof -
  let ?K = "closure {x. f x \<noteq> 0}"
  let ?d = "slp_complex_partial_derivative f i"
  have f_smooth: "smooth_on UNIV f" and K_compact: "compact ?K"
    using f_test unfolding slp_test_function_on_def by blast+
  have d_test: "slp_test_function_on UNIV ?d"
    by (rule slp_test_function_on_partial_derivative[OF f_test])
  have d_integrable: "integrable lborel ?d"
    by (rule slp_test_function_integrable_bounded(1)[OF d_test])
  have d_smooth: "smooth_on UNIV ?d"
    by (rule slp_complex_partial_derivative_smooth[OF f_smooth])
  have d_continuous: "continuous_on UNIV ?d"
    by (rule smooth_on_imp_continuous_on[OF d_smooth])
  have d_borel: "?d \<in> borel_measurable (borel :: slp_point measure)"
    by (rule borel_measurable_continuous_onI[OF d_continuous])
  have d_support: "closure {x. ?d x \<noteq> 0} \<subseteq> ?K"
    by (rule slp_complex_partial_derivative_support_subset[OF f_smooth])
  obtain R::real where R_positive: "0 < R"
    and K_bound: "\<And>x. x \<in> ?K \<Longrightarrow> norm x < R"
    using compact_imp_bounded[OF K_compact]
    unfolding bounded_pos_less by blast
  have outside_zero: "f x = 0 \<and> ?d x = 0"
    if outside: "R \<le> norm x" for x :: slp_point
  proof -
    have not_support: "x \<notin> ?K" using outside K_bound[of x] by auto
    have f_zero: "f x = 0" using not_support by auto
    have d_zero: "?d x = 0"
      using not_support d_support closure_subset[of "{x. ?d x \<noteq> 0}"] by auto
    show ?thesis by (rule conjI[OF f_zero d_zero])
  qed
  have f_differentiable: "f differentiable at x" for x :: slp_point
    using smooth_on_imp_differentiable_on[OF f_smooth]
    by (simp add: differentiable_on_def)

  let ?V = "\<lambda>omega::2 \<Rightarrow> real. (\<chi> j. omega j) :: slp_point"
  let ?P = "PiM (UNIV :: 2 set) (\<lambda>_. (lborel :: real measure))"
  have V_measurable: "?V \<in> measurable ?P borel"
    by (rule slp_cartesian_vector_constructor_measurable)
  have d_distr_integrable: "integrable (distr ?P borel ?V) ?d"
    using d_integrable
    by (simp only: slp_lborel_cartesian_vector_product[where 'n=2])
  have pullback_integrable: "integrable ?P (\<lambda>omega. ?d (?V omega))"
    by (rule integrable_distr[OF V_measurable d_distr_integrable])
  have integral_transport:
      "integral\<^sup>L lborel ?d =
        integral\<^sup>L ?P (\<lambda>omega. ?d (?V omega))"
    using integral_distr[OF V_measurable d_borel]
    by (simp only: slp_lborel_cartesian_vector_product[where 'n=2])

  have line_zero:
      "integral\<^sup>L lborel (\<lambda>t. ?d (?V (omega(i := t)))) = 0"
    for omega :: "2 \<Rightarrow> real"
  proof -
    let ?L = "\<lambda>t::real. ?V (omega(i := t))"
    have line_affine:
        "?L = (\<lambda>t. ?V (omega(i := 0)) + t *\<^sub>R axis i 1)"
      by (rule ext) (simp add: vec_eq_iff axis_def)
    have line_derivative:
        "(?L has_vector_derivative axis i 1) (at t)" for t :: real
      unfolding line_affine
      by (intro derivative_eq_intros) auto
    have line_continuous: "continuous_on UNIV ?L"
      unfolding line_affine by (intro continuous_intros)
    have d_image_continuous: "continuous_on (?L ` UNIV) ?d"
      by (rule continuous_on_subset[OF d_continuous]) simp
    have G_continuous: "continuous_on UNIV (\<lambda>t. ?d (?L t))"
      using continuous_on_compose[OF line_continuous d_image_continuous]
      by (simp only: comp_def)
    have composed_derivative:
        "((\<lambda>t. f (?L t)) has_vector_derivative ?d (?L t)) (at t)"
      for t :: real
    proof -
      have f_derivative:
          "(f has_derivative frechet_derivative f (at (?L t)))
            (at (?L t) within ?L ` UNIV)"
        by (rule has_derivative_at_withinI)
          (use f_differentiable[of "?L t"] in
            \<open>simp only: frechet_derivative_works\<close>)
      note chain = vector_derivative_diff_chain_within[
        OF line_derivative[of t] f_derivative]
      show ?thesis using chain
        by (simp only: comp_def slp_complex_partial_derivative_def)
    qed
    have line_norm_bound: "abs t \<le> norm (?L t)" for t :: real
    proof -
      have "abs (?L t $ i) \<le> norm (?L t)"
        by (rule component_le_norm_cart)
      then show ?thesis by simp
    qed
    have F_zero: "f (?L t) = 0" if outside: "R \<le> abs t" for t :: real
      by (rule conjunct1[OF outside_zero[OF
            order_trans[OF outside line_norm_bound]]])
    have G_zero: "?d (?L t) = 0" if outside: "R \<le> abs t" for t :: real
      by (rule conjunct2[OF outside_zero[OF
            order_trans[OF outside line_norm_bound]]])
    show ?thesis
      by (rule slp_compact_line_derivative_integral_zero[
            OF R_positive composed_derivative G_continuous F_zero G_zero])
  qed

  interpret scalar: product_sigma_finite "\<lambda>_::2. (lborel :: real measure)"
    by standard
  let ?I = "(UNIV :: 2 set) - {i}"
  have I_finite: "finite ?I" and i_outside: "i \<notin> ?I" by simp_all
  have index_universe: "insert i ?I = (UNIV :: 2 set)" by auto
  have insert_integrable:
      "integrable (PiM (insert i ?I) (\<lambda>_. (lborel :: real measure)))
        (\<lambda>omega. ?d (?V omega))"
    using pullback_integrable by (simp only: index_universe)
  have integral_slices:
      "integral\<^sup>L ?P (\<lambda>omega. ?d (?V omega)) =
        integral\<^sup>L (PiM ?I (\<lambda>_. (lborel :: real measure)))
          (\<lambda>omega. integral\<^sup>L lborel
            (\<lambda>t. ?d (?V (omega(i := t)))))"
    using scalar.product_integral_insert[OF I_finite i_outside insert_integrable]
    by (simp only: index_universe)
  have product_zero: "integral\<^sup>L ?P (\<lambda>omega. ?d (?V omega)) = 0"
    using integral_slices by (simp only: line_zero integral_zero)
  show ?thesis using integral_transport product_zero by simp
qed

end
