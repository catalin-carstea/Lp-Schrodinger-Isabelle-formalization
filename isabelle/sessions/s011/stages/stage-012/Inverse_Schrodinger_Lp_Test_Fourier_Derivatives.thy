theory Inverse_Schrodinger_Lp_Test_Fourier_Derivatives
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Center_Average_Uniform_Fourier"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Fourier differentiation for compactly supported smooth inputs\<close>

lemma slp_fourier_phase_smooth:
  "smooth_on UNIV (slp_fourier_phase xi)"
proof -
  let ?t = "\<lambda>x::slp_point. - inner x xi"
  have inner_smooth: "smooth_on UNIV (\<lambda>x::slp_point. inner x xi)"
    by (rule bounded_linear.smooth_on[OF bounded_linear_inner_left])
  have t_smooth: "smooth_on UNIV ?t"
    by (rule smooth_on_uminus[OF inner_smooth open_UNIV])
  have cos_smooth: "smooth_on UNIV (\<lambda>x. cos (?t x))"
    by (rule smooth_on_cos[OF t_smooth open_UNIV])
  have sin_smooth: "smooth_on UNIV (\<lambda>x. sin (?t x))"
    by (rule smooth_on_sin[OF t_smooth open_UNIV])
  have complex_cos: "smooth_on UNIV (\<lambda>x. of_real (cos (?t x)) :: complex)"
    unfolding of_real_def
    by (rule smooth_on_scaleR[OF cos_smooth smooth_on_const open_UNIV])
  have complex_sin: "smooth_on UNIV (\<lambda>x. of_real (sin (?t x)) :: complex)"
    unfolding of_real_def
    by (rule smooth_on_scaleR[OF sin_smooth smooth_on_const open_UNIV])
  have imaginary_sin: "smooth_on UNIV (\<lambda>x. \<i> * of_real (sin (?t x)))"
    by (rule smooth_on_mult[OF smooth_on_const complex_sin open_UNIV])
  have euler: "smooth_on UNIV (\<lambda>x. of_real (cos (?t x)) + \<i> * of_real (sin (?t x)))"
    by (rule smooth_on_add[OF complex_cos imaginary_sin open_UNIV])
  have identity: "slp_fourier_phase xi =
      (\<lambda>x. of_real (cos (?t x)) + \<i> * of_real (sin (?t x)))"
    by (rule ext) (simp only: slp_fourier_phase_def exp_Euler cos_of_real sin_of_real)
  show ?thesis unfolding identity by (rule euler)
qed


lemma slp_fourier_phase_partial:
  "slp_complex_partial_derivative (slp_fourier_phase xi) i x =
    - (\<i> * of_real (xi $ i)) * slp_fourier_phase xi x"
proof -
  have linear:
      "((\<lambda>y::slp_point. \<i> * of_real (- inner y xi)) has_derivative
        (\<lambda>h. \<i> * of_real (- inner h xi))) (at x)"
    by (auto intro!: derivative_eq_intros)
  have exp_at:
      "(exp has_derivative (\<lambda>h. exp (\<i> * of_real (- inner x xi)) * h))
        (at (\<i> * of_real (- inner x xi)))"
    by (rule DERIV_exp[unfolded has_field_derivative_def])
  have derivative:
      "(slp_fourier_phase xi has_derivative
        (\<lambda>h. slp_fourier_phase xi x * (\<i> * of_real (- inner h xi)))) (at x)"
    unfolding slp_fourier_phase_def
    by (rule has_derivative_compose[OF linear exp_at])
  have frechet:
      "frechet_derivative (slp_fourier_phase xi) (at x) =
        (\<lambda>h. slp_fourier_phase xi x * (\<i> * of_real (- inner h xi)))"
    by (rule sym, rule frechet_derivative_at[OF derivative])
  show ?thesis unfolding slp_complex_partial_derivative_def frechet
    by (simp add: inner_axis inner_commute mult.commute mult.left_commute)
qed

lemma slp_test_fourier_partial_derivative:
  fixes f :: slp_scalar_field and i :: 2
  assumes f_test: "slp_test_function_on UNIV f"
  shows "slp_fourier_transform (slp_complex_partial_derivative f i) xi =
    (\<i> * of_real (xi $ i)) * slp_fourier_transform f xi"
proof -
  let ?a = "slp_fourier_phase xi"
  let ?d = "slp_complex_partial_derivative f i"
  let ?b = "\<i> * of_real (xi $ i)"
  have f_smooth: "smooth_on UNIV f"
    using f_test unfolding slp_test_function_on_def by blast
  have derivative_test: "slp_test_function_on UNIV ?d"
    by (rule slp_test_function_on_partial_derivative[OF f_test])
  have f_integrable: "integrable lborel f"
    by (rule slp_test_function_integrable_bounded(1)[OF f_test])
  have derivative_integrable: "integrable lborel ?d"
    by (rule slp_test_function_integrable_bounded(1)[OF derivative_test])
  have product_test: "slp_test_function_on UNIV (\<lambda>x. ?a x * f x)"
    by (rule slp_test_function_on_mult_left[OF slp_fourier_phase_smooth f_test])
  have integral_zero:
      "integral\<^sup>L lborel (slp_complex_partial_derivative (\<lambda>x. ?a x * f x) i) = 0"
    by (rule slp_test_function_partial_integral_zero[OF product_test])
  have derivative_identity:
      "slp_complex_partial_derivative (\<lambda>x. ?a x * f x) i =
        (\<lambda>x. ?a x * ?d x - ?b * (?a x * f x))"
    by (rule ext) (simp only: slp_complex_partial_derivative_mult[
        OF slp_fourier_phase_smooth f_smooth] slp_fourier_phase_partial;
        simp add: algebra_simps)
  have first_integrable: "integrable lborel (\<lambda>x. ?a x * ?d x)"
    by (rule slp_fourier_integrand_integrable[OF derivative_integrable])
  have second_integrable: "integrable lborel (\<lambda>x. ?b * (?a x * f x))"
    by (rule Bochner_Integration.integrable_mult_right)
      (rule slp_fourier_integrand_integrable[OF f_integrable])
  have relation: "slp_fourier_transform ?d xi - ?b * slp_fourier_transform f xi = 0"
    using integral_zero
    by (simp only: derivative_identity Bochner_Integration.integral_diff[
        OF first_integrable second_integrable] integral_mult_right_zero
        slp_fourier_transform_def)
  show ?thesis using relation by simp
qed

lemma slp_test_fourier_iterated_partial:
  fixes f :: slp_scalar_field and i :: 2
  assumes f_test: "slp_test_function_on UNIV f"
  shows "slp_test_function_on UNIV (((\<lambda>g. slp_complex_partial_derivative g i) ^^ n) f) \<and>
    (\<forall>xi. slp_fourier_transform (((\<lambda>g. slp_complex_partial_derivative g i) ^^ n) f) xi =
      (\<i> * of_real (xi $ i)) ^ n * slp_fourier_transform f xi)"
proof (induction n)
  case 0
  then show ?case using f_test by simp
next
  case (Suc n)
  let ?h = "((\<lambda>g. slp_complex_partial_derivative g i) ^^ n) f"
  have h_test: "slp_test_function_on UNIV ?h" using Suc.IH by blast
  have derivative_test: "slp_test_function_on UNIV (slp_complex_partial_derivative ?h i)"
    by (rule slp_test_function_on_partial_derivative[OF h_test])
  have transform:
      "slp_fourier_transform (slp_complex_partial_derivative ?h i) xi =
        (\<i> * of_real (xi $ i)) ^ Suc n * slp_fourier_transform f xi" for xi
    using slp_test_fourier_partial_derivative[OF h_test, where i=i and xi=xi] Suc.IH
    by (simp add: power_Suc mult.assoc)
  show ?case using derivative_test transform by simp
qed

end
