theory Inverse_Schrodinger_Lp_Test_Fourier_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Test_Fourier_Derivatives"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Polynomial Fourier decay of compact smooth tests\<close>

lemma slp_test_fourier_coordinate_weight:
  fixes f :: slp_scalar_field and i :: 2
  assumes f_test: "slp_test_function_on UNIV f"
  shows "slp_test_function_on UNIV
      (\<lambda>x. f x - slp_complex_partial_derivative (slp_complex_partial_derivative f i) i x) \<and>
    (\<forall>xi. slp_fourier_transform
      (\<lambda>x. f x - slp_complex_partial_derivative (slp_complex_partial_derivative f i) i x) xi =
      of_real (1 + (xi $ i)^2) * slp_fourier_transform f xi)"
proof -
  let ?d = "slp_complex_partial_derivative f i"
  let ?dd = "slp_complex_partial_derivative ?d i"
  let ?h = "\<lambda>x. f x - ?dd x"
  have d_test: "slp_test_function_on UNIV ?d"
    by (rule slp_test_function_on_partial_derivative[OF f_test])
  have dd_test: "slp_test_function_on UNIV ?dd"
    by (rule slp_test_function_on_partial_derivative[OF d_test])
  have h_test: "slp_test_function_on UNIV ?h"
    by (rule slp_test_function_on_diff[OF f_test dd_test])
  have f_integrable: "integrable lborel f"
    by (rule slp_test_function_integrable_bounded(1)[OF f_test])
  have dd_integrable: "integrable lborel ?dd"
    by (rule slp_test_function_integrable_bounded(1)[OF dd_test])
  have second_transform:
      "slp_fourier_transform ?dd xi =
        - of_real ((xi $ i)^2) * slp_fourier_transform f xi" for xi
    using slp_test_fourier_partial_derivative[OF d_test, where i=i and xi=xi]
      slp_test_fourier_partial_derivative[OF f_test, where i=i and xi=xi]
    by (simp add: power2_eq_square algebra_simps)
  have h_transform: "slp_fourier_transform ?h xi =
      of_real (1 + (xi $ i)^2) * slp_fourier_transform f xi" for xi
    by (simp only: slp_fourier_transform_diff[OF f_integrable dd_integrable]
        second_transform; simp add: algebra_simps)
  show ?thesis using h_test h_transform by blast
qed

lemma slp_test_fourier_product_weight:
  fixes f :: slp_scalar_field
  assumes f_test: "slp_test_function_on UNIV f"
  shows "\<exists>g. slp_test_function_on UNIV g \<and>
    (\<forall>xi. slp_fourier_transform g xi =
      of_real ((1 + (xi $ 0)^2) * (1 + (xi $ 1)^2)) * slp_fourier_transform f xi)"
proof -
  let ?h = "\<lambda>x. f x -
    slp_complex_partial_derivative (slp_complex_partial_derivative f 0) 0 x"
  let ?g = "\<lambda>x. ?h x -
    slp_complex_partial_derivative (slp_complex_partial_derivative ?h 1) 1 x"
  have first_weight: "slp_test_function_on UNIV ?h \<and>
      (\<forall>xi. slp_fourier_transform ?h xi =
        of_real (1 + (xi $ 0)^2) * slp_fourier_transform f xi)"
    by (rule slp_test_fourier_coordinate_weight[OF f_test])
  have h_test: "slp_test_function_on UNIV ?h" by (rule conjunct1[OF first_weight])
  have second_weight: "slp_test_function_on UNIV ?g \<and>
      (\<forall>xi. slp_fourier_transform ?g xi =
        of_real (1 + (xi $ 1)^2) * slp_fourier_transform ?h xi)"
    by (rule slp_test_fourier_coordinate_weight[OF h_test])
  have g_test: "slp_test_function_on UNIV ?g" by (rule conjunct1[OF second_weight])
  have transform: "slp_fourier_transform ?g xi =
      of_real ((1 + (xi $ 0)^2) * (1 + (xi $ 1)^2)) * slp_fourier_transform f xi" for xi
    using first_weight second_weight by (simp add: mult_ac)
  show ?thesis using g_test transform by blast
qed

lemma slp_test_fourier_product_decay:
  fixes f :: slp_scalar_field
  assumes f_test: "slp_test_function_on UNIV f"
  shows "\<exists>C\<ge>0. \<forall>xi. norm (slp_fourier_transform f xi) \<le>
    C * (inverse (1 + (xi $ 0)^2) * inverse (1 + (xi $ 1)^2))"
proof -
  obtain g where g_test: "slp_test_function_on UNIV g"
    and transform: "\<And>xi. slp_fourier_transform g xi =
      of_real ((1 + (xi $ 0)^2) * (1 + (xi $ 1)^2)) * slp_fourier_transform f xi"
    using slp_test_fourier_product_weight[OF f_test] by blast
  let ?C = "integral\<^sup>L lborel (\<lambda>x. norm (g x))"
  have C_nonnegative: "0 \<le> ?C" by simp
  have g_integrable: "integrable lborel g"
    by (rule slp_test_function_integrable_bounded(1)[OF g_test])
  have bound: "norm (slp_fourier_transform f xi) \<le>
      ?C * (inverse (1 + (xi $ 0)^2) * inverse (1 + (xi $ 1)^2))" for xi
  proof -
    let ?P = "(1 + (xi $ 0)^2) * (1 + (xi $ 1)^2)"
    have coordinate_positive: "0 < 1 + (xi $ i)^2" for i
      by (rule add_pos_nonneg) simp_all
    have P_positive: "0 < ?P"
      by (rule mult_pos_pos[OF coordinate_positive coordinate_positive])
    have transform_bound: "norm (slp_fourier_transform g xi) \<le> ?C"
      by (rule slp_fourier_transform_norm_bound[OF g_integrable])
    have weighted_bound: "?P * norm (slp_fourier_transform f xi) \<le> ?C"
      using transform_bound
      by (simp only: transform norm_mult norm_of_real abs_of_pos[OF P_positive])
    have divided_bound: "norm (slp_fourier_transform f xi) \<le> ?C / ?P"
      using weighted_bound P_positive by (simp add: le_divide_eq mult.commute)
    show ?thesis using divided_bound by (simp add: divide_inverse mult.assoc)
  qed
  show ?thesis using C_nonnegative bound by blast
qed

end
