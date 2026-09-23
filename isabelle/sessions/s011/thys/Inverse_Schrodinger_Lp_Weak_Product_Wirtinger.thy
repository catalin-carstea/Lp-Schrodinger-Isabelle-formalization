theory Inverse_Schrodinger_Lp_Weak_Product_Wirtinger
  imports Inverse_Schrodinger_Lp_Weak_Product_Rule
    Inverse_Schrodinger_Lp_Cauchy_Weak_Wirtinger
begin

section \<open>Wirtinger projection of the Cartesian weak product rule\<close>

definition slp_classical_wirtinger_partial ::
  "slp_scalar_field \<Rightarrow> slp_scalar_field"
where
  "slp_classical_wirtinger_partial a x =
    (slp_complex_partial_derivative a 0 x -
      \<i> * slp_complex_partial_derivative a 1 x) / 2"

lemma slp_wirtinger_product_algebra:
  "((a * d0 + u * e0) - \<i> * (a * d1 + u * e1)) / 2 =
    a * ((d0 - \<i> * d1) / 2) +
      u * ((e0 - \<i> * e1) / 2)"
proof -
  have numerator:
    "(a * d0 + u * e0) - \<i> * (a * d1 + u * e1) =
      a * (d0 - \<i> * d1) + u * (e0 - \<i> * e1)"
    by (simp add: algebra_simps)
  have first:
    "((a * d0 + u * e0) - \<i> * (a * d1 + u * e1)) / 2 =
      (a * (d0 - \<i> * d1) + u * (e0 - \<i> * e1)) / 2"
    by (simp only: numerator)
  have second:
    "(a * (d0 - \<i> * d1) + u * (e0 - \<i> * e1)) / 2 =
      (a * (d0 - \<i> * d1)) / 2 +
        (u * (e0 - \<i> * e1)) / 2"
    by (rule add_divide_distrib)
  have third:
    "(a * (d0 - \<i> * d1)) / 2 +
        (u * (e0 - \<i> * e1)) / 2 =
      a * ((d0 - \<i> * d1) / 2) +
        u * ((e0 - \<i> * e1) / 2)"
    by simp
  show ?thesis
    by (rule trans[OF first trans[OF second third]])
qed

lemma slp_product_gradient_wirtinger_partial:
  "slp_gradient_wirtinger_partial
      (\<lambda>x. \<chi> i. a x * Du x $ i +
        u x * slp_complex_partial_derivative a i x) =
    (\<lambda>x. a x * slp_gradient_wirtinger_partial Du x +
      u x * slp_classical_wirtinger_partial a x)"
  unfolding slp_gradient_wirtinger_partial_def
    slp_classical_wirtinger_partial_def
  by (rule ext) (simp only: vec_lambda_beta
      slp_wirtinger_product_algebra)

theorem slp_weak_gradient_on_mult_smooth_wirtinger:
  assumes p_at_least_one: "1 \<le> p"
    and U_measurable: "U \<in> sets lborel"
    and U_bounded: "bounded U"
    and u_lp: "aim_complex_lp_on_plane p u"
    and Du_lp: "slp_gradient_components_lp p Du"
    and a_smooth: "smooth_on UNIV a"
    and weak_u: "slp_weak_gradient_on U u Du"
  shows "slp_weak_gradient_on U
      (\<lambda>x. a x * u x)
      (\<lambda>x. \<chi> i. a x * Du x $ i +
        u x * slp_complex_partial_derivative a i x) \<and>
    slp_gradient_wirtinger_partial
      (\<lambda>x. \<chi> i. a x * Du x $ i +
        u x * slp_complex_partial_derivative a i x) =
      (\<lambda>x. a x * slp_gradient_wirtinger_partial Du x +
        u x * slp_classical_wirtinger_partial a x)"
  using slp_weak_gradient_on_mult_smooth[OF p_at_least_one U_measurable
      U_bounded u_lp Du_lp a_smooth weak_u]
    slp_product_gradient_wirtinger_partial
  by blast

end
