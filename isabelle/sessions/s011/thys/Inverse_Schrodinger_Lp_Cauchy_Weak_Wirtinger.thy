theory Inverse_Schrodinger_Lp_Cauchy_Weak_Wirtinger
  imports Inverse_Schrodinger_Lp_Cauchy_Weak_Derivative_Conjugate
begin

section \<open>Wirtinger combinations of the checked weak gradients\<close>

definition slp_gradient_wirtinger_partial ::
  "slp_gradient_field \<Rightarrow> slp_scalar_field"
where
  "slp_gradient_wirtinger_partial Du x =
    (Du x $ 0 - \<i> * Du x $ 1) / 2"

definition slp_gradient_wirtinger_dbar ::
  "slp_gradient_field \<Rightarrow> slp_scalar_field"
where
  "slp_gradient_wirtinger_dbar Du x =
    (Du x $ 0 + \<i> * Du x $ 1) / 2"

lemma slp_dbar_inverse_gradient_wirtinger_dbar [simp]:
  "slp_gradient_wirtinger_dbar (slp_dbar_inverse_gradient f) = f"
  by (rule ext)
    (simp add: slp_gradient_wirtinger_dbar_def algebra_simps)

lemma slp_partial_inverse_gradient_wirtinger_partial [simp]:
  "slp_gradient_wirtinger_partial (slp_partial_inverse_gradient f) = f"
  by (rule ext)
    (simp add: slp_gradient_wirtinger_partial_def algebra_simps)

context aim_planar_cauchy_beurling_derivatives
begin

theorem slp_both_cauchy_weak_wirtinger_right_inverse:
  assumes p_lower: "1 < (p::real)"
    and f_lp: "aim_complex_lp_on_plane p f"
    and f_support: "bounded {x. f x \<noteq> 0}"
  shows "slp_weak_gradient_on UNIV
      (slp_dbar_inverse f) (slp_dbar_inverse_gradient f) \<and>
    slp_gradient_wirtinger_dbar (slp_dbar_inverse_gradient f) = f \<and>
    slp_weak_gradient_on UNIV
      (slp_partial_inverse f) (slp_partial_inverse_gradient f) \<and>
    slp_gradient_wirtinger_partial (slp_partial_inverse_gradient f) = f"
proof (intro conjI)
  show "slp_weak_gradient_on UNIV
      (slp_dbar_inverse f) (slp_dbar_inverse_gradient f)"
    by (rule slp_dbar_inverse_weak_gradient[OF p_lower f_lp f_support])
  show "slp_gradient_wirtinger_dbar
      (slp_dbar_inverse_gradient f) = f"
    by simp
  show "slp_weak_gradient_on UNIV
      (slp_partial_inverse f) (slp_partial_inverse_gradient f)"
    by (rule slp_partial_inverse_weak_gradient[OF
          p_lower f_lp f_support])
  show "slp_gradient_wirtinger_partial
      (slp_partial_inverse_gradient f) = f"
    by simp
qed

end

end
