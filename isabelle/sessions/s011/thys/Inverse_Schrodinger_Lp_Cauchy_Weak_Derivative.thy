theory Inverse_Schrodinger_Lp_Cauchy_Weak_Derivative
  imports
    Inverse_Schrodinger_Lp_Beurling_Lp
    "Paper_ISLP_AIM_Planar_Cauchy_Beurling_Derivatives.AIM_Planar_Cauchy_Beurling_Derivatives_Interface"
begin

section \<open>Source-orientation Cauchy weak derivative\<close>

definition slp_dbar_inverse_gradient ::
  "aim_planar_field \<Rightarrow> slp_gradient_field"
where
  "slp_dbar_inverse_gradient f x =
    (\<chi> i. if i = 0 then
      f x + slp_beurling_transform f x
    else
      \<i> * (slp_beurling_transform f x - f x))"

lemma slp_dbar_inverse_gradient_component_0 [simp]:
  "slp_dbar_inverse_gradient f x $ 0 =
    f x + slp_beurling_transform f x"
  by (simp add: slp_dbar_inverse_gradient_def)

lemma slp_dbar_inverse_gradient_component_1 [simp]:
  "slp_dbar_inverse_gradient f x $ 1 =
    \<i> * (slp_beurling_transform f x - f x)"
  by (simp add: slp_dbar_inverse_gradient_def)

lemma slp_dbar_inverse_gradient_eq_aim:
  "slp_dbar_inverse_gradient f =
    aim_planar_cauchy_beurling_gradient f"
  unfolding slp_dbar_inverse_gradient_def
    aim_planar_cauchy_beurling_gradient_def
    slp_beurling_transform_def
  by (rule refl)

context aim_planar_cauchy_beurling_derivatives
begin

theorem slp_dbar_inverse_weak_gradient:
  assumes p_lower: "1 < (p::real)"
    and f_lp: "aim_complex_lp_on_plane p f"
    and f_support: "bounded {x. f x \<noteq> 0}"
  shows "slp_weak_gradient_on UNIV
    (slp_dbar_inverse f)
    (slp_dbar_inverse_gradient f)"
proof -
  have source_gradient:
    "slp_weak_gradient_on UNIV
      (aim_planar_cauchy_transform f)
      (aim_planar_cauchy_beurling_gradient f)"
    using aim_planar_cauchy_beurling_derivatives
      p_lower f_lp f_support
    unfolding aim_planar_cauchy_beurling_derivatives_claim_def
    by blast
  show ?thesis
    using source_gradient
    by (simp only: slp_dbar_inverse_eq_aim
        slp_dbar_inverse_gradient_eq_aim)
qed

end

end
