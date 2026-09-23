theory AIM_Planar_Cauchy_Beurling_Derivatives_Interface
  imports
    "Paper_Inverse_Schrodinger_Lp_Uniqueness.Inverse_Schrodinger_Lp_Setup"
    "Paper_ISLP_AIM_Planar_Beurling_Lp.AIM_Planar_Beurling_Lp_Interface"
begin

section \<open>Distributional derivatives of the planar Cauchy transform\<close>

definition aim_planar_cauchy_beurling_gradient ::
  "aim_planar_field \<Rightarrow> slp_gradient_field"
where
  "aim_planar_cauchy_beurling_gradient f x =
    (\<chi> i. if i = 0 then
      f x + aim_planar_beurling_transform f x
    else
      \<i> * (aim_planar_beurling_transform f x - f x))"

definition aim_planar_cauchy_beurling_derivatives_claim :: bool
where
  "aim_planar_cauchy_beurling_derivatives_claim \<longleftrightarrow>
    (\<forall>p::real. 1 < p \<longrightarrow>
      (\<forall>f. aim_complex_lp_on_plane p f \<and> bounded {x. f x \<noteq> 0}
        \<longrightarrow>
        slp_weak_gradient_on UNIV
          (aim_planar_cauchy_transform f)
          (aim_planar_cauchy_beurling_gradient f)))"

text \<open>
  The first Cartesian component is `f + S f` and the second is
  `i * (S f - f)`.  Thus the associated Wirtinger derivatives are exactly
  `dbar (C f) = f` and `partial (C f) = S f`.  Bounded support guarantees the
  local integrability of the explicit Cauchy representative used by the
  distributional predicate.  No norm estimate or manuscript conclusion is
  included here.
\<close>

locale aim_planar_cauchy_beurling_derivatives =
  aim_planar_beurling_lp +
  assumes aim_planar_cauchy_beurling_derivatives:
    aim_planar_cauchy_beurling_derivatives_claim

end
