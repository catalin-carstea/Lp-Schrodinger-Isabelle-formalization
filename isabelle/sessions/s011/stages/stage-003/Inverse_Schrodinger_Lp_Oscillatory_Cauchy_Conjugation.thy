theory Inverse_Schrodinger_Lp_Oscillatory_Cauchy_Conjugation
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Oscillatory_Cauchy"
begin

section \<open>Exact conjugation of the two Cauchy orientations\<close>

fun slp_opposite_cauchy_orientation ::
    "slp_cauchy_orientation \<Rightarrow> slp_cauchy_orientation"
where
  "slp_opposite_cauchy_orientation SLP_Partial_Inverse =
      SLP_Dbar_Inverse"
| "slp_opposite_cauchy_orientation SLP_Dbar_Inverse =
      SLP_Partial_Inverse"

lemma slp_opposite_cauchy_orientation_involutive [simp]:
  "slp_opposite_cauchy_orientation
      (slp_opposite_cauchy_orientation orientation) = orientation"
  by (cases orientation) simp_all

lemma slp_cauchy_denominator_conjugate [simp]:
  "cnj (slp_cauchy_denominator orientation z y) =
    slp_cauchy_denominator (slp_opposite_cauchy_orientation orientation) z y"
  by (cases orientation)
    (simp_all add: slp_cauchy_denominator_def)

lemma slp_cauchy_kernel_conjugate [simp]:
  "cnj (slp_cauchy_kernel orientation z y) =
    slp_cauchy_kernel (slp_opposite_cauchy_orientation orientation) z y"
  unfolding slp_cauchy_kernel_def by simp

lemma slp_cauchy_integrand_conjugate [simp]:
  "cnj (slp_cauchy_integrand orientation f z y) =
    slp_cauchy_integrand (slp_opposite_cauchy_orientation orientation)
      (\<lambda>x. cnj (f x)) z y"
  unfolding slp_cauchy_integrand_def by simp

lemma slp_cauchy_transform_conjugate [simp]:
  "cnj (slp_cauchy_transform orientation f z) =
    slp_cauchy_transform (slp_opposite_cauchy_orientation orientation)
      (\<lambda>x. cnj (f x)) z"
proof -
  have move_conjugate:
      "integral\<^sup>L lborel
          (\<lambda>y. cnj (slp_cauchy_integrand orientation f z y)) =
        cnj (integral\<^sup>L lborel
          (slp_cauchy_integrand orientation f z))"
    by (rule Bochner_Integration.integral_cnj)
  have integrand_eq:
      "(\<lambda>y. cnj (slp_cauchy_integrand orientation f z y)) =
        slp_cauchy_integrand
          (slp_opposite_cauchy_orientation orientation)
          (\<lambda>x. cnj (f x)) z"
    by (rule ext) (rule slp_cauchy_integrand_conjugate)
  have integral_conjugate:
      "cnj (integral\<^sup>L lborel
          (slp_cauchy_integrand orientation f z)) =
        integral\<^sup>L lborel
          (slp_cauchy_integrand
            (slp_opposite_cauchy_orientation orientation)
            (\<lambda>x. cnj (f x)) z)"
    using move_conjugate unfolding integrand_eq by simp
  show ?thesis
    unfolding slp_cauchy_transform_def
    using integral_conjugate by simp
qed

lemma slp_partial_psi_inverse_conjugate [simp]:
  "cnj (slp_partial_psi_inverse tau center f z) =
    slp_dbar_psi_inverse tau center (\<lambda>x. cnj (f x)) z"
  unfolding slp_partial_psi_inverse_eq slp_dbar_psi_inverse_eq
  by simp

lemma slp_dbar_psi_inverse_conjugate [simp]:
  "cnj (slp_dbar_psi_inverse tau center f z) =
    slp_partial_psi_inverse tau center (\<lambda>x. cnj (f x)) z"
  unfolding slp_partial_psi_inverse_eq slp_dbar_psi_inverse_eq
  by simp

end
