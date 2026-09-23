theory Inverse_Schrodinger_Lp_CGO_Born_Tested_Remainder
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_CGO_Born_Tested_Zero"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Exact full, finite and remainder tested-functional split\<close>

definition slp_cgo_born_tested_neumann_remainder_functional ::
    "slp_point set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow>
      slp_scalar_field \<Rightarrow> complex"
  where
  "slp_cgo_born_tested_neumann_remainder_functional
      X N M tau phi Q cutoff q qt =
    of_real tau * inverse (of_real pi) *
      integral\<^sup>L lborel (\<lambda>c. phi c *
        integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_cgo_born_neumann_remainder
            X N M tau c cutoff q qt z))"

lemma slp_cgo_born_neumann_root_finite_remainder:
  assumes partial_integrable:
      "integrable lborel (\<lambda>z. Q z *
        slp_cgo_born_partial_bracket X N M tau c cutoff q qt z)"
    and remainder_integrable:
      "integrable lborel (\<lambda>z. Q z *
        slp_cgo_born_neumann_remainder X N M tau c cutoff q qt z)"
  shows
    "integrable lborel (\<lambda>z. Q z *
        slp_cgo_born_neumann_bracket X tau c cutoff q qt z) \<and>
      integral\<^sup>L lborel (\<lambda>z. Q z *
        slp_cgo_born_neumann_bracket X tau c cutoff q qt z) =
      integral\<^sup>L lborel (\<lambda>z. Q z *
        slp_cgo_born_partial_bracket X N M tau c cutoff q qt z) +
      integral\<^sup>L lborel (\<lambda>z. Q z *
        slp_cgo_born_neumann_remainder X N M tau c cutoff q qt z)"
proof -
  have bracket_split:
      "slp_cgo_born_neumann_bracket X tau c cutoff q qt z =
        slp_cgo_born_partial_bracket X N M tau c cutoff q qt z +
        slp_cgo_born_neumann_remainder X N M tau c cutoff q qt z"
    for z
    by (rule slp_cgo_born_neumann_bracket_finite_remainder[
          where N=N and M=M])
  have integrand_split:
      "(\<lambda>z. Q z *
          slp_cgo_born_neumann_bracket X tau c cutoff q qt z) =
        (\<lambda>z. Q z *
          slp_cgo_born_partial_bracket X N M tau c cutoff q qt z +
          Q z * slp_cgo_born_neumann_remainder
            X N M tau c cutoff q qt z)"
    by (rule ext) (simp only: bracket_split distrib_left)
  have full_integrable:
      "integrable lborel (\<lambda>z. Q z *
        slp_cgo_born_neumann_bracket X tau c cutoff q qt z)"
    unfolding integrand_split
    by (rule Bochner_Integration.integrable_add[OF
          partial_integrable remainder_integrable])
  have full_integral:
      "integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_cgo_born_neumann_bracket X tau c cutoff q qt z) =
        integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_cgo_born_partial_bracket X N M tau c cutoff q qt z) +
        integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_cgo_born_neumann_remainder X N M tau c cutoff q qt z)"
    unfolding integrand_split
    by (rule Bochner_Integration.integral_add[OF
          partial_integrable remainder_integrable])
  show ?thesis by (rule conjI[OF full_integrable full_integral])
qed

theorem slp_cgo_born_tested_neumann_finite_remainder:
  assumes root_partial:
      "\<And>c. integrable lborel (\<lambda>z. Q z *
        slp_cgo_born_partial_bracket X N M tau c cutoff q qt z)"
    and root_remainder:
      "\<And>c. integrable lborel (\<lambda>z. Q z *
        slp_cgo_born_neumann_remainder X N M tau c cutoff q qt z)"
    and outer_partial:
      "integrable lborel (\<lambda>c. phi c *
        integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_cgo_born_partial_bracket X N M tau c cutoff q qt z))"
    and outer_remainder:
      "integrable lborel (\<lambda>c. phi c *
        integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_cgo_born_neumann_remainder X N M tau c cutoff q qt z))"
  shows
    "slp_cgo_born_tested_neumann_functional X tau phi Q cutoff q qt =
      slp_cgo_born_tested_partial_functional X N M tau phi Q cutoff q qt +
      slp_cgo_born_tested_neumann_remainder_functional
        X N M tau phi Q cutoff q qt"
proof -
  have root_split:
      "integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_cgo_born_neumann_bracket X tau c cutoff q qt z) =
        integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_cgo_born_partial_bracket X N M tau c cutoff q qt z) +
        integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_cgo_born_neumann_remainder X N M tau c cutoff q qt z)"
    for c
    using slp_cgo_born_neumann_root_finite_remainder[
      OF root_partial root_remainder]
    by blast
  have outer_split:
      "integral\<^sup>L lborel (\<lambda>c. phi c *
          integral\<^sup>L lborel (\<lambda>z. Q z *
            slp_cgo_born_neumann_bracket X tau c cutoff q qt z)) =
        integral\<^sup>L lborel (\<lambda>c. phi c *
          integral\<^sup>L lborel (\<lambda>z. Q z *
            slp_cgo_born_partial_bracket X N M tau c cutoff q qt z)) +
        integral\<^sup>L lborel (\<lambda>c. phi c *
          integral\<^sup>L lborel (\<lambda>z. Q z *
            slp_cgo_born_neumann_remainder X N M tau c cutoff q qt z))"
  proof -
    have outer_integrand_split:
        "(\<lambda>c. phi c * integral\<^sup>L lborel (\<lambda>z. Q z *
            slp_cgo_born_neumann_bracket X tau c cutoff q qt z)) =
          (\<lambda>c. phi c * integral\<^sup>L lborel (\<lambda>z. Q z *
              slp_cgo_born_partial_bracket X N M tau c cutoff q qt z) +
            phi c * integral\<^sup>L lborel (\<lambda>z. Q z *
              slp_cgo_born_neumann_remainder X N M tau c cutoff q qt z))"
      by (rule ext) (simp only: root_split distrib_left)
    show ?thesis
      unfolding outer_integrand_split
      by (rule Bochner_Integration.integral_add[OF
            outer_partial outer_remainder])
  qed
  show ?thesis
    unfolding slp_cgo_born_tested_neumann_functional_def
      slp_cgo_born_tested_partial_functional_def
      slp_cgo_born_tested_neumann_remainder_functional_def outer_split
    by (simp only: distrib_left)
qed

theorem slp_cgo_born_tested_partial_eq_neg_remainder:
  assumes root_partial:
      "\<And>c. integrable lborel (\<lambda>z. Q z *
        slp_cgo_born_partial_bracket X N M tau c cutoff q qt z)"
    and root_remainder:
      "\<And>c. integrable lborel (\<lambda>z. Q z *
        slp_cgo_born_neumann_remainder X N M tau c cutoff q qt z)"
    and outer_partial:
      "integrable lborel (\<lambda>c. phi c *
        integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_cgo_born_partial_bracket X N M tau c cutoff q qt z))"
    and outer_remainder:
      "integrable lborel (\<lambda>c. phi c *
        integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_cgo_born_neumann_remainder X N M tau c cutoff q qt z))"
    and full_zero:
      "slp_cgo_born_tested_neumann_functional X tau phi Q cutoff q qt = 0"
  shows
    "slp_cgo_born_tested_partial_functional X N M tau phi Q cutoff q qt =
      - slp_cgo_born_tested_neumann_remainder_functional
          X N M tau phi Q cutoff q qt"
proof -
  have split:
      "slp_cgo_born_tested_neumann_functional X tau phi Q cutoff q qt =
        slp_cgo_born_tested_partial_functional X N M tau phi Q cutoff q qt +
        slp_cgo_born_tested_neumann_remainder_functional
          X N M tau phi Q cutoff q qt"
    by (rule slp_cgo_born_tested_neumann_finite_remainder[OF
          root_partial root_remainder outer_partial outer_remainder])
  have sum_zero:
      "slp_cgo_born_tested_partial_functional X N M tau phi Q cutoff q qt +
        slp_cgo_born_tested_neumann_remainder_functional
          X N M tau phi Q cutoff q qt = 0"
    using split full_zero by simp
  have shifted:
      "slp_cgo_born_tested_partial_functional X N M tau phi Q cutoff q qt +
          slp_cgo_born_tested_neumann_remainder_functional
            X N M tau phi Q cutoff q qt -
          slp_cgo_born_tested_neumann_remainder_functional
            X N M tau phi Q cutoff q qt =
        0 - slp_cgo_born_tested_neumann_remainder_functional
          X N M tau phi Q cutoff q qt"
    by (simp only: sum_zero)
  show ?thesis using shifted by simp
qed

end
