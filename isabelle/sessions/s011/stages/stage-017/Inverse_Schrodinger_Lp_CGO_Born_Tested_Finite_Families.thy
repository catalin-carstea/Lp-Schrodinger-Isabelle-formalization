theory Inverse_Schrodinger_Lp_CGO_Born_Tested_Finite_Families
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_CGO_Born_Tested_Remainder"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Finite Born families against the tested Neumann remainder\<close>

theorem slp_cgo_born_tested_finite_families_eq_neg_remainder:
  assumes Q_outside: "\<And>z. z \<notin> X \<Longrightarrow> Q z = 0"
    and root_partial:
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
    and root_leading:
      "\<And>c. integrable lborel (\<lambda>z. Q z * slp_center_kernel tau c z)"
    and root_left:
      "\<And>c j. j < N \<Longrightarrow> integrable lborel (\<lambda>z. Q z *
        slp_left_neumann_iterate j tau c cutoff q SLP_Dbar_Inverse z)"
    and root_right:
      "\<And>c k. k < M \<Longrightarrow> integrable lborel (\<lambda>z. Q z *
        slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z)"
    and root_mixed:
      "\<And>c j k. j < N \<Longrightarrow> k < M \<Longrightarrow>
        integrable lborel (\<lambda>z. Q z * slp_center_kernel (- tau) c z *
          slp_left_neumann_iterate j tau c cutoff q SLP_Dbar_Inverse z *
          slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z)"
    and outer_leading:
      "integrable lborel (\<lambda>c. phi c *
        integral\<^sup>L lborel (\<lambda>z. Q z * slp_center_kernel tau c z))"
    and outer_left:
      "\<And>j. j < N \<Longrightarrow> integrable lborel (\<lambda>c. phi c *
        integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_left_neumann_iterate j tau c cutoff q SLP_Dbar_Inverse z))"
    and outer_right:
      "\<And>k. k < M \<Longrightarrow> integrable lborel (\<lambda>c. phi c *
        integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z))"
    and outer_mixed:
      "\<And>j k. j < N \<Longrightarrow> k < M \<Longrightarrow>
        integrable lborel (\<lambda>c. phi c *
          integral\<^sup>L lborel (\<lambda>z.
            Q z * slp_center_kernel (- tau) c z *
            slp_left_neumann_iterate j tau c cutoff q SLP_Dbar_Inverse z *
            slp_right_neumann_iterate k tau c cutoff qt
              SLP_Partial_Inverse z))"
    and full_zero:
      "slp_cgo_born_tested_neumann_functional X tau phi Q cutoff q qt = 0"
  shows
    "slp_leading_functional tau phi Q +
      (\<Sum>j<N. slp_left_born_functional j tau phi Q cutoff q
        SLP_Dbar_Inverse) +
      (\<Sum>k<M. slp_right_born_functional k tau phi Q cutoff qt
        SLP_Partial_Inverse) +
      (\<Sum>j<N. \<Sum>k<M. slp_mixed_born_functional j k tau phi Q cutoff
        q qt SLP_Dbar_Inverse SLP_Partial_Inverse) =
      - slp_cgo_born_tested_neumann_remainder_functional
          X N M tau phi Q cutoff q qt"
proof -
  have partial_eq_remainder:
      "slp_cgo_born_tested_partial_functional
          X N M tau phi Q cutoff q qt =
        - slp_cgo_born_tested_neumann_remainder_functional
            X N M tau phi Q cutoff q qt"
    by (rule slp_cgo_born_tested_partial_eq_neg_remainder[OF
          root_partial root_remainder outer_partial outer_remainder full_zero])
  have partial_expansion:
      "slp_cgo_born_tested_partial_functional
          X N M tau phi Q cutoff q qt =
        slp_leading_functional tau phi Q +
        (\<Sum>j<N. slp_left_born_functional j tau phi Q cutoff q
          SLP_Dbar_Inverse) +
        (\<Sum>k<M. slp_right_born_functional k tau phi Q cutoff qt
          SLP_Partial_Inverse) +
        (\<Sum>j<N. \<Sum>k<M. slp_mixed_born_functional j k tau phi Q cutoff
          q qt SLP_Dbar_Inverse SLP_Partial_Inverse)"
    by (rule slp_cgo_born_tested_partial_functional_expansion[OF
          Q_outside root_leading root_left root_right root_mixed
          outer_leading outer_left outer_right outer_mixed])
  show ?thesis
    unfolding partial_expansion[symmetric]
    by (rule partial_eq_remainder)
qed

end
