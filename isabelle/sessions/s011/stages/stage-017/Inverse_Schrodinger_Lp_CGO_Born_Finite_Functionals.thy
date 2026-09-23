theory Inverse_Schrodinger_Lp_CGO_Born_Finite_Functionals
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_CGO_Born_Finite_Expansion"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Leading_Functional"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_One_Sided_Born_Cancellation"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_Natural_Right_One_Sided_Born_Cancellation"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_Mixed_Born_Cancellation"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Exact finite center-tested Born functional expansion\<close>

definition slp_cgo_born_tested_partial_functional ::
    "slp_point set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow>
      slp_scalar_field \<Rightarrow> complex"
  where
  "slp_cgo_born_tested_partial_functional X N M tau phi Q cutoff q qt =
    of_real tau * inverse (of_real pi) *
      integral\<^sup>L lborel (\<lambda>c. phi c *
        integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_cgo_born_partial_bracket X N M tau c cutoff q qt z))"

lemma slp_cgo_born_partial_weighted_expansion:
  assumes Q_outside: "\<And>z. z \<notin> X \<Longrightarrow> Q z = 0"
  shows
    "Q z * slp_cgo_born_partial_bracket X N M tau c cutoff q qt z =
      Q z * slp_center_kernel tau c z +
      (\<Sum>j<N. Q z *
        slp_left_neumann_iterate j tau c cutoff q SLP_Dbar_Inverse z) +
      (\<Sum>k<M. Q z *
        slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z) +
      (\<Sum>j<N. \<Sum>k<M. Q z * slp_center_kernel (- tau) c z *
        slp_left_neumann_iterate j tau c cutoff q SLP_Dbar_Inverse z *
        slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z)"
proof (cases "z \<in> X")
  case True
  note expansion = slp_cgo_born_partial_bracket_expansion_on_carrier[
    OF True, where N=N and M=M and tau=tau and c=c and cutoff=cutoff
      and coefficient=q and coefficient_tilde=qt]
  show ?thesis
    unfolding expansion
    by (simp add: sum_distrib_left algebra_simps)
next
  case False
  then have "Q z = 0" by (rule Q_outside)
  then show ?thesis by simp
qed

lemma slp_cgo_born_partial_root_integral_expansion:
  assumes Q_outside: "\<And>z. z \<notin> X \<Longrightarrow> Q z = 0"
    and leading_integrable:
      "integrable lborel (\<lambda>z. Q z * slp_center_kernel tau c z)"
    and left_integrable:
      "\<And>j. j < N \<Longrightarrow> integrable lborel (\<lambda>z. Q z *
        slp_left_neumann_iterate j tau c cutoff q SLP_Dbar_Inverse z)"
    and right_integrable:
      "\<And>k. k < M \<Longrightarrow> integrable lborel (\<lambda>z. Q z *
        slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z)"
    and mixed_integrable:
      "\<And>j k. j < N \<Longrightarrow> k < M \<Longrightarrow>
        integrable lborel (\<lambda>z. Q z * slp_center_kernel (- tau) c z *
          slp_left_neumann_iterate j tau c cutoff q SLP_Dbar_Inverse z *
          slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z)"
  shows
    "integral\<^sup>L lborel (\<lambda>z. Q z *
        slp_cgo_born_partial_bracket X N M tau c cutoff q qt z) =
      integral\<^sup>L lborel (\<lambda>z. Q z * slp_center_kernel tau c z) +
      (\<Sum>j<N. integral\<^sup>L lborel (\<lambda>z. Q z *
        slp_left_neumann_iterate j tau c cutoff q SLP_Dbar_Inverse z)) +
      (\<Sum>k<M. integral\<^sup>L lborel (\<lambda>z. Q z *
        slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z)) +
      (\<Sum>j<N. \<Sum>k<M. integral\<^sup>L lborel (\<lambda>z.
        Q z * slp_center_kernel (- tau) c z *
        slp_left_neumann_iterate j tau c cutoff q SLP_Dbar_Inverse z *
        slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z))"
proof -
  let ?L = "\<lambda>j z. Q z *
    slp_left_neumann_iterate j tau c cutoff q SLP_Dbar_Inverse z"
  let ?R = "\<lambda>k z. Q z *
    slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z"
  let ?B = "\<lambda>j k z. Q z * slp_center_kernel (- tau) c z *
    slp_left_neumann_iterate j tau c cutoff q SLP_Dbar_Inverse z *
    slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z"
  have left_sum_integrable:
      "integrable lborel (\<lambda>z. \<Sum>j<N. ?L j z)"
    by (rule Bochner_Integration.integrable_sum) (simp add: left_integrable)
  have right_sum_integrable:
      "integrable lborel (\<lambda>z. \<Sum>k<M. ?R k z)"
    by (rule Bochner_Integration.integrable_sum) (simp add: right_integrable)
  have mixed_inner_integrable:
      "integrable lborel (\<lambda>z. \<Sum>k<M. ?B j k z)"
    if j_in: "j < N" for j
    proof (rule Bochner_Integration.integrable_sum)
      fix k
      assume k_in: "k \<in> {..<M}"
      show "integrable lborel (?B j k)"
        by (rule mixed_integrable) (use j_in k_in in simp_all)
    qed
  have mixed_sum_integrable:
      "integrable lborel (\<lambda>z. \<Sum>j<N. \<Sum>k<M. ?B j k z)"
    by (rule Bochner_Integration.integrable_sum)
      (simp add: mixed_inner_integrable)
  have left_integral:
      "integral\<^sup>L lborel (\<lambda>z. \<Sum>j<N. ?L j z) =
        (\<Sum>j<N. integral\<^sup>L lborel (?L j))"
    by (rule Bochner_Integration.integral_sum) (simp add: left_integrable)
  have right_integral:
      "integral\<^sup>L lborel (\<lambda>z. \<Sum>k<M. ?R k z) =
        (\<Sum>k<M. integral\<^sup>L lborel (?R k))"
    by (rule Bochner_Integration.integral_sum) (simp add: right_integrable)
  have mixed_integral:
      "integral\<^sup>L lborel (\<lambda>z. \<Sum>j<N. \<Sum>k<M. ?B j k z) =
        (\<Sum>j<N. \<Sum>k<M. integral\<^sup>L lborel (?B j k))"
  proof -
    have inner: "integral\<^sup>L lborel (\<lambda>z. \<Sum>k<M. ?B j k z) =
        (\<Sum>k<M. integral\<^sup>L lborel (?B j k))" if "j < N" for j
      by (rule Bochner_Integration.integral_sum)
        (simp add: mixed_integrable that)
    show ?thesis
      by (subst Bochner_Integration.integral_sum)
        (simp_all add: mixed_inner_integrable inner)
  qed
  have pointwise:
      "(\<lambda>z. Q z *
          slp_cgo_born_partial_bracket X N M tau c cutoff q qt z) =
        (\<lambda>z. Q z * slp_center_kernel tau c z +
          (\<Sum>j<N. ?L j z) + (\<Sum>k<M. ?R k z) +
          (\<Sum>j<N. \<Sum>k<M. ?B j k z))"
    by (rule ext)
      (rule slp_cgo_born_partial_weighted_expansion[OF Q_outside])
  show ?thesis
    unfolding pointwise
    by (simp only:
        Bochner_Integration.integral_add[OF leading_integrable
          left_sum_integrable]
        Bochner_Integration.integrable_add[OF leading_integrable
          left_sum_integrable]
        Bochner_Integration.integral_add[OF
          Bochner_Integration.integrable_add[OF leading_integrable
            left_sum_integrable] right_sum_integrable]
        Bochner_Integration.integrable_add[OF
          Bochner_Integration.integrable_add[OF leading_integrable
            left_sum_integrable] right_sum_integrable]
        Bochner_Integration.integral_add[OF
          Bochner_Integration.integrable_add[OF
            Bochner_Integration.integrable_add[OF leading_integrable
              left_sum_integrable] right_sum_integrable]
          mixed_sum_integrable]
        left_integral right_integral mixed_integral)
qed

theorem slp_cgo_born_tested_partial_functional_expansion:
  assumes Q_outside: "\<And>z. z \<notin> X \<Longrightarrow> Q z = 0"
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
            slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z))"
  shows
    "slp_cgo_born_tested_partial_functional X N M tau phi Q cutoff q qt =
      slp_leading_functional tau phi Q +
      (\<Sum>j<N. slp_left_born_functional j tau phi Q cutoff q
        SLP_Dbar_Inverse) +
      (\<Sum>k<M. slp_right_born_functional k tau phi Q cutoff qt
        SLP_Partial_Inverse) +
      (\<Sum>j<N. \<Sum>k<M. slp_mixed_born_functional j k tau phi Q cutoff
        q qt SLP_Dbar_Inverse SLP_Partial_Inverse)"
proof -
  let ?A = "of_real tau * inverse (of_real pi)"
  let ?L = "\<lambda>j c. phi c * integral\<^sup>L lborel (\<lambda>z. Q z *
    slp_left_neumann_iterate j tau c cutoff q SLP_Dbar_Inverse z)"
  let ?R = "\<lambda>k c. phi c * integral\<^sup>L lborel (\<lambda>z. Q z *
    slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z)"
  let ?B = "\<lambda>j k c. phi c * integral\<^sup>L lborel (\<lambda>z.
    Q z * slp_center_kernel (- tau) c z *
    slp_left_neumann_iterate j tau c cutoff q SLP_Dbar_Inverse z *
    slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z)"
  have left_outer_integrable:
      "integrable lborel (\<lambda>c. \<Sum>j<N. ?L j c)"
    by (rule Bochner_Integration.integrable_sum) (simp add: outer_left)
  have right_outer_integrable:
      "integrable lborel (\<lambda>c. \<Sum>k<M. ?R k c)"
    by (rule Bochner_Integration.integrable_sum) (simp add: outer_right)
  have mixed_inner_outer_integrable:
      "integrable lborel (\<lambda>c. \<Sum>k<M. ?B j k c)"
    if j_in: "j < N" for j
    proof (rule Bochner_Integration.integrable_sum)
      fix k
      assume k_in: "k \<in> {..<M}"
      show "integrable lborel (?B j k)"
        by (rule outer_mixed) (use j_in k_in in simp_all)
    qed
  have mixed_outer_integrable:
      "integrable lborel (\<lambda>c. \<Sum>j<N. \<Sum>k<M. ?B j k c)"
    by (rule Bochner_Integration.integrable_sum)
      (simp add: mixed_inner_outer_integrable)
  have left_outer_integral:
      "integral\<^sup>L lborel (\<lambda>c. \<Sum>j<N. ?L j c) =
        (\<Sum>j<N. integral\<^sup>L lborel (?L j))"
    by (rule Bochner_Integration.integral_sum) (simp add: outer_left)
  have right_outer_integral:
      "integral\<^sup>L lborel (\<lambda>c. \<Sum>k<M. ?R k c) =
        (\<Sum>k<M. integral\<^sup>L lborel (?R k))"
    by (rule Bochner_Integration.integral_sum) (simp add: outer_right)
  have mixed_outer_integral:
      "integral\<^sup>L lborel (\<lambda>c. \<Sum>j<N. \<Sum>k<M. ?B j k c) =
        (\<Sum>j<N. \<Sum>k<M. integral\<^sup>L lborel (?B j k))"
  proof -
    have inner: "integral\<^sup>L lborel (\<lambda>c. \<Sum>k<M. ?B j k c) =
        (\<Sum>k<M. integral\<^sup>L lborel (?B j k))" if "j < N" for j
      by (rule Bochner_Integration.integral_sum)
        (simp add: outer_mixed that)
    show ?thesis
      by (subst Bochner_Integration.integral_sum)
        (simp_all add: mixed_inner_outer_integrable inner)
  qed
  have root_expansion:
      "integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_cgo_born_partial_bracket X N M tau c cutoff q qt z) =
        integral\<^sup>L lborel (\<lambda>z. Q z * slp_center_kernel tau c z) +
        (\<Sum>j<N. integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_left_neumann_iterate j tau c cutoff q SLP_Dbar_Inverse z)) +
        (\<Sum>k<M. integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z)) +
        (\<Sum>j<N. \<Sum>k<M. integral\<^sup>L lborel (\<lambda>z.
          Q z * slp_center_kernel (- tau) c z *
          slp_left_neumann_iterate j tau c cutoff q SLP_Dbar_Inverse z *
          slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z))"
    for c
    by (rule slp_cgo_born_partial_root_integral_expansion[OF Q_outside
          root_leading root_left root_right root_mixed])
  have outer_pointwise:
      "(\<lambda>c. phi c * integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_cgo_born_partial_bracket X N M tau c cutoff q qt z)) =
        (\<lambda>c. phi c *
          integral\<^sup>L lborel (\<lambda>z. Q z * slp_center_kernel tau c z) +
          (\<Sum>j<N. ?L j c) + (\<Sum>k<M. ?R k c) +
          (\<Sum>j<N. \<Sum>k<M. ?B j k c))"
    by (rule ext) (simp only: root_expansion sum_distrib_left algebra_simps)
  have outer_integral:
      "integral\<^sup>L lborel (\<lambda>c. phi c * integral\<^sup>L lborel
          (\<lambda>z. Q z * slp_cgo_born_partial_bracket
            X N M tau c cutoff q qt z)) =
        integral\<^sup>L lborel (\<lambda>c. phi c *
          integral\<^sup>L lborel (\<lambda>z. Q z * slp_center_kernel tau c z)) +
        (\<Sum>j<N. integral\<^sup>L lborel (?L j)) +
        (\<Sum>k<M. integral\<^sup>L lborel (?R k)) +
        (\<Sum>j<N. \<Sum>k<M. integral\<^sup>L lborel (?B j k))"
    unfolding outer_pointwise
    by (simp only:
        Bochner_Integration.integral_add[OF outer_leading
          left_outer_integrable]
        Bochner_Integration.integrable_add[OF outer_leading
          left_outer_integrable]
        Bochner_Integration.integral_add[OF
          Bochner_Integration.integrable_add[OF outer_leading
            left_outer_integrable] right_outer_integrable]
        Bochner_Integration.integrable_add[OF
          Bochner_Integration.integrable_add[OF outer_leading
            left_outer_integrable] right_outer_integrable]
        Bochner_Integration.integral_add[OF
          Bochner_Integration.integrable_add[OF
            Bochner_Integration.integrable_add[OF outer_leading
              left_outer_integrable] right_outer_integrable]
          mixed_outer_integrable]
        left_outer_integral right_outer_integral mixed_outer_integral)
  show ?thesis
    unfolding slp_cgo_born_tested_partial_functional_def outer_integral
      slp_left_born_functional_def slp_right_born_functional_def
      slp_mixed_born_functional_def
    using slp_nested_leading_functional_eq[where tau=tau and phi=phi and Q=Q]
    unfolding slp_nested_leading_functional_def
    by (simp add: divide_inverse sum_distrib_left algebra_simps)
qed

end
