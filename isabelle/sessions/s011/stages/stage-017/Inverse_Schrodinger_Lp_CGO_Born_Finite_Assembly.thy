theory Inverse_Schrodinger_Lp_CGO_Born_Finite_Assembly
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_CGO_Born_Leading_Integrability"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Finite Born integrability assembly\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_cgo_born_finite_partial_integrability:
  fixes N M :: nat and R C p tau :: real and X :: "slp_point set"
    and phi cutoff q qt Q :: slp_scalar_field
  assumes R_nonnegative: "0 \<le> R"
    and C_nonnegative: "0 \<le> C"
    and p_lower: "1 < p" and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel" and X_bounded: "bounded X"
    and cutoff_measurable[measurable]: "cutoff \<in> borel_measurable lborel"
    and q_lp: "aim_complex_lp_on_plane p q"
    and qt_lp: "aim_complex_lp_on_plane p qt"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and Q_outside: "\<And>x. x \<notin> X \<Longrightarrow> Q x = 0"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and q_support: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and qt_support: "\<And>x. qt x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and phi_test: "slp_test_function_on UNIV phi"
  shows
    "(\<forall>c. integrable lborel (\<lambda>z. Q z *
        slp_cgo_born_partial_bracket X N M tau c cutoff q qt z)) \<and>
     integrable lborel (\<lambda>c. phi c *
       integral\<^sup>L lborel (\<lambda>z. Q z *
         slp_cgo_born_partial_bracket X N M tau c cutoff q qt z))"
proof -
  note left_mixed = slp_cgo_born_finite_left_mixed_integrability[
    OF R_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
      cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound Q_support
      cutoff_support q_support qt_support phi_test,
    where N=N and M=M and tau=tau]
  note right = slp_cgo_born_finite_right_integrability[
    OF R_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
      cutoff_measurable qt_lp Q_lp Q_outside cutoff_bound Q_support
      cutoff_support qt_support phi_test,
    where M=M and tau=tau]
  note leading = slp_cgo_born_leading_integrability[
    OF p_lower X_measurable X_bounded Q_lp Q_outside phi_test,
    where tau=tau]
  have root_leading:
      "integrable lborel (\<lambda>z. Q z * slp_center_kernel tau c z)" for c
    using leading by blast
  have root_left:
      "integrable lborel (\<lambda>z. Q z *
        slp_left_neumann_iterate j tau c cutoff q SLP_Dbar_Inverse z)"
    if "j < N" for c j
    using left_mixed that by blast
  have root_right:
      "integrable lborel (\<lambda>z. Q z *
        slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z)"
    if "k < M" for c k
    using right that by blast
  have root_mixed:
      "integrable lborel (\<lambda>z. Q z * slp_center_kernel (- tau) c z *
        slp_left_neumann_iterate j tau c cutoff q SLP_Dbar_Inverse z *
        slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z)"
    if "j < N" "k < M" for c j k
    using left_mixed that by blast
  have outer_leading:
      "integrable lborel (\<lambda>c. phi c * integral\<^sup>L lborel
        (\<lambda>z. Q z * slp_center_kernel tau c z))"
    using leading by blast
  have outer_left:
      "integrable lborel (\<lambda>c. phi c * integral\<^sup>L lborel (\<lambda>z. Q z *
        slp_left_neumann_iterate j tau c cutoff q SLP_Dbar_Inverse z))"
    if "j < N" for j
    using left_mixed that by blast
  have outer_right:
      "integrable lborel (\<lambda>c. phi c * integral\<^sup>L lborel (\<lambda>z. Q z *
        slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z))"
    if "k < M" for k
    using right that by blast
  have outer_mixed:
      "integrable lborel (\<lambda>c. phi c * integral\<^sup>L lborel (\<lambda>z.
        Q z * slp_center_kernel (- tau) c z *
        slp_left_neumann_iterate j tau c cutoff q SLP_Dbar_Inverse z *
        slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z))"
    if "j < N" "k < M" for j k
    using left_mixed that by blast
  have root_partial:
      "integrable lborel (\<lambda>z. Q z *
        slp_cgo_born_partial_bracket X N M tau c cutoff q qt z)" for c
  proof -
    have integrand_expansion:
        "(\<lambda>z. Q z *
            slp_cgo_born_partial_bracket X N M tau c cutoff q qt z) =
          (\<lambda>z. Q z * slp_center_kernel tau c z +
            (\<Sum>j<N. Q z *
              slp_left_neumann_iterate j tau c cutoff q SLP_Dbar_Inverse z) +
            (\<Sum>k<M. Q z *
              slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z) +
            (\<Sum>j<N. \<Sum>k<M. Q z * slp_center_kernel (- tau) c z *
              slp_left_neumann_iterate j tau c cutoff q SLP_Dbar_Inverse z *
              slp_right_neumann_iterate k tau c cutoff qt
                SLP_Partial_Inverse z))"
      by (rule ext)
        (rule slp_cgo_born_partial_weighted_expansion[OF Q_outside])
    show ?thesis
      unfolding integrand_expansion
      by (intro Bochner_Integration.integrable_add
          Bochner_Integration.integrable_sum)
        (auto intro: root_leading root_left root_right root_mixed)
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
          slp_right_neumann_iterate k tau c cutoff qt
            SLP_Partial_Inverse z))" for c
    by (rule slp_cgo_born_partial_root_integral_expansion[
      OF Q_outside root_leading root_left root_right root_mixed])
  have outer_integrand_expansion:
      "(\<lambda>c. phi c * integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_cgo_born_partial_bracket X N M tau c cutoff q qt z)) =
        (\<lambda>c. phi c * integral\<^sup>L lborel
            (\<lambda>z. Q z * slp_center_kernel tau c z) +
          (\<Sum>j<N. phi c * integral\<^sup>L lborel (\<lambda>z. Q z *
            slp_left_neumann_iterate j tau c cutoff q SLP_Dbar_Inverse z)) +
          (\<Sum>k<M. phi c * integral\<^sup>L lborel (\<lambda>z. Q z *
            slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z)) +
          (\<Sum>j<N. \<Sum>k<M. phi c * integral\<^sup>L lborel (\<lambda>z.
            Q z * slp_center_kernel (- tau) c z *
            slp_left_neumann_iterate j tau c cutoff q SLP_Dbar_Inverse z *
            slp_right_neumann_iterate k tau c cutoff qt
              SLP_Partial_Inverse z)))"
    by (rule ext) (simp only: root_expansion sum_distrib_left algebra_simps)
  have outer_partial:
      "integrable lborel (\<lambda>c. phi c *
        integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_cgo_born_partial_bracket X N M tau c cutoff q qt z))"
    unfolding outer_integrand_expansion
    by (intro Bochner_Integration.integrable_add
        Bochner_Integration.integrable_sum)
      (auto intro: outer_leading outer_left outer_right outer_mixed)
  show ?thesis using root_partial outer_partial by blast
qed

theorem slp_cgo_born_finite_families_eq_neg_remainder:
  fixes N M :: nat and R C p tau :: real and X :: "slp_point set"
    and phi cutoff q qt Q :: slp_scalar_field
  assumes R_nonnegative: "0 \<le> R"
    and C_nonnegative: "0 \<le> C"
    and p_lower: "1 < p" and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel" and X_bounded: "bounded X"
    and cutoff_measurable[measurable]: "cutoff \<in> borel_measurable lborel"
    and q_lp: "aim_complex_lp_on_plane p q"
    and qt_lp: "aim_complex_lp_on_plane p qt"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and Q_outside: "\<And>x. x \<notin> X \<Longrightarrow> Q x = 0"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and q_support: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and qt_support: "\<And>x. qt x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and phi_test: "slp_test_function_on UNIV phi"
    and root_remainder:
      "\<And>c. integrable lborel (\<lambda>z. Q z *
        slp_cgo_born_neumann_remainder X N M tau c cutoff q qt z)"
    and outer_remainder:
      "integrable lborel (\<lambda>c. phi c *
        integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_cgo_born_neumann_remainder X N M tau c cutoff q qt z))"
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
  note left_mixed = slp_cgo_born_finite_left_mixed_integrability[
    OF R_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
      cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound Q_support
      cutoff_support q_support qt_support phi_test,
    where N=N and M=M and tau=tau]
  note right = slp_cgo_born_finite_right_integrability[
    OF R_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
      cutoff_measurable qt_lp Q_lp Q_outside cutoff_bound Q_support
      cutoff_support qt_support phi_test,
    where M=M and tau=tau]
  note leading = slp_cgo_born_leading_integrability[
    OF p_lower X_measurable X_bounded Q_lp Q_outside phi_test,
    where tau=tau]
  note partial = slp_cgo_born_finite_partial_integrability[
    OF R_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
      cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound Q_support
      cutoff_support q_support qt_support phi_test,
    where N=N and M=M and tau=tau]
  have root_partial:
      "integrable lborel (\<lambda>z. Q z *
        slp_cgo_born_partial_bracket X N M tau c cutoff q qt z)" for c
    using partial by blast
  have outer_partial:
      "integrable lborel (\<lambda>c. phi c *
        integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_cgo_born_partial_bracket X N M tau c cutoff q qt z))"
    using partial by blast
  have root_leading:
      "integrable lborel (\<lambda>z. Q z * slp_center_kernel tau c z)" for c
    using leading by blast
  have root_left:
      "integrable lborel (\<lambda>z. Q z *
        slp_left_neumann_iterate j tau c cutoff q SLP_Dbar_Inverse z)"
    if "j < N" for c j
    using left_mixed that by blast
  have root_right:
      "integrable lborel (\<lambda>z. Q z *
        slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z)"
    if "k < M" for c k
    using right that by blast
  have root_mixed:
      "integrable lborel (\<lambda>z. Q z * slp_center_kernel (- tau) c z *
        slp_left_neumann_iterate j tau c cutoff q SLP_Dbar_Inverse z *
        slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z)"
    if "j < N" "k < M" for c j k
    using left_mixed that by blast
  have outer_leading:
      "integrable lborel (\<lambda>c. phi c * integral\<^sup>L lborel
        (\<lambda>z. Q z * slp_center_kernel tau c z))"
    using leading by blast
  have outer_left:
      "integrable lborel (\<lambda>c. phi c * integral\<^sup>L lborel (\<lambda>z. Q z *
        slp_left_neumann_iterate j tau c cutoff q SLP_Dbar_Inverse z))"
    if "j < N" for j
    using left_mixed that by blast
  have outer_right:
      "integrable lborel (\<lambda>c. phi c * integral\<^sup>L lborel (\<lambda>z. Q z *
        slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z))"
    if "k < M" for k
    using right that by blast
  have outer_mixed:
      "integrable lborel (\<lambda>c. phi c * integral\<^sup>L lborel (\<lambda>z.
        Q z * slp_center_kernel (- tau) c z *
        slp_left_neumann_iterate j tau c cutoff q SLP_Dbar_Inverse z *
        slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z))"
    if "j < N" "k < M" for j k
    using left_mixed that by blast
  show ?thesis
    by (rule slp_cgo_born_tested_finite_families_eq_neg_remainder[
      OF Q_outside root_partial root_remainder outer_partial outer_remainder
        root_leading root_left root_right root_mixed outer_leading outer_left
        outer_right outer_mixed full_zero])
qed

end

end
