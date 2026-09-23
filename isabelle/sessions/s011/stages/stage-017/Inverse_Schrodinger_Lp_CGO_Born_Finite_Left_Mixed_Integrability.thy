theory Inverse_Schrodinger_Lp_CGO_Born_Finite_Left_Mixed_Integrability
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_CGO_Born_Tested_Finite_Families"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Finite left and mixed Born component integrability\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_cgo_born_finite_left_mixed_integrability:
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
    "(\<forall>c j. j < N \<longrightarrow> integrable lborel (\<lambda>z. Q z *
        slp_left_neumann_iterate j tau c cutoff q SLP_Dbar_Inverse z)) \<and>
     (\<forall>j. j < N \<longrightarrow> integrable lborel (\<lambda>c. phi c *
        integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_left_neumann_iterate j tau c cutoff q SLP_Dbar_Inverse z))) \<and>
     (\<forall>c j k. j < N \<longrightarrow> k < M \<longrightarrow>
        integrable lborel (\<lambda>z. Q z * slp_center_kernel (- tau) c z *
          slp_left_neumann_iterate j tau c cutoff q SLP_Dbar_Inverse z *
          slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z)) \<and>
     (\<forall>j k. j < N \<longrightarrow> k < M \<longrightarrow>
        integrable lborel (\<lambda>c. phi c * integral\<^sup>L lborel (\<lambda>z.
          Q z * slp_center_kernel (- tau) c z *
          slp_left_neumann_iterate j tau c cutoff q SLP_Dbar_Inverse z *
          slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z)))"
proof -
  have left_data:
      "integrable lborel (\<lambda>z. Q z *
          slp_left_neumann_iterate j tau c cutoff q SLP_Dbar_Inverse z) \<and>
       integrable lborel (\<lambda>y. phi y * integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_left_neumann_iterate j tau y cutoff q SLP_Dbar_Inverse z))"
    for c j
  proof -
    note identity = slp_natural_one_sided_born_bracket_identity[
      OF R_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable q_lp Q_lp Q_outside cutoff_bound C_nonnegative
        Q_support cutoff_support q_support phi_test,
      where n=j and tau=tau and orientation=SLP_Dbar_Inverse]
    show ?thesis using identity by (auto simp only: Let_def)
  qed
  have mixed_data:
      "integrable lborel (\<lambda>z. Q z * slp_center_kernel (- tau) c z *
          slp_left_neumann_iterate j tau c cutoff q SLP_Dbar_Inverse z *
          slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z) \<and>
       integrable lborel (\<lambda>y. phi y * integral\<^sup>L lborel (\<lambda>z.
          Q z * slp_center_kernel (- tau) y z *
          slp_left_neumann_iterate j tau y cutoff q SLP_Dbar_Inverse z *
          slp_right_neumann_iterate k tau y cutoff qt SLP_Partial_Inverse z))"
    for c j k
  proof -
    note identity = slp_natural_mixed_born_bracket_identity[
      OF R_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound Q_support
        cutoff_support q_support qt_support phi_test,
      where n=j and m=k and tau=tau and lo=SLP_Dbar_Inverse
        and ro=SLP_Partial_Inverse]
    show ?thesis using identity by (auto simp only: Let_def)
  qed
  show ?thesis using left_data mixed_data by blast
qed

end

end
