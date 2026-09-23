theory Inverse_Schrodinger_Lp_CGO_Born_Finite_Right_Integrability
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_CGO_Born_Finite_Left_Mixed_Integrability"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Finite right Born component integrability\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_cgo_born_finite_right_integrability:
  fixes M :: nat and R C p tau :: real and X :: "slp_point set"
    and phi cutoff qt Q :: slp_scalar_field
  assumes R_nonnegative: "0 \<le> R"
    and C_nonnegative: "0 \<le> C"
    and p_lower: "1 < p" and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel" and X_bounded: "bounded X"
    and cutoff_measurable[measurable]: "cutoff \<in> borel_measurable lborel"
    and qt_lp: "aim_complex_lp_on_plane p qt"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and Q_outside: "\<And>x. x \<notin> X \<Longrightarrow> Q x = 0"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and qt_support: "\<And>x. qt x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and phi_test: "slp_test_function_on UNIV phi"
  shows
    "(\<forall>c k. k < M \<longrightarrow> integrable lborel (\<lambda>z. Q z *
        slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z)) \<and>
     (\<forall>k. k < M \<longrightarrow> integrable lborel (\<lambda>c. phi c *
        integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z)))"
proof -
  let ?Qc = "\<lambda>x. cnj (Q x)"
  let ?cutoffc = "\<lambda>x. cnj (cutoff x)"
  let ?qtc = "\<lambda>x. cnj (qt x)"
  let ?phic = "\<lambda>x. cnj (phi x)"
  have cnj_borel: "cnj \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF
          continuous_on_cnj[OF continuous_on_id]])
  have cutoffc_measurable[measurable]:
      "?cutoffc \<in> borel_measurable lborel"
    using measurable_comp[OF cutoff_measurable cnj_borel]
    by (simp only: comp_def)
  have qtc_lp: "aim_complex_lp_on_plane p ?qtc"
    using qt_lp by simp
  have Qc_lp: "aim_complex_lp_on_plane p ?Qc"
    using Q_lp by simp
  have Qc_outside: "?Qc x = 0" if "x \<notin> X" for x
    using Q_outside[OF that] by simp
  have cutoffc_bound: "norm (?cutoffc x) \<le> C" for x
    using cutoff_bound[of x] by simp
  have Qc_support: "norm x \<le> R" if "?Qc x \<noteq> 0" for x
    by (rule Q_support) (use that in simp)
  have cutoffc_support: "norm x \<le> R" if "?cutoffc x \<noteq> 0" for x
    by (rule cutoff_support) (use that in simp)
  have qtc_support: "norm x \<le> R" if "?qtc x \<noteq> 0" for x
    by (rule qt_support) (use that in simp)
  have phic_test: "slp_test_function_on UNIV ?phic"
    using phi_test by simp
  have left_data:
      "integrable lborel (\<lambda>z. ?Qc z *
          slp_left_neumann_iterate k (- tau) c ?cutoffc ?qtc
            SLP_Dbar_Inverse z) \<and>
       integrable lborel (\<lambda>y. ?phic y * integral\<^sup>L lborel (\<lambda>z. ?Qc z *
          slp_left_neumann_iterate k (- tau) y ?cutoffc ?qtc
            SLP_Dbar_Inverse z))"
    for c k
  proof -
    note identity = slp_natural_one_sided_born_bracket_identity[
      OF R_nonnegative p_lower p_upper X_measurable X_bounded
        cutoffc_measurable qtc_lp Qc_lp Qc_outside cutoffc_bound
        C_nonnegative Qc_support cutoffc_support qtc_support phic_test,
      where n=k and tau="- tau"
        and orientation=SLP_Dbar_Inverse]
    show ?thesis using identity by (auto simp only: Let_def)
  qed
  have iterate_conjugate:
      "cnj (slp_left_neumann_iterate k (- tau) c ?cutoffc ?qtc
          SLP_Dbar_Inverse z) =
        slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z"
    for c k z
    using slp_left_neumann_iterate_conjugate_eq_right[
      where n=k and tau=tau and center=c and cutoff=cutoff and potential=qt
        and orientation=SLP_Partial_Inverse and origin=z]
    by simp
  have root_integrable:
      "integrable lborel (\<lambda>z. Q z *
        slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z)"
    for c k
  proof -
    have conjugate_integrable:
        "integrable lborel (\<lambda>z. cnj (?Qc z *
          slp_left_neumann_iterate k (- tau) c ?cutoffc ?qtc
            SLP_Dbar_Inverse z))"
      by (rule integrable_cnj[OF conjunct1[OF left_data[where c=c and k=k]]])
    show ?thesis
      using conjugate_integrable
      by (simp only: complex_cnj_mult complex_cnj_cnj iterate_conjugate)
  qed
  have inner_conjugate:
      "integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z) =
        cnj (integral\<^sup>L lborel (\<lambda>z. ?Qc z *
          slp_left_neumann_iterate k (- tau) c ?cutoffc ?qtc
            SLP_Dbar_Inverse z))"
    for c k
  proof -
    have move_conjugate:
        "integral\<^sup>L lborel (\<lambda>z. cnj (?Qc z *
            slp_left_neumann_iterate k (- tau) c ?cutoffc ?qtc
              SLP_Dbar_Inverse z)) =
          cnj (integral\<^sup>L lborel (\<lambda>z. ?Qc z *
            slp_left_neumann_iterate k (- tau) c ?cutoffc ?qtc
              SLP_Dbar_Inverse z))"
      by (rule Bochner_Integration.integral_cnj)
    show ?thesis
      using move_conjugate
      by (simp only: complex_cnj_mult complex_cnj_cnj iterate_conjugate)
  qed
  have outer_integrable:
      "integrable lborel (\<lambda>c. phi c * integral\<^sup>L lborel (\<lambda>z. Q z *
        slp_right_neumann_iterate k tau c cutoff qt SLP_Partial_Inverse z))"
    for k
  proof -
    have left_outer:
        "integrable lborel (\<lambda>c. ?phic c * integral\<^sup>L lborel (\<lambda>z. ?Qc z *
          slp_left_neumann_iterate k (- tau) c ?cutoffc ?qtc
            SLP_Dbar_Inverse z))"
      using conjunct2[OF left_data[where c=0 and k=k]] .
    have conjugate_integrable:
        "integrable lborel (\<lambda>c. cnj (?phic c * integral\<^sup>L lborel (\<lambda>z. ?Qc z *
          slp_left_neumann_iterate k (- tau) c ?cutoffc ?qtc
            SLP_Dbar_Inverse z)))"
      by (rule integrable_cnj[OF left_outer])
    show ?thesis
      using conjugate_integrable
      by (simp only: complex_cnj_mult complex_cnj_cnj inner_conjugate)
  qed
  show ?thesis using root_integrable outer_integrable by blast
qed

end

end
