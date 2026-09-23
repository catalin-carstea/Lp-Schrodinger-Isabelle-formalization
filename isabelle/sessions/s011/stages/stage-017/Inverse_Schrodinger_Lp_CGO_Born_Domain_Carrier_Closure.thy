theory Inverse_Schrodinger_Lp_CGO_Born_Domain_Carrier_Closure
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_CGO_Born_Remainder_Measurable"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Physical-domain carrier closure for the Born remainder\<close>

theorem slp_cgo_born_domain_carrier_remainder_integrability:
  fixes N M :: nat and X Omega Z :: "slp_point set" and tau :: real
    and phi Q cutoff q qt :: slp_scalar_field
  assumes phi_test: "slp_test_function_on Omega phi"
    and X_measurable: "X \<in> sets lborel"
    and Q_measurable: "Q \<in> borel_measurable lborel"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and q_measurable: "q \<in> borel_measurable lborel"
    and qt_measurable: "qt \<in> borel_measurable lborel"
    and Q_outside: "\<And>z. z \<notin> Omega \<Longrightarrow> Q z = 0"
    and carrier_AE:
      "AE c in (lborel :: slp_point measure).
        c \<in> Omega \<longleftrightarrow> c \<in> Z"
    and root_partial:
      "\<And>c. integrable lborel (\<lambda>z. Q z *
        slp_cgo_born_partial_bracket X N M tau c cutoff q qt z)"
    and outer_partial:
      "integrable lborel (\<lambda>c. phi c *
        integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_cgo_born_partial_bracket X N M tau c cutoff q qt z))"
    and born_integrable:
      "\<And>c. c \<in> Z \<Longrightarrow> set_integrable lborel Omega (\<lambda>z. Q z *
        slp_cgo_born_neumann_bracket X tau c cutoff q qt z)"
    and born_zero:
      "\<And>c. c \<in> Z \<Longrightarrow> set_lebesgue_integral lborel Omega
        (\<lambda>z. Q z *
          slp_cgo_born_neumann_bracket X tau c cutoff q qt z) = 0"
  shows
    "(\<forall>c \<in> Z. integrable lborel (\<lambda>z. Q z *
        slp_cgo_born_neumann_remainder X N M tau c cutoff q qt z) \<and>
       integral\<^sup>L lborel (\<lambda>z. Q z *
        slp_cgo_born_neumann_remainder X N M tau c cutoff q qt z) =
       - integral\<^sup>L lborel (\<lambda>z. Q z *
        slp_cgo_born_partial_bracket X N M tau c cutoff q qt z)) \<and>
     integrable lborel (\<lambda>c. phi c *
       integral\<^sup>L lborel (\<lambda>z. Q z *
         slp_cgo_born_neumann_remainder X N M tau c cutoff q qt z)) \<and>
     slp_cgo_born_tested_partial_functional X N M tau phi Q cutoff q qt =
       - slp_cgo_born_tested_neumann_remainder_functional
           X N M tau phi Q cutoff q qt"
proof -
  have phi_smooth: "smooth_on UNIV phi"
    using phi_test unfolding slp_test_function_on_def by blast
  have phi_continuous: "continuous_on UNIV phi"
    by (rule smooth_on_imp_continuous_on[OF phi_smooth])
  have phi_measurable: "phi \<in> borel_measurable lborel"
    using borel_measurable_continuous_onI[OF phi_continuous] by simp
  have outer_remainder_measurable:
      "(\<lambda>c. phi c * integral\<^sup>L lborel (\<lambda>z. Q z *
        slp_cgo_born_neumann_remainder X N M tau c cutoff q qt z))
          \<in> borel_measurable lborel"
    by (rule slp_cgo_born_tested_neumann_remainder_outer_measurable[
          OF X_measurable phi_measurable Q_measurable cutoff_measurable
            q_measurable qt_measurable])
  have phi_outside: "phi c = 0" if c_outside: "c \<notin> Omega" for c
  proof -
    have restriction: "slp_restrict_field Omega phi c = phi c"
      by (rule fun_cong[OF slp_test_function_restrict_field_eq[OF phi_test]])
    show ?thesis
      using restriction c_outside by (simp add: slp_restrict_field_def)
  qed
  have root_remainder:
      "integrable lborel (\<lambda>z. Q z *
          slp_cgo_born_neumann_remainder X N M tau c cutoff q qt z) \<and>
       integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_cgo_born_neumann_remainder X N M tau c cutoff q qt z) =
        - integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_cgo_born_partial_bracket X N M tau c cutoff q qt z)"
    if c_in: "c \<in> Z" for c
  proof -
    have full:
        "integrable lborel (\<lambda>z. Q z *
            slp_cgo_born_neumann_bracket X tau c cutoff q qt z) \<and>
         integral\<^sup>L lborel (\<lambda>z. Q z *
            slp_cgo_born_neumann_bracket X tau c cutoff q qt z) = 0"
      by (rule slp_cgo_born_neumann_root_integrable_zero[
            OF Q_outside born_integrable[OF c_in] born_zero[OF c_in]])
    have integrand_difference:
        "(\<lambda>z. Q z *
            slp_cgo_born_neumann_remainder X N M tau c cutoff q qt z) =
          (\<lambda>z. Q z *
              slp_cgo_born_neumann_bracket X tau c cutoff q qt z -
            Q z * slp_cgo_born_partial_bracket
              X N M tau c cutoff q qt z)"
    proof (rule ext)
      fix z
      have split:
          "slp_cgo_born_neumann_bracket X tau c cutoff q qt z =
            slp_cgo_born_partial_bracket X N M tau c cutoff q qt z +
            slp_cgo_born_neumann_remainder X N M tau c cutoff q qt z"
        by (rule slp_cgo_born_neumann_bracket_finite_remainder[
              where N=N and M=M])
      show "Q z * slp_cgo_born_neumann_remainder X N M tau c cutoff q qt z =
        Q z * slp_cgo_born_neumann_bracket X tau c cutoff q qt z -
          Q z * slp_cgo_born_partial_bracket X N M tau c cutoff q qt z"
        using split by (simp add: algebra_simps)
    qed
    have remainder_integrable:
        "integrable lborel (\<lambda>z. Q z *
          slp_cgo_born_neumann_remainder X N M tau c cutoff q qt z)"
      unfolding integrand_difference
      by (rule Bochner_Integration.integrable_diff)
        (use full root_partial in blast)+
    have remainder_integral:
        "integral\<^sup>L lborel (\<lambda>z. Q z *
            slp_cgo_born_neumann_remainder X N M tau c cutoff q qt z) =
          integral\<^sup>L lborel (\<lambda>z. Q z *
            slp_cgo_born_neumann_bracket X tau c cutoff q qt z) -
          integral\<^sup>L lborel (\<lambda>z. Q z *
            slp_cgo_born_partial_bracket X N M tau c cutoff q qt z)"
      unfolding integrand_difference
      by (rule Bochner_Integration.integral_diff)
        (use full root_partial in blast)+
    show ?thesis
      using remainder_integrable remainder_integral full by simp
  qed
  have outer_AE:
      "AE c in (lborel :: slp_point measure).
        phi c * integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_cgo_born_neumann_remainder X N M tau c cutoff q qt z) =
        - (phi c * integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_cgo_born_partial_bracket X N M tau c cutoff q qt z))"
    using carrier_AE
  proof eventually_elim
    fix c
    assume carrier: "c \<in> Omega \<longleftrightarrow> c \<in> Z"
    show "phi c * integral\<^sup>L lborel (\<lambda>z. Q z *
        slp_cgo_born_neumann_remainder X N M tau c cutoff q qt z) =
      - (phi c * integral\<^sup>L lborel (\<lambda>z. Q z *
        slp_cgo_born_partial_bracket X N M tau c cutoff q qt z))"
    proof (cases "c \<in> Omega")
      case True
      then have "c \<in> Z" using carrier by blast
      then show ?thesis using root_remainder by simp
    next
      case False
      then show ?thesis by (simp add: phi_outside)
    qed
  qed
  have outer_partial_negative:
      "integrable lborel (\<lambda>c. - (phi c *
        integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_cgo_born_partial_bracket X N M tau c cutoff q qt z)))"
    using outer_partial by simp
  have outer_remainder:
      "integrable lborel (\<lambda>c. phi c *
        integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_cgo_born_neumann_remainder X N M tau c cutoff q qt z))"
    by (rule integrable_cong_AE_imp[
          OF outer_partial_negative outer_remainder_measurable])
      (use outer_AE in eventually_elim; simp)
  have outer_integral:
      "integral\<^sup>L lborel (\<lambda>c. phi c *
          integral\<^sup>L lborel (\<lambda>z. Q z *
            slp_cgo_born_neumann_remainder X N M tau c cutoff q qt z)) =
        - integral\<^sup>L lborel (\<lambda>c. phi c *
          integral\<^sup>L lborel (\<lambda>z. Q z *
            slp_cgo_born_partial_bracket X N M tau c cutoff q qt z))"
  proof -
    have negative_measurable:
        "(\<lambda>c. - (phi c * integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_cgo_born_partial_bracket X N M tau c cutoff q qt z)))
            \<in> borel_measurable lborel"
      using outer_partial_negative by measurable
    have equality:
        "integral\<^sup>L lborel (\<lambda>c. phi c *
            integral\<^sup>L lborel (\<lambda>z. Q z *
              slp_cgo_born_neumann_remainder X N M tau c cutoff q qt z)) =
          integral\<^sup>L lborel (\<lambda>c. - (phi c *
            integral\<^sup>L lborel (\<lambda>z. Q z *
              slp_cgo_born_partial_bracket X N M tau c cutoff q qt z)))"
      by (rule integral_cong_AE[
            OF outer_remainder_measurable negative_measurable outer_AE])
    show ?thesis
      using equality outer_partial by simp
  qed
  have functional_equality:
      "slp_cgo_born_tested_partial_functional X N M tau phi Q cutoff q qt =
        - slp_cgo_born_tested_neumann_remainder_functional
            X N M tau phi Q cutoff q qt"
    unfolding slp_cgo_born_tested_partial_functional_def
      slp_cgo_born_tested_neumann_remainder_functional_def outer_integral
    by simp
  show ?thesis
    using root_remainder outer_remainder functional_equality by blast
qed

context aim_planar_riesz_hls_cauchy
begin

theorem slp_cgo_born_domain_carrier_finite_families_eq_neg_remainder:
  fixes N M :: nat and R C p tau :: real
    and X Omega Z :: "slp_point set"
    and phi cutoff q qt Q :: slp_scalar_field
  assumes R_nonnegative: "0 \<le> R"
    and C_nonnegative: "0 \<le> C"
    and p_lower: "1 < p" and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel" and X_bounded: "bounded X"
    and Omega_subset: "Omega \<subseteq> X"
    and cutoff_measurable[measurable]: "cutoff \<in> borel_measurable lborel"
    and q_lp: "aim_complex_lp_on_plane p q"
    and qt_lp: "aim_complex_lp_on_plane p qt"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and Q_outside: "\<And>x. x \<notin> Omega \<Longrightarrow> Q x = 0"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and q_support: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and qt_support: "\<And>x. qt x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and phi_test: "slp_test_function_on Omega phi"
    and carrier_AE:
      "AE c in (lborel :: slp_point measure).
        c \<in> Omega \<longleftrightarrow> c \<in> Z"
    and born_integrable:
      "\<And>c. c \<in> Z \<Longrightarrow> set_integrable lborel Omega (\<lambda>z. Q z *
        slp_cgo_born_neumann_bracket X tau c cutoff q qt z)"
    and born_zero:
      "\<And>c. c \<in> Z \<Longrightarrow> set_lebesgue_integral lborel Omega
        (\<lambda>z. Q z *
          slp_cgo_born_neumann_bracket X tau c cutoff q qt z) = 0"
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
  have phi_test_UNIV: "slp_test_function_on UNIV phi"
    using phi_test unfolding slp_test_function_on_def by blast
  have q_measurable: "q \<in> borel_measurable lborel"
    using q_lp unfolding aim_complex_lp_on_plane_def by blast
  have qt_measurable: "qt \<in> borel_measurable lborel"
    using qt_lp unfolding aim_complex_lp_on_plane_def by blast
  have Q_measurable: "Q \<in> borel_measurable lborel"
    using Q_lp unfolding aim_complex_lp_on_plane_def by blast
  have Q_outside_X: "Q x = 0" if x_outside: "x \<notin> X" for x
  proof -
    have "x \<notin> Omega" using Omega_subset x_outside by blast
    then show ?thesis by (rule Q_outside)
  qed
  note left_mixed = slp_cgo_born_finite_left_mixed_integrability[
    OF R_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
      cutoff_measurable q_lp qt_lp Q_lp Q_outside_X cutoff_bound Q_support
      cutoff_support q_support qt_support phi_test_UNIV,
    where N=N and M=M and tau=tau]
  note right = slp_cgo_born_finite_right_integrability[
    OF R_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
      cutoff_measurable qt_lp Q_lp Q_outside_X cutoff_bound Q_support
      cutoff_support qt_support phi_test_UNIV,
    where M=M and tau=tau]
  note leading = slp_cgo_born_leading_integrability[
    OF p_lower X_measurable X_bounded Q_lp Q_outside_X phi_test_UNIV,
    where tau=tau]
  note partial = slp_cgo_born_finite_partial_integrability[
    OF R_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
      cutoff_measurable q_lp qt_lp Q_lp Q_outside_X cutoff_bound Q_support
      cutoff_support q_support qt_support phi_test_UNIV,
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
  note remainder = slp_cgo_born_domain_carrier_remainder_integrability[
    OF phi_test X_measurable Q_measurable cutoff_measurable q_measurable
      qt_measurable Q_outside carrier_AE root_partial outer_partial
      born_integrable born_zero]
  have partial_eq_remainder:
      "slp_cgo_born_tested_partial_functional
          X N M tau phi Q cutoff q qt =
        - slp_cgo_born_tested_neumann_remainder_functional
            X N M tau phi Q cutoff q qt"
    using remainder by blast
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
        slp_right_neumann_iterate k tau c cutoff qt
          SLP_Partial_Inverse z))"
    if "j < N" "k < M" for j k
    using left_mixed that by blast
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
          Q_outside_X root_leading root_left root_right root_mixed
          outer_leading outer_left outer_right outer_mixed])
  show ?thesis
    unfolding partial_expansion[symmetric]
    by (rule partial_eq_remainder)
qed

end

end
