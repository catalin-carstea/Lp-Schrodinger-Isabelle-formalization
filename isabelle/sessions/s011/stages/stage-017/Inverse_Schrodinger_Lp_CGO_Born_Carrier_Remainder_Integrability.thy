theory Inverse_Schrodinger_Lp_CGO_Born_Carrier_Remainder_Integrability
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_CGO_Born_Finite_Assembly"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Remainder integrability on the admissible center carrier\<close>

theorem slp_cgo_born_carrier_remainder_integrability:
  fixes N M :: nat and X Omega Z :: "slp_point set" and tau :: real
    and phi Q cutoff q qt :: slp_scalar_field
  assumes phi_test: "slp_test_function_on Omega phi"
    and Q_outside: "\<And>z. z \<notin> X \<Longrightarrow> Q z = 0"
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
    and outer_remainder_measurable:
      "(\<lambda>c. phi c * integral\<^sup>L lborel (\<lambda>z. Q z *
        slp_cgo_born_neumann_remainder X N M tau c cutoff q qt z))
          \<in> borel_measurable lborel"
    and born_integrable:
      "\<And>c. c \<in> Z \<Longrightarrow> set_integrable lborel X (\<lambda>z. Q z *
        slp_cgo_born_neumann_bracket X tau c cutoff q qt z)"
    and born_zero:
      "\<And>c. c \<in> Z \<Longrightarrow> set_lebesgue_integral lborel X (\<lambda>z. Q z *
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

end
