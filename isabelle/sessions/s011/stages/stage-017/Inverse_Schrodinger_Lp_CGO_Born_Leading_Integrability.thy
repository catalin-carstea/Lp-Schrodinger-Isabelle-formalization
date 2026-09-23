theory Inverse_Schrodinger_Lp_CGO_Born_Leading_Integrability
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_CGO_Born_Finite_Right_Integrability"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Leading Born component integrability\<close>

theorem slp_cgo_born_leading_integrability:
  fixes p tau :: real and X :: "slp_point set" and phi Q :: slp_scalar_field
  assumes p_lower: "1 < p"
    and X_measurable: "X \<in> sets lborel" and X_bounded: "bounded X"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and Q_outside: "\<And>x. x \<notin> X \<Longrightarrow> Q x = 0"
    and phi_test: "slp_test_function_on UNIV phi"
  shows
    "(\<forall>c. integrable lborel (\<lambda>z. Q z * slp_center_kernel tau c z)) \<and>
     integrable lborel (\<lambda>c. phi c * integral\<^sup>L lborel
       (\<lambda>z. Q z * slp_center_kernel tau c z))"
proof -
  have p_one: "1 \<le> p" using p_lower by linarith
  have Q_integrable: "integrable lborel Q"
    by (rule aim_complex_lp_on_plane_integrable_bounded_support[
      OF p_one X_measurable X_bounded Q_lp Q_outside])
  have phi_integrable: "integrable lborel phi"
    by (rule slp_test_function_integrable_bounded(1)[OF phi_test])
  have root_integrable:
      "integrable lborel (\<lambda>z. Q z * slp_center_kernel tau c z)" for c
    using slp_center_kernel_integrable_mult[OF Q_integrable, where tau=tau and c=c]
    by (simp add: mult.commute)
  have joint_integrable:
      "integrable (lborel \<Otimes>\<^sub>M lborel) (\<lambda>(c, z).
        phi c * (slp_center_kernel tau c z * Q z))"
    by (rule slp_center_product_integrable[OF phi_integrable Q_integrable])
  have section_integrable:
      "integrable lborel (\<lambda>c. integral\<^sup>L lborel (\<lambda>z.
        phi c * (slp_center_kernel tau c z * Q z)))"
    by (rule lborel_pair.integrable_fst[OF joint_integrable])
  have inner_identity:
      "integral\<^sup>L lborel (\<lambda>z. phi c *
          (slp_center_kernel tau c z * Q z)) =
        phi c * integral\<^sup>L lborel
          (\<lambda>z. Q z * slp_center_kernel tau c z)" for c
    by (simp only: Bochner_Integration.integral_mult_right_zero;
        simp add: mult.commute)
  show ?thesis using root_integrable section_integrable
    by (simp only: inner_identity; blast)
qed

end
