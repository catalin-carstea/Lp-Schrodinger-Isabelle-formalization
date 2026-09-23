theory Inverse_Schrodinger_Lp_CGO_Born_Tested_Zero
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_CGO_Born_Finite_Functionals"
begin

hide_const (open) Commutative_Ring.norm

section \<open>From the conull Born identity to the full tested zero\<close>

definition slp_cgo_born_tested_neumann_functional ::
    "slp_point set \<Rightarrow> real \<Rightarrow> slp_scalar_field \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow> complex"
  where
  "slp_cgo_born_tested_neumann_functional X tau phi Q cutoff q qt =
    of_real tau * inverse (of_real pi) *
      integral\<^sup>L lborel (\<lambda>c. phi c *
        integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_cgo_born_neumann_bracket X tau c cutoff q qt z))"

lemma slp_cgo_born_neumann_root_integrable_zero:
  assumes Q_outside: "\<And>z. z \<notin> Omega \<Longrightarrow> Q z = 0"
    and born_integrable:
      "set_integrable lborel Omega (\<lambda>z. Q z *
        slp_cgo_born_neumann_bracket X tau c cutoff q qt z)"
    and born_zero:
      "set_lebesgue_integral lborel Omega (\<lambda>z. Q z *
        slp_cgo_born_neumann_bracket X tau c cutoff q qt z) = 0"
  shows
    "integrable lborel (\<lambda>z. Q z *
        slp_cgo_born_neumann_bracket X tau c cutoff q qt z)
      \<and> integral\<^sup>L lborel (\<lambda>z. Q z *
        slp_cgo_born_neumann_bracket X tau c cutoff q qt z) = 0"
proof -
  have indicator_identity:
      "(\<lambda>z. indicator Omega z *\<^sub>R
          (Q z * slp_cgo_born_neumann_bracket
            X tau c cutoff q qt z)) =
        (\<lambda>z. Q z * slp_cgo_born_neumann_bracket
          X tau c cutoff q qt z)"
  proof (rule ext)
    fix z
    show "indicator Omega z *\<^sub>R
        (Q z * slp_cgo_born_neumann_bracket X tau c cutoff q qt z) =
      Q z * slp_cgo_born_neumann_bracket X tau c cutoff q qt z"
      by (cases "z \<in> Omega")
        (simp_all add: indicator_def Q_outside)
  qed
  have global_integrable:
      "integrable lborel (\<lambda>z. Q z *
        slp_cgo_born_neumann_bracket X tau c cutoff q qt z)"
    using born_integrable
    unfolding set_integrable_def
    by (simp only: indicator_identity)
  have global_zero:
      "integral\<^sup>L lborel (\<lambda>z. Q z *
        slp_cgo_born_neumann_bracket X tau c cutoff q qt z) = 0"
    using born_zero
    unfolding set_lebesgue_integral_def
    by (simp only: indicator_identity)
  show ?thesis by (rule conjI[OF global_integrable global_zero])
qed

theorem slp_cgo_born_tested_neumann_functional_zero:
  assumes phi_test: "slp_test_function_on Omega phi"
    and Q_outside: "\<And>z. z \<notin> Omega \<Longrightarrow> Q z = 0"
    and carrier_AE:
      "AE c in (lborel :: slp_point measure).
        c \<in> Omega \<longleftrightarrow> c \<in> Z"
    and born_integrable:
      "\<And>c. c \<in> Z \<Longrightarrow>
        set_integrable lborel Omega (\<lambda>z. Q z *
          slp_cgo_born_neumann_bracket X tau c cutoff q qt z)"
    and born_zero:
      "\<And>c. c \<in> Z \<Longrightarrow>
        set_lebesgue_integral lborel Omega (\<lambda>z. Q z *
          slp_cgo_born_neumann_bracket X tau c cutoff q qt z) = 0"
  shows
    "slp_cgo_born_tested_neumann_functional
      X tau phi Q cutoff q qt = 0"
proof -
  have phi_restriction: "slp_restrict_field Omega phi = phi"
    by (rule slp_test_function_restrict_field_eq[OF phi_test])
  have phi_outside: "phi c = 0" if c_outside: "c \<notin> Omega" for c
  proof -
    have "slp_restrict_field Omega phi c = phi c"
      using fun_cong[OF phi_restriction, of c] .
    then show ?thesis
      by (simp add: slp_restrict_field_def c_outside)
  qed
  have root_zero:
      "integral\<^sup>L lborel (\<lambda>z. Q z *
        slp_cgo_born_neumann_bracket X tau c cutoff q qt z) = 0"
    if c_in: "c \<in> Z" for c
    using slp_cgo_born_neumann_root_integrable_zero[
      OF Q_outside born_integrable[OF c_in] born_zero[OF c_in]]
    by blast
  have weighted_zero:
      "AE c in (lborel :: slp_point measure).
        phi c * integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_cgo_born_neumann_bracket X tau c cutoff q qt z) = 0"
    using carrier_AE
  proof eventually_elim
    fix c
    assume carrier: "c \<in> Omega \<longleftrightarrow> c \<in> Z"
    show "phi c * integral\<^sup>L lborel (\<lambda>z. Q z *
        slp_cgo_born_neumann_bracket X tau c cutoff q qt z) = 0"
    proof (cases "c \<in> Omega")
      case True
      then have "c \<in> Z" using carrier by blast
      then show ?thesis by (simp add: root_zero)
    next
      case False
      then show ?thesis by (simp add: phi_outside)
    qed
  qed
  have outer_zero:
      "integral\<^sup>L lborel (\<lambda>c. phi c *
        integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_cgo_born_neumann_bracket X tau c cutoff q qt z)) = 0"
    by (rule integral_eq_zero_AE[OF weighted_zero])
  show ?thesis
    unfolding slp_cgo_born_tested_neumann_functional_def outer_zero
    by simp
qed

end
