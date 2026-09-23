theory Inverse_Schrodinger_Lp_Zero_Extension_Invariance
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_018.Inverse_Schrodinger_Lp_Physical_Subquadratic_Recovery"
begin

section \<open>Invariance under the physical zero extension\<close>

lemma slp_restrict_field_idem:
  "slp_restrict_field U (slp_restrict_field U V) = slp_restrict_field U V"
  by (rule ext) (simp add: slp_restrict_field_def)

lemma slp_complex_lp_on_restrict_field_iff:
  "slp_complex_lp_on p U (slp_restrict_field U V) \<longleftrightarrow>
    slp_complex_lp_on p U V"
  unfolding slp_complex_lp_on_def
  by (simp add: slp_restrict_field_idem)

lemma slp_indicator_restrict_potential:
  "(\<lambda>x. indicator U x *\<^sub>R
      (slp_restrict_field U V x * F x * G x)) =
    (\<lambda>x. indicator U x *\<^sub>R (V x * F x * G x))"
proof (rule ext)
  fix x
  show "indicator U x *\<^sub>R
      (slp_restrict_field U V x * F x * G x) =
    indicator U x *\<^sub>R (V x * F x * G x)"
    by (cases "x \<in> U")
      (simp_all add: indicator_def slp_restrict_field_def)
qed

lemma slp_indicator_restrict_potential_difference:
  "(\<lambda>x. indicator U x *\<^sub>R
      ((slp_restrict_field U V x -
        slp_restrict_field U V_tilde x) * F x * G x)) =
    (\<lambda>x. indicator U x *\<^sub>R
      ((V x - V_tilde x) * F x * G x))"
proof (rule ext)
  fix x
  show "indicator U x *\<^sub>R
      ((slp_restrict_field U V x -
        slp_restrict_field U V_tilde x) * F x * G x) =
    indicator U x *\<^sub>R ((V x - V_tilde x) * F x * G x)"
    by (cases "x \<in> U")
      (simp_all add: indicator_def slp_restrict_field_def)
qed

lemma slp_weak_form_integrable_restrict_potential_iff:
  "slp_weak_form_integrable U (slp_restrict_field U V) F G \<longleftrightarrow>
    slp_weak_form_integrable U V F G"
  unfolding slp_weak_form_integrable_def set_integrable_def
  by (simp only: slp_indicator_restrict_potential)

lemma slp_weak_form_restrict_potential:
  "slp_weak_form U (slp_restrict_field U V) F G =
    slp_weak_form U V F G"
  unfolding slp_weak_form_def set_lebesgue_integral_def
  by (simp only: slp_indicator_restrict_potential)

lemma slp_weak_solution_restrict_potential_iff:
  "slp_weak_solution U (slp_restrict_field U V) F \<longleftrightarrow>
    slp_weak_solution U V F"
  unfolding slp_weak_solution_def
  by (simp add: slp_weak_form_integrable_restrict_potential_iff
      slp_weak_form_restrict_potential)

theorem slp_alessandrini_orthogonality_restrict_potentials:
  assumes orthogonality: "slp_alessandrini_orthogonality U V V_tilde"
  shows "slp_alessandrini_orthogonality U
    (slp_restrict_field U V) (slp_restrict_field U V_tilde)"
proof -
  have pairing_integrable:
      "\<And>F G. set_integrable lborel U
          (\<lambda>x. (slp_restrict_field U V x -
            slp_restrict_field U V_tilde x) * fst F x * fst G x) \<longleftrightarrow>
        set_integrable lborel U
          (\<lambda>x. (V x - V_tilde x) * fst F x * fst G x)"
    unfolding set_integrable_def
    by (simp only: slp_indicator_restrict_potential_difference)
  have pairing_integral:
      "\<And>F G. set_lebesgue_integral lborel U
          (\<lambda>x. (slp_restrict_field U V x -
            slp_restrict_field U V_tilde x) * fst F x * fst G x) =
        set_lebesgue_integral lborel U
          (\<lambda>x. (V x - V_tilde x) * fst F x * fst G x)"
    unfolding set_lebesgue_integral_def
    by (simp only: slp_indicator_restrict_potential_difference)
  show ?thesis
    using orthogonality
    unfolding slp_alessandrini_orthogonality_def
    by (simp add: slp_weak_solution_restrict_potential_iff
        pairing_integrable pairing_integral)
qed

lemma slp_potential_ae_equal_restrict_potentials_iff:
  assumes measurable_U: "U \<in> sets lborel"
  shows "slp_potential_ae_equal U
      (slp_restrict_field U V) (slp_restrict_field U V_tilde) \<longleftrightarrow>
    slp_potential_ae_equal U V V_tilde"
  unfolding slp_potential_ae_equal_def
  using measurable_U
  by (simp add: AE_restrict_space_iff slp_restrict_field_def)

end
