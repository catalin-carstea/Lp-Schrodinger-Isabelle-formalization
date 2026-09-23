theory Inverse_Schrodinger_Lp_Neumann_Affine_Source_Bridge
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Conjugated_Cauchy_Source_Weak_Wirtinger"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_Exact_Neumann_Iterate_Bridge"
begin

section \<open>Pointwise additivity of the conjugated Cauchy operators\<close>

lemma slp_partial_psi_inverse_add_at:
  fixes f g :: slp_scalar_field
  assumes f_integrable:
    "slp_cauchy_integrable_at SLP_Partial_Inverse
      (slp_oscillatory_modulation tau c f) z"
    and g_integrable:
    "slp_cauchy_integrable_at SLP_Partial_Inverse
      (slp_oscillatory_modulation tau c g) z"
  shows
    "slp_partial_psi_inverse tau c f z +
        slp_partial_psi_inverse tau c g z =
      slp_partial_psi_inverse tau c (\<lambda>x. f x + g x) z"
proof -
  have modulation_add:
      "slp_oscillatory_modulation tau c (\<lambda>x. f x + g x) =
        (\<lambda>x. slp_oscillatory_modulation tau c f x +
          slp_oscillatory_modulation tau c g x)"
    by (rule ext)
      (simp add: slp_oscillatory_modulation_def algebra_simps)
  have additive:
      "slp_cauchy_transform SLP_Partial_Inverse
          (slp_oscillatory_modulation tau c f) z +
        slp_cauchy_transform SLP_Partial_Inverse
          (slp_oscillatory_modulation tau c g) z =
        slp_cauchy_transform SLP_Partial_Inverse
          (\<lambda>x. slp_oscillatory_modulation tau c f x +
            slp_oscillatory_modulation tau c g x) z"
    by (rule sym)
      (rule slp_cauchy_transform_add[OF f_integrable g_integrable])
  show ?thesis
    unfolding slp_partial_psi_inverse_def modulation_add
    by (rule additive)
qed

lemma slp_dbar_psi_inverse_add_at:
  fixes f g :: slp_scalar_field
  assumes f_integrable:
    "slp_cauchy_integrable_at SLP_Dbar_Inverse
      (slp_oscillatory_modulation (- tau) c f) z"
    and g_integrable:
    "slp_cauchy_integrable_at SLP_Dbar_Inverse
      (slp_oscillatory_modulation (- tau) c g) z"
  shows
    "slp_dbar_psi_inverse tau c f z +
        slp_dbar_psi_inverse tau c g z =
      slp_dbar_psi_inverse tau c (\<lambda>x. f x + g x) z"
proof -
  have modulation_add:
      "slp_oscillatory_modulation (- tau) c (\<lambda>x. f x + g x) =
        (\<lambda>x. slp_oscillatory_modulation (- tau) c f x +
          slp_oscillatory_modulation (- tau) c g x)"
    by (rule ext)
      (simp add: slp_oscillatory_modulation_def algebra_simps)
  have additive:
      "slp_cauchy_transform SLP_Dbar_Inverse
          (slp_oscillatory_modulation (- tau) c f) z +
        slp_cauchy_transform SLP_Dbar_Inverse
          (slp_oscillatory_modulation (- tau) c g) z =
        slp_cauchy_transform SLP_Dbar_Inverse
          (\<lambda>x. slp_oscillatory_modulation (- tau) c f x +
            slp_oscillatory_modulation (- tau) c g x) z"
    by (rule sym)
      (rule slp_cauchy_transform_add[OF f_integrable g_integrable])
  show ?thesis
    unfolding slp_dbar_psi_inverse_def modulation_add
    by (rule additive)
qed

section \<open>Exact affine Neumann terms as one conjugated source\<close>

theorem slp_both_neumann_affine_terms_eq_conjugated_source:
  fixes cutoff coefficient W :: slp_scalar_field
  assumes left_base_integrable:
    "\<And>z. slp_cauchy_integrable_at SLP_Partial_Inverse
      (slp_oscillatory_modulation tau c
        (\<lambda>x. cutoff x *
          (slp_dbar_inverse coefficient x -
            slp_dbar_inverse coefficient c))) z"
    and left_step_integrable:
    "\<And>z. slp_cauchy_integrable_at SLP_Partial_Inverse
      (slp_oscillatory_modulation tau c
        (\<lambda>x. cutoff x *
          slp_dbar_psi_inverse tau c
            (\<lambda>y. coefficient y * W y) x)) z"
    and right_base_integrable:
    "\<And>z. slp_cauchy_integrable_at SLP_Dbar_Inverse
      (slp_oscillatory_modulation (- (- tau)) c
        (\<lambda>x. cutoff x *
          (slp_partial_inverse coefficient x -
            slp_partial_inverse coefficient c))) z"
    and right_step_integrable:
    "\<And>z. slp_cauchy_integrable_at SLP_Dbar_Inverse
      (slp_oscillatory_modulation (- (- tau)) c
        (\<lambda>x. cutoff x *
          slp_partial_psi_inverse (- tau) c
            (\<lambda>y. coefficient y * W y) x)) z"
  shows
    "(\<lambda>z.
        slp_left_neumann_base tau c cutoff coefficient
            SLP_Dbar_Inverse z +
          slp_left_neumann_step tau c cutoff coefficient W z) =
      slp_partial_psi_inverse tau c
        (\<lambda>x. cutoff x *
          slp_left_conjugated_cauchy_source tau c coefficient
            (\<lambda>y. coefficient y * W y) x)
    \<and>
    (\<lambda>z.
        slp_right_neumann_base tau c cutoff coefficient
            SLP_Partial_Inverse z +
          slp_right_neumann_step tau c cutoff coefficient W z) =
      slp_dbar_psi_inverse (- tau) c
        (\<lambda>x. cutoff x *
          slp_right_conjugated_cauchy_source tau c coefficient
            (\<lambda>y. coefficient y * W y) x)"
proof
  show
    "(\<lambda>z.
        slp_left_neumann_base tau c cutoff coefficient
            SLP_Dbar_Inverse z +
          slp_left_neumann_step tau c cutoff coefficient W z) =
      slp_partial_psi_inverse tau c
        (\<lambda>x. cutoff x *
          slp_left_conjugated_cauchy_source tau c coefficient
            (\<lambda>y. coefficient y * W y) x)"
  proof (rule ext)
    fix z
    have additive:
        "slp_partial_psi_inverse tau c
            (\<lambda>x. cutoff x *
              (slp_dbar_inverse coefficient x -
                slp_dbar_inverse coefficient c)) z +
          slp_partial_psi_inverse tau c
            (\<lambda>x. cutoff x *
              slp_dbar_psi_inverse tau c
                (\<lambda>y. coefficient y * W y) x) z =
          slp_partial_psi_inverse tau c
            (\<lambda>x.
              cutoff x *
                (slp_dbar_inverse coefficient x -
                  slp_dbar_inverse coefficient c) +
              cutoff x *
                slp_dbar_psi_inverse tau c
                  (\<lambda>y. coefficient y * W y) x) z"
      by (rule slp_partial_psi_inverse_add_at[
            OF left_base_integrable left_step_integrable])
    show
      "slp_left_neumann_base tau c cutoff coefficient
            SLP_Dbar_Inverse z +
          slp_left_neumann_step tau c cutoff coefficient W z =
        slp_partial_psi_inverse tau c
          (\<lambda>x. cutoff x *
            slp_left_conjugated_cauchy_source tau c coefficient
              (\<lambda>y. coefficient y * W y) x) z"
      using additive
      unfolding slp_left_neumann_base_def slp_left_neumann_step_def
        slp_left_conjugated_cauchy_source_def
      by (simp only: algebra_simps)
  qed
next
  show
    "(\<lambda>z.
        slp_right_neumann_base tau c cutoff coefficient
            SLP_Partial_Inverse z +
          slp_right_neumann_step tau c cutoff coefficient W z) =
      slp_dbar_psi_inverse (- tau) c
        (\<lambda>x. cutoff x *
          slp_right_conjugated_cauchy_source tau c coefficient
            (\<lambda>y. coefficient y * W y) x)"
  proof (rule ext)
    fix z
    have additive:
        "slp_dbar_psi_inverse (- tau) c
            (\<lambda>x. cutoff x *
              (slp_partial_inverse coefficient x -
                slp_partial_inverse coefficient c)) z +
          slp_dbar_psi_inverse (- tau) c
            (\<lambda>x. cutoff x *
              slp_partial_psi_inverse (- tau) c
                (\<lambda>y. coefficient y * W y) x) z =
          slp_dbar_psi_inverse (- tau) c
            (\<lambda>x.
              cutoff x *
                (slp_partial_inverse coefficient x -
                  slp_partial_inverse coefficient c) +
              cutoff x *
                slp_partial_psi_inverse (- tau) c
                  (\<lambda>y. coefficient y * W y) x) z"
      by (rule slp_dbar_psi_inverse_add_at[
            OF right_base_integrable right_step_integrable])
    show
      "slp_right_neumann_base tau c cutoff coefficient
            SLP_Partial_Inverse z +
          slp_right_neumann_step tau c cutoff coefficient W z =
        slp_dbar_psi_inverse (- tau) c
          (\<lambda>x. cutoff x *
            slp_right_conjugated_cauchy_source tau c coefficient
              (\<lambda>y. coefficient y * W y) x) z"
      using additive
      unfolding slp_right_neumann_base_def slp_right_neumann_step_def
        slp_right_conjugated_cauchy_source_def
      by (simp only: algebra_simps)
  qed
qed

end
