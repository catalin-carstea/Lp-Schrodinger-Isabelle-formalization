theory Inverse_Schrodinger_Lp_CGO_Smooth_Weak_Solution
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_CGO_Second_Weak_Wirtinger"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_Weak_Wirtinger_Energy"
begin

section \<open>Restriction of project weak gradients and H1 pairs\<close>

lemma slp_weak_gradient_on_subset:
  assumes weak: "slp_weak_gradient_on X u Du"
    and Omega_subset: "Omega \<subseteq> X"
  shows "slp_weak_gradient_on Omega u Du"
  unfolding slp_weak_gradient_on_def
proof (intro allI impI)
  fix phi i
  assume phi_test: "slp_test_function_on Omega phi"
  let ?dphi = "slp_complex_partial_derivative phi i"
  let ?left = "\<lambda>x. u x * ?dphi x"
  let ?right = "\<lambda>x. Du x $ i * phi x"

  have phi_test_X: "slp_test_function_on X phi"
    using phi_test Omega_subset
    unfolding slp_test_function_on_def by blast
  have source:
      "set_integrable lborel X ?left \<and>
        set_integrable lborel X ?right \<and>
        set_lebesgue_integral lborel X ?left =
          - set_lebesgue_integral lborel X ?right"
    using weak phi_test_X
    unfolding slp_weak_gradient_on_def by blast

  have phi_restriction_Omega: "slp_restrict_field Omega phi = phi"
    by (rule slp_test_function_restrict_field_eq[OF phi_test])
  have phi_restriction_X: "slp_restrict_field X phi = phi"
    by (rule slp_test_function_restrict_field_eq[OF phi_test_X])
  have derivative_restriction_Omega:
      "slp_restrict_field Omega ?dphi = ?dphi"
    by (rule slp_test_function_partial_restrict_field_eq[OF phi_test])
  have derivative_restriction_X:
      "slp_restrict_field X ?dphi = ?dphi"
    by (rule slp_test_function_partial_restrict_field_eq[OF phi_test_X])

  have left_indicator_Omega:
      "(\<lambda>x. indicator Omega x *\<^sub>R ?left x) = ?left"
  proof (rule ext)
    fix x
    have derivative_point:
        "slp_restrict_field Omega ?dphi x = ?dphi x"
      using fun_cong[OF derivative_restriction_Omega, of x] .
    show "indicator Omega x *\<^sub>R ?left x = ?left x"
      using derivative_point
      by (cases "x \<in> Omega")
         (simp_all add: indicator_def slp_restrict_field_def)
  qed
  have left_indicator_X:
      "(\<lambda>x. indicator X x *\<^sub>R ?left x) = ?left"
  proof (rule ext)
    fix x
    have derivative_point: "slp_restrict_field X ?dphi x = ?dphi x"
      using fun_cong[OF derivative_restriction_X, of x] .
    show "indicator X x *\<^sub>R ?left x = ?left x"
      using derivative_point
      by (cases "x \<in> X")
         (simp_all add: indicator_def slp_restrict_field_def)
  qed
  have right_indicator_Omega:
      "(\<lambda>x. indicator Omega x *\<^sub>R ?right x) = ?right"
  proof (rule ext)
    fix x
    have phi_point: "slp_restrict_field Omega phi x = phi x"
      using fun_cong[OF phi_restriction_Omega, of x] .
    show "indicator Omega x *\<^sub>R ?right x = ?right x"
      using phi_point
      by (cases "x \<in> Omega")
         (simp_all add: indicator_def slp_restrict_field_def)
  qed
  have right_indicator_X:
      "(\<lambda>x. indicator X x *\<^sub>R ?right x) = ?right"
  proof (rule ext)
    fix x
    have phi_point: "slp_restrict_field X phi x = phi x"
      using fun_cong[OF phi_restriction_X, of x] .
    show "indicator X x *\<^sub>R ?right x = ?right x"
      using phi_point
      by (cases "x \<in> X")
         (simp_all add: indicator_def slp_restrict_field_def)
  qed

  have local_left: "set_integrable lborel Omega ?left"
    using source unfolding set_integrable_def
    by (simp only: left_indicator_Omega left_indicator_X)
  have local_right: "set_integrable lborel Omega ?right"
    using source unfolding set_integrable_def
    by (simp only: right_indicator_Omega right_indicator_X)
  have left_integral:
      "set_lebesgue_integral lborel Omega ?left =
        set_lebesgue_integral lborel X ?left"
    unfolding set_lebesgue_integral_def
    by (simp only: left_indicator_Omega left_indicator_X)
  have right_integral:
      "set_lebesgue_integral lborel Omega ?right =
        set_lebesgue_integral lborel X ?right"
    unfolding set_lebesgue_integral_def
    by (simp only: right_indicator_Omega right_indicator_X)
  show "set_integrable lborel Omega ?left \<and>
      set_integrable lborel Omega ?right \<and>
      set_lebesgue_integral lborel Omega ?left =
        - set_lebesgue_integral lborel Omega ?right"
  proof (intro conjI)
    show "set_integrable lborel Omega ?left"
      by (rule local_left)
    show "set_integrable lborel Omega ?right"
      by (rule local_right)
    show "set_lebesgue_integral lborel Omega ?left =
        - set_lebesgue_integral lborel Omega ?right"
      using source left_integral right_integral by simp
  qed
qed

lemma slp_h1_pair_on_subset:
  assumes Omega_measurable:
      "Omega \<in> sets (lborel :: slp_point measure)"
    and Omega_subset: "Omega \<subseteq> X"
    and pair: "slp_h1_pair_on X u Du"
  shows "slp_h1_pair_on Omega u Du"
proof -
  have u_measurable_X:
      "u \<in> borel_measurable (restrict_space lborel X)"
    using pair unfolding slp_h1_pair_on_def by blast
  have Du_measurable_X:
      "Du \<in> borel_measurable (restrict_space lborel X)"
    using pair unfolding slp_h1_pair_on_def by blast
  have u_measurable_Omega:
      "u \<in> borel_measurable (restrict_space lborel Omega)"
    by (rule measurable_restrict_mono[OF u_measurable_X Omega_subset])
  have Du_measurable_Omega:
      "Du \<in> borel_measurable (restrict_space lborel Omega)"
    by (rule measurable_restrict_mono[OF Du_measurable_X Omega_subset])
  have weak_X: "slp_weak_gradient_on X u Du"
    using pair unfolding slp_h1_pair_on_def by blast
  have weak_Omega: "slp_weak_gradient_on Omega u Du"
    by (rule slp_weak_gradient_on_subset[OF weak_X Omega_subset])
  have value_integrable_X:
      "set_integrable lborel X (\<lambda>x. norm (u x) ^ 2)"
    using pair unfolding slp_h1_pair_on_def by blast
  have gradient_integrable_X:
      "set_integrable lborel X (\<lambda>x. norm (Du x) ^ 2)"
    using pair unfolding slp_h1_pair_on_def by blast
  have value_integrable_Omega:
      "set_integrable lborel Omega (\<lambda>x. norm (u x) ^ 2)"
    by (rule set_integrable_subset[OF
          value_integrable_X Omega_measurable Omega_subset])
  have gradient_integrable_Omega:
      "set_integrable lborel Omega (\<lambda>x. norm (Du x) ^ 2)"
    by (rule set_integrable_subset[OF
          gradient_integrable_X Omega_measurable Omega_subset])
  show ?thesis
    unfolding slp_h1_pair_on_def
    using u_measurable_Omega Du_measurable_Omega weak_Omega
      value_integrable_Omega gradient_integrable_Omega by blast
qed

section \<open>Literal CGO fields satisfy the smooth-test weak equation\<close>

context slp_cauchy_outer_fixed_point
begin

theorem slp_both_affine_fixed_point_cgo_fields_smooth_weak_solution:
  fixes p M_left M_right tau :: real
    and c :: slp_point
    and X Omega :: "slp_point set"
    and cutoff q V W_left W_right :: slp_scalar_field
  assumes exponent_lower: "1 < p"
    and exponent_upper: "p < 2"
    and X_open: "open X"
    and X_bounded: "bounded X"
    and Omega_measurable:
      "Omega \<in> sets (lborel :: slp_point measure)"
    and Omega_bounded: "bounded Omega"
    and Omega_subset: "Omega \<subseteq> X"
    and cutoff_test: "slp_test_function_on X cutoff"
    and cutoff_one: "\<And>z. z \<in> Omega \<Longrightarrow> cutoff z = 1"
    and q_lp: "aim_complex_lp_on_plane p q"
    and q_support: "{x. q x \<noteq> 0} \<subseteq> X"
    and q_normalization: "q = (\<lambda>z. V z / 4)"
    and left_admissible:
      "slp_ae_bounded_measurable lborel M_left W_left"
    and right_admissible:
      "slp_ae_bounded_measurable lborel M_right W_right"
    and left_fixed:
      "AE z in lborel.
        W_left z =
          slp_restrict_field X
            (slp_left_neumann_base tau c cutoff q SLP_Dbar_Inverse) z +
          slp_restrict_field X
            (slp_left_neumann_step tau c cutoff q W_left) z"
    and right_fixed:
      "AE z in lborel.
        W_right z =
          slp_restrict_field X
            (slp_right_neumann_base tau c cutoff q SLP_Partial_Inverse) z +
          slp_restrict_field X
            (slp_right_neumann_step tau c cutoff q W_right) z"
  shows
    "(slp_h1_data_on Omega
        (slp_left_cgo_field tau c W_left,
          slp_left_cgo_gradient tau c W_left
            (slp_left_outer_conjugated_gradient tau c cutoff q W_left))
      \<and>
      (\<forall>phi. slp_test_function_on Omega phi \<longrightarrow>
        slp_weak_form_integrable Omega V
          (slp_left_cgo_field tau c W_left,
            slp_left_cgo_gradient tau c W_left
              (slp_left_outer_conjugated_gradient tau c cutoff q W_left))
          (phi, slp_classical_gradient phi)
        \<and>
        slp_weak_form Omega V
          (slp_left_cgo_field tau c W_left,
            slp_left_cgo_gradient tau c W_left
              (slp_left_outer_conjugated_gradient tau c cutoff q W_left))
          (phi, slp_classical_gradient phi) = 0))
    \<and>
    (slp_h1_data_on Omega
        (slp_right_cgo_field tau c W_right,
          slp_right_cgo_gradient tau c W_right
            (slp_right_outer_conjugated_gradient tau c cutoff q W_right))
      \<and>
      (\<forall>phi. slp_test_function_on Omega phi \<longrightarrow>
        slp_weak_form_integrable Omega V
          (slp_right_cgo_field tau c W_right,
            slp_right_cgo_gradient tau c W_right
              (slp_right_outer_conjugated_gradient tau c cutoff q W_right))
          (phi, slp_classical_gradient phi)
        \<and>
        slp_weak_form Omega V
          (slp_right_cgo_field tau c W_right,
            slp_right_cgo_gradient tau c W_right
              (slp_right_outer_conjugated_gradient tau c cutoff q W_right))
          (phi, slp_classical_gradient phi) = 0))"
proof -
  let ?uL = "slp_left_cgo_field tau c W_left"
  let ?DuL = "slp_left_cgo_gradient tau c W_left
    (slp_left_outer_conjugated_gradient tau c cutoff q W_left)"
  let ?DpartialL =
    "slp_left_cgo_partial_second_gradient tau c q W_left"
  let ?uR = "slp_right_cgo_field tau c W_right"
  let ?DuR = "slp_right_cgo_gradient tau c W_right
    (slp_right_outer_conjugated_gradient tau c cutoff q W_right)"
  let ?DdbarR = "slp_right_cgo_dbar_second_gradient tau c q W_right"

  note h1_X = slp_both_affine_fixed_point_cgo_fields_h1[OF
    exponent_lower exponent_upper X_open X_bounded cutoff_test q_lp q_support
    left_admissible right_admissible left_fixed right_fixed]
  have left_h1_X: "slp_h1_pair_on X ?uL ?DuL"
    using h1_X by blast
  have right_h1_X: "slp_h1_pair_on X ?uR ?DuR"
    using h1_X by blast
  have left_h1: "slp_h1_pair_on Omega ?uL ?DuL"
    by (rule slp_h1_pair_on_subset[OF
          Omega_measurable Omega_subset left_h1_X])
  have right_h1: "slp_h1_pair_on Omega ?uR ?DuR"
    by (rule slp_h1_pair_on_subset[OF
          Omega_measurable Omega_subset right_h1_X])
  have left_weak: "slp_weak_gradient_on Omega ?uL ?DuL"
    using left_h1 unfolding slp_h1_pair_on_def by blast
  have right_weak: "slp_weak_gradient_on Omega ?uR ?DuR"
    using right_h1 unfolding slp_h1_pair_on_def by blast

  note left_second =
    slp_both_cgo_projection_second_weak_wirtinger_on_cutoff_one[OF
      exponent_lower exponent_upper X_open X_bounded cutoff_test q_lp q_support
      left_admissible Omega_measurable Omega_bounded cutoff_one]
  have left_projected_weak:
      "slp_weak_gradient_on Omega
        (slp_gradient_wirtinger_partial ?DuL) ?DpartialL"
    using left_second by blast
  have left_projection:
      "slp_gradient_wirtinger_dbar ?DpartialL =
        (\<lambda>z. q z * ?uL z)"
    using left_second by blast

  note right_second =
    slp_both_cgo_projection_second_weak_wirtinger_on_cutoff_one[OF
      exponent_lower exponent_upper X_open X_bounded cutoff_test q_lp q_support
      right_admissible Omega_measurable Omega_bounded cutoff_one]
  have right_projected_weak:
      "slp_weak_gradient_on Omega
        (slp_gradient_wirtinger_dbar ?DuR) ?DdbarR"
    using right_second by blast
  have right_projection:
      "slp_gradient_wirtinger_partial ?DdbarR =
        (\<lambda>z. q z * ?uR z)"
    using right_second by blast

  have left_tests:
      "\<forall>phi. slp_test_function_on Omega phi \<longrightarrow>
        slp_weak_form_integrable Omega V
          (?uL, ?DuL) (phi, slp_classical_gradient phi) \<and>
        slp_weak_form Omega V
          (?uL, ?DuL) (phi, slp_classical_gradient phi) = 0"
  proof (intro allI impI)
    fix phi
    assume phi_test: "slp_test_function_on Omega phi"
    note energy = slp_weak_partial_dbar_smooth_test_energy[OF
      left_weak left_projected_weak phi_test]
    have energy_integrable:
        "set_integrable lborel Omega
          (\<lambda>x. \<Sum>i\<in>UNIV.
            ?DuL x $ i * slp_classical_gradient phi x $ i)"
      using energy by blast
    have source_integrable:
        "set_integrable lborel Omega (\<lambda>x. q x * ?uL x * phi x)"
      using energy unfolding left_projection by blast
    have energy_integral:
        "set_lebesgue_integral lborel Omega
            (\<lambda>x. \<Sum>i\<in>UNIV.
              ?DuL x $ i * slp_classical_gradient phi x $ i) =
          - 4 * set_lebesgue_integral lborel Omega
            (\<lambda>x. q x * ?uL x * phi x)"
      using energy unfolding left_projection by blast
    have potential_function:
        "(\<lambda>x. V x * ?uL x * phi x) =
          (\<lambda>x. (q x * ?uL x * phi x) * (4::complex))"
      by (rule ext) (simp add: q_normalization algebra_simps)
    have potential_integrable:
        "set_integrable lborel Omega (\<lambda>x. V x * ?uL x * phi x)"
      using source_integrable unfolding potential_function by simp
    have potential_integral:
        "set_lebesgue_integral lborel Omega
            (\<lambda>x. V x * ?uL x * phi x) =
          4 * set_lebesgue_integral lborel Omega
            (\<lambda>x. q x * ?uL x * phi x)"
      unfolding potential_function by (simp add: mult.commute)
    show "slp_weak_form_integrable Omega V
          (?uL, ?DuL) (phi, slp_classical_gradient phi) \<and>
        slp_weak_form Omega V
          (?uL, ?DuL) (phi, slp_classical_gradient phi) = 0"
      unfolding slp_weak_form_integrable_def slp_weak_form_def
      using energy_integrable potential_integrable energy_integral
        potential_integral by simp
  qed

  have right_tests:
      "\<forall>phi. slp_test_function_on Omega phi \<longrightarrow>
        slp_weak_form_integrable Omega V
          (?uR, ?DuR) (phi, slp_classical_gradient phi) \<and>
        slp_weak_form Omega V
          (?uR, ?DuR) (phi, slp_classical_gradient phi) = 0"
  proof (intro allI impI)
    fix phi
    assume phi_test: "slp_test_function_on Omega phi"
    note energy = slp_weak_dbar_partial_smooth_test_energy[OF
      right_weak right_projected_weak phi_test]
    have energy_integrable:
        "set_integrable lborel Omega
          (\<lambda>x. \<Sum>i\<in>UNIV.
            ?DuR x $ i * slp_classical_gradient phi x $ i)"
      using energy by blast
    have source_integrable:
        "set_integrable lborel Omega (\<lambda>x. q x * ?uR x * phi x)"
      using energy unfolding right_projection by blast
    have energy_integral:
        "set_lebesgue_integral lborel Omega
            (\<lambda>x. \<Sum>i\<in>UNIV.
              ?DuR x $ i * slp_classical_gradient phi x $ i) =
          - 4 * set_lebesgue_integral lborel Omega
            (\<lambda>x. q x * ?uR x * phi x)"
      using energy unfolding right_projection by blast
    have potential_function:
        "(\<lambda>x. V x * ?uR x * phi x) =
          (\<lambda>x. (q x * ?uR x * phi x) * (4::complex))"
      by (rule ext) (simp add: q_normalization algebra_simps)
    have potential_integrable:
        "set_integrable lborel Omega (\<lambda>x. V x * ?uR x * phi x)"
      using source_integrable unfolding potential_function by simp
    have potential_integral:
        "set_lebesgue_integral lborel Omega
            (\<lambda>x. V x * ?uR x * phi x) =
          4 * set_lebesgue_integral lborel Omega
            (\<lambda>x. q x * ?uR x * phi x)"
      unfolding potential_function by (simp add: mult.commute)
    show "slp_weak_form_integrable Omega V
          (?uR, ?DuR) (phi, slp_classical_gradient phi) \<and>
        slp_weak_form Omega V
          (?uR, ?DuR) (phi, slp_classical_gradient phi) = 0"
      unfolding slp_weak_form_integrable_def slp_weak_form_def
      using energy_integrable potential_integrable energy_integral
        potential_integral by simp
  qed

  show ?thesis
    using left_h1 right_h1 left_tests right_tests
    unfolding slp_h1_data_on_def
    by (simp only: fst_conv snd_conv)
qed

end

end
