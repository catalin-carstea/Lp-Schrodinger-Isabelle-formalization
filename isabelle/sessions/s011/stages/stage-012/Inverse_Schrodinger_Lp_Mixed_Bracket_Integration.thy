theory Inverse_Schrodinger_Lp_Mixed_Bracket_Integration
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Mixed_Weighted_Integrability"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Integrating the literal five-term mixed bracket\<close>

theorem slp_mixed_finite_bracket_measurable:
  fixes left_type :: "'i::finite itself" and right_type :: "'j::finite itself"
    and tau :: real
    and Q left_cutoff q A right_cutoff qt B phi :: slp_scalar_field
  assumes Q_measurable: "Q \<in> borel_measurable lborel"
    and left_cutoff_measurable: "left_cutoff \<in> borel_measurable lborel"
    and q_measurable: "q \<in> borel_measurable lborel"
    and A_measurable: "A \<in> borel_measurable lborel"
    and right_cutoff_measurable: "right_cutoff \<in> borel_measurable lborel"
    and qt_measurable: "qt \<in> borel_measurable lborel"
    and B_measurable: "B \<in> borel_measurable lborel"
    and phi_integrable: "integrable lborel phi"
    and phi_B_integrable: "integrable lborel (\<lambda>x. phi x * B x)"
    and phi_A_integrable: "integrable lborel (\<lambda>x. phi x * A x)"
    and phi_AB_integrable: "integrable lborel (\<lambda>x. phi x * (A x * B x))"
  shows joint:
    "case_prod (slp_mixed_center_finite_bracket_integrand tau
      Q left_cutoff q A right_cutoff qt B phi ::
      slp_point \<Rightarrow>
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)
      \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    and kernel:
    "slp_mixed_center_finite_bracket_kernel TYPE('i) TYPE('j) tau
      Q left_cutoff q A right_cutoff qt B phi \<in> borel_measurable lborel"
proof -
  let ?bracket = "slp_mixed_center_finite_bracket_integrand tau
    Q left_cutoff q A right_cutoff qt B phi ::
    slp_point \<Rightarrow>
      ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex"
  let ?W = "\<lambda>T U H. slp_mixed_center_finite_weighted_oscillatory_integrand
    tau Q left_cutoff q T right_cutoff qt U H ::
    slp_point \<Rightarrow>
      ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex"
  let ?E0 = "slp_center_average tau phi"
  let ?EB = "slp_center_average tau (\<lambda>x. phi x * B x)"
  let ?EA = "slp_center_average tau (\<lambda>x. phi x * A x)"
  let ?EAB = "slp_center_average tau (\<lambda>x. phi x * (A x * B x))"
  have E0_measurable: "?E0 \<in> borel_measurable lborel"
    by (rule slp_center_average_measurable[OF phi_integrable])
  have EB_measurable: "?EB \<in> borel_measurable lborel"
    by (rule slp_center_average_measurable[OF phi_B_integrable])
  have EA_measurable: "?EA \<in> borel_measurable lborel"
    by (rule slp_center_average_measurable[OF phi_A_integrable])
  have EAB_measurable: "?EAB \<in> borel_measurable lborel"
    by (rule slp_center_average_measurable[OF phi_AB_integrable])
  have unit_measurable: "(\<lambda>_::slp_point. (1::complex)) \<in> borel_measurable lborel"
    by measurable
  have weighted_measurable:
    "case_prod (?W T U H) \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    if T_measurable: "T \<in> borel_measurable lborel"
      and U_measurable: "U \<in> borel_measurable lborel"
      and H_measurable: "H \<in> borel_measurable lborel"
    for T U H
    by (rule slp_mixed_center_finite_weighted_oscillatory_integrand_joint_measurable[OF
        Q_measurable left_cutoff_measurable q_measurable T_measurable
        right_cutoff_measurable qt_measurable U_measurable H_measurable])
  have expansion:
    "case_prod ?bracket =
      (\<lambda>z. case_prod (?W A B ?E0) z -
        case_prod (?W A (\<lambda>_. 1) ?EB) z -
        case_prod (?W (\<lambda>_. 1) B ?EA) z +
        case_prod (?W (\<lambda>_. 1) (\<lambda>_. 1) ?EAB) z)"
    by (rule ext)
      (simp add: split_beta' slp_mixed_center_finite_bracket_integrand_def
        slp_mixed_center_average_bracket_def
        slp_mixed_weighted_integrand_terminal_factor algebra_simps)
  have bracket_measurable:
    "case_prod ?bracket \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    unfolding expansion
    using weighted_measurable[OF A_measurable B_measurable E0_measurable]
      weighted_measurable[OF A_measurable unit_measurable EB_measurable]
      weighted_measurable[OF unit_measurable B_measurable EA_measurable]
      weighted_measurable[OF unit_measurable unit_measurable EAB_measurable]
    by measurable
  show "case_prod ?bracket \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule bracket_measurable)
  have kernel_function:
    "slp_mixed_center_finite_bracket_kernel TYPE('i) TYPE('j) tau
      Q left_cutoff q A right_cutoff qt B phi =
      (\<lambda>center. integral\<^sup>L lborel (?bracket center))"
    by (rule ext) (simp only: slp_mixed_center_finite_bracket_kernel_def)
  show "slp_mixed_center_finite_bracket_kernel TYPE('i) TYPE('j) tau
      Q left_cutoff q A right_cutoff qt B phi \<in> borel_measurable lborel"
    unfolding kernel_function
    by (rule lborel.borel_measurable_lebesgue_integral[OF bracket_measurable])
qed

theorem slp_mixed_finite_bracket_kernel_expansion:
  fixes left_type :: "'i::finite itself" and right_type :: "'j::finite itself"
    and tau :: real and center :: slp_point
    and Q left_cutoff q A right_cutoff qt B phi :: slp_scalar_field
  assumes fiber_principal:
    "integrable lborel (slp_mixed_center_finite_weighted_oscillatory_integrand tau
      Q left_cutoff q (\<lambda>x. A x - A center)
      right_cutoff qt (\<lambda>x. B x - B center) phi center ::
      ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    and fiber_smooth:
    "integrable lborel (slp_mixed_center_finite_weighted_oscillatory_integrand tau
      Q left_cutoff q A right_cutoff qt B
      (\<lambda>x. slp_center_average tau phi x - phi x) center ::
      ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    and fiber_left:
    "integrable lborel (slp_mixed_center_finite_weighted_oscillatory_integrand tau
      Q left_cutoff q A right_cutoff qt (\<lambda>_. 1)
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * B z) x -
        phi x * B x) center ::
      ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    and fiber_right:
    "integrable lborel (slp_mixed_center_finite_weighted_oscillatory_integrand tau
      Q left_cutoff q (\<lambda>_. 1) right_cutoff qt B
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * A z) x -
        phi x * A x) center ::
      ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    and fiber_product:
    "integrable lborel (slp_mixed_center_finite_weighted_oscillatory_integrand tau
      Q left_cutoff q (\<lambda>_. 1) right_cutoff qt (\<lambda>_. 1)
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * (A z * B z)) x -
        phi x * (A x * B x)) center ::
      ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
  shows integrability:
    "integrable lborel (slp_mixed_center_finite_bracket_integrand tau
      Q left_cutoff q A right_cutoff qt B phi center ::
      ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    and expansion:
    "slp_mixed_center_finite_bracket_kernel TYPE('i) TYPE('j) tau
      Q left_cutoff q A right_cutoff qt B phi center =
    slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_kernel
      TYPE('i) TYPE('j) tau Q left_cutoff q A right_cutoff qt B phi center
    + slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) tau
      Q left_cutoff q A right_cutoff qt B
      (\<lambda>x. slp_center_average tau phi x - phi x) center
    - slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) tau
      Q left_cutoff q A right_cutoff qt (\<lambda>_. 1)
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * B z) x -
        phi x * B x) center
    - slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) tau
      Q left_cutoff q (\<lambda>_. 1) right_cutoff qt B
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * A z) x -
        phi x * A x) center
    + slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) tau
      Q left_cutoff q (\<lambda>_. 1) right_cutoff qt (\<lambda>_. 1)
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * (A z * B z)) x -
        phi x * (A x * B x)) center"
proof -
  let ?F0 = "slp_mixed_center_finite_weighted_oscillatory_integrand tau
      Q left_cutoff q (\<lambda>x. A x - A center)
      right_cutoff qt (\<lambda>x. B x - B center) phi center ::
    ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex"
  let ?F1 = "slp_mixed_center_finite_weighted_oscillatory_integrand tau
      Q left_cutoff q A right_cutoff qt B
      (\<lambda>x. slp_center_average tau phi x - phi x) center ::
    ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex"
  let ?F2 = "slp_mixed_center_finite_weighted_oscillatory_integrand tau
      Q left_cutoff q A right_cutoff qt (\<lambda>_. 1)
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * B z) x -
        phi x * B x) center ::
    ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex"
  let ?F3 = "slp_mixed_center_finite_weighted_oscillatory_integrand tau
      Q left_cutoff q (\<lambda>_. 1) right_cutoff qt B
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * A z) x -
        phi x * A x) center ::
    ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex"
  let ?F4 = "slp_mixed_center_finite_weighted_oscillatory_integrand tau
      Q left_cutoff q (\<lambda>_. 1) right_cutoff qt (\<lambda>_. 1)
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * (A z * B z)) x -
        phi x * (A x * B x)) center ::
    ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex"
  have i01: "integrable lborel (\<lambda>x. ?F0 x + ?F1 x)"
    by (rule Bochner_Integration.integrable_add[OF fiber_principal fiber_smooth])
  have i012: "integrable lborel (\<lambda>x. ?F0 x + ?F1 x - ?F2 x)"
    by (rule Bochner_Integration.integrable_diff[OF i01 fiber_left])
  have i0123: "integrable lborel (\<lambda>x. ?F0 x + ?F1 x - ?F2 x - ?F3 x)"
    by (rule Bochner_Integration.integrable_diff[OF i012 fiber_right])
  have i01234:
    "integrable lborel (\<lambda>x. ?F0 x + ?F1 x - ?F2 x - ?F3 x + ?F4 x)"
    by (rule Bochner_Integration.integrable_add[OF i0123 fiber_product])
  have identity:
    "(slp_mixed_center_finite_bracket_integrand tau
      Q left_cutoff q A right_cutoff qt B phi center ::
      ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex) =
      (\<lambda>x. ?F0 x + ?F1 x - ?F2 x - ?F3 x + ?F4 x)"
    by (rule ext) (rule slp_mixed_finite_bracket_integrand_decomposition)
  show "integrable lborel
    (slp_mixed_center_finite_bracket_integrand tau
      Q left_cutoff q A right_cutoff qt B phi center ::
      ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    using i01234 by (simp only: identity)
  have integrated:
    "integral\<^sup>L lborel
      (slp_mixed_center_finite_bracket_integrand tau
        Q left_cutoff q A right_cutoff qt B phi center ::
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex) =
      integral\<^sup>L lborel ?F0 + integral\<^sup>L lborel ?F1 -
      integral\<^sup>L lborel ?F2 - integral\<^sup>L lborel ?F3 +
      integral\<^sup>L lborel ?F4"
    unfolding identity
    by (simp only: Bochner_Integration.integral_add[OF i0123 fiber_product]
        Bochner_Integration.integral_diff[OF i012 fiber_right]
        Bochner_Integration.integral_diff[OF i01 fiber_left]
        Bochner_Integration.integral_add[OF fiber_principal fiber_smooth])
  show "slp_mixed_center_finite_bracket_kernel TYPE('i) TYPE('j) tau
      Q left_cutoff q A right_cutoff qt B phi center =
    slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_kernel
      TYPE('i) TYPE('j) tau Q left_cutoff q A right_cutoff qt B phi center
    + slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) tau
      Q left_cutoff q A right_cutoff qt B
      (\<lambda>x. slp_center_average tau phi x - phi x) center
    - slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) tau
      Q left_cutoff q A right_cutoff qt (\<lambda>_. 1)
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * B z) x -
        phi x * B x) center
    - slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) tau
      Q left_cutoff q (\<lambda>_. 1) right_cutoff qt B
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * A z) x -
        phi x * A x) center
    + slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) tau
      Q left_cutoff q (\<lambda>_. 1) right_cutoff qt (\<lambda>_. 1)
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * (A z * B z)) x -
        phi x * (A x * B x)) center"
    unfolding slp_mixed_center_finite_bracket_kernel_def
      slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_kernel_def
      slp_mixed_center_finite_weighted_oscillatory_kernel_def
    by (rule integrated)
qed

theorem slp_mixed_finite_bracket_global_expansion:
  fixes left_type :: "'i::finite itself" and right_type :: "'j::finite itself"
    and tau :: real
    and Q left_cutoff q A right_cutoff qt B phi :: slp_scalar_field
  assumes kernel_measurable:
    "slp_mixed_center_finite_bracket_kernel TYPE('i) TYPE('j) tau
      Q left_cutoff q A right_cutoff qt B phi \<in> borel_measurable lborel"
    and fibers:
    "AE center in lborel.
      integrable lborel (slp_mixed_center_finite_weighted_oscillatory_integrand tau
      Q left_cutoff q (\<lambda>x. A x - A center)
      right_cutoff qt (\<lambda>x. B x - B center) phi center ::
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex) \<and>
      integrable lborel (slp_mixed_center_finite_weighted_oscillatory_integrand tau
      Q left_cutoff q A right_cutoff qt B
      (\<lambda>x. slp_center_average tau phi x - phi x) center ::
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex) \<and>
      integrable lborel (slp_mixed_center_finite_weighted_oscillatory_integrand tau
      Q left_cutoff q A right_cutoff qt (\<lambda>_. 1)
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * B z) x -
        phi x * B x) center ::
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex) \<and>
      integrable lborel (slp_mixed_center_finite_weighted_oscillatory_integrand tau
      Q left_cutoff q (\<lambda>_. 1) right_cutoff qt B
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * A z) x -
        phi x * A x) center ::
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex) \<and>
      integrable lborel (slp_mixed_center_finite_weighted_oscillatory_integrand tau
      Q left_cutoff q (\<lambda>_. 1) right_cutoff qt (\<lambda>_. 1)
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * (A z * B z)) x -
        phi x * (A x * B x)) center ::
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    and principal_center: "integrable lborel (slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_kernel
      TYPE('i) TYPE('j) tau Q left_cutoff q A right_cutoff qt B phi)"
    and smooth_center: "integrable lborel (slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) tau
      Q left_cutoff q A right_cutoff qt B
      (\<lambda>x. slp_center_average tau phi x - phi x))"
    and left_center: "integrable lborel (slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) tau
      Q left_cutoff q A right_cutoff qt (\<lambda>_. 1)
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * B z) x -
        phi x * B x))"
    and right_center: "integrable lborel (slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) tau
      Q left_cutoff q (\<lambda>_. 1) right_cutoff qt B
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * A z) x -
        phi x * A x))"
    and product_center: "integrable lborel (slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) tau
      Q left_cutoff q (\<lambda>_. 1) right_cutoff qt (\<lambda>_. 1)
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * (A z * B z)) x -
        phi x * (A x * B x)))"
  shows global_integrability: "integrable lborel (slp_mixed_center_finite_bracket_kernel TYPE('i) TYPE('j) tau
      Q left_cutoff q A right_cutoff qt B phi)"
    and global_expansion:
    "integral\<^sup>L lborel (slp_mixed_center_finite_bracket_kernel TYPE('i) TYPE('j) tau
      Q left_cutoff q A right_cutoff qt B phi) =
    integral\<^sup>L lborel (slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_kernel
      TYPE('i) TYPE('j) tau Q left_cutoff q A right_cutoff qt B phi)
    + integral\<^sup>L lborel (slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) tau
      Q left_cutoff q A right_cutoff qt B
      (\<lambda>x. slp_center_average tau phi x - phi x))
    - integral\<^sup>L lborel (slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) tau
      Q left_cutoff q A right_cutoff qt (\<lambda>_. 1)
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * B z) x -
        phi x * B x))
    - integral\<^sup>L lborel (slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) tau
      Q left_cutoff q (\<lambda>_. 1) right_cutoff qt B
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * A z) x -
        phi x * A x))
    + integral\<^sup>L lborel (slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) tau
      Q left_cutoff q (\<lambda>_. 1) right_cutoff qt (\<lambda>_. 1)
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * (A z * B z)) x -
        phi x * (A x * B x)))"
proof -
  let ?full_kernel = "slp_mixed_center_finite_bracket_kernel TYPE('i) TYPE('j) tau
      Q left_cutoff q A right_cutoff qt B phi"
  let ?K0 = "slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_kernel
      TYPE('i) TYPE('j) tau Q left_cutoff q A right_cutoff qt B phi"
  let ?K1 = "slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) tau
      Q left_cutoff q A right_cutoff qt B
      (\<lambda>x. slp_center_average tau phi x - phi x)"
  let ?K2 = "slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) tau
      Q left_cutoff q A right_cutoff qt (\<lambda>_. 1)
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * B z) x -
        phi x * B x)"
  let ?K3 = "slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) tau
      Q left_cutoff q (\<lambda>_. 1) right_cutoff qt B
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * A z) x -
        phi x * A x)"
  let ?K4 = "slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) tau
      Q left_cutoff q (\<lambda>_. 1) right_cutoff qt (\<lambda>_. 1)
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * (A z * B z)) x -
        phi x * (A x * B x))"
  let ?F0 = "(\<lambda>center. slp_mixed_center_finite_weighted_oscillatory_integrand tau
      Q left_cutoff q (\<lambda>x. A x - A center)
      right_cutoff qt (\<lambda>x. B x - B center) phi center ::
    ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
  let ?F1 = "(\<lambda>center. slp_mixed_center_finite_weighted_oscillatory_integrand tau
      Q left_cutoff q A right_cutoff qt B
      (\<lambda>x. slp_center_average tau phi x - phi x) center ::
    ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
  let ?F2 = "(\<lambda>center. slp_mixed_center_finite_weighted_oscillatory_integrand tau
      Q left_cutoff q A right_cutoff qt (\<lambda>_. 1)
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * B z) x -
        phi x * B x) center ::
    ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
  let ?F3 = "(\<lambda>center. slp_mixed_center_finite_weighted_oscillatory_integrand tau
      Q left_cutoff q (\<lambda>_. 1) right_cutoff qt B
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * A z) x -
        phi x * A x) center ::
    ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
  let ?F4 = "(\<lambda>center. slp_mixed_center_finite_weighted_oscillatory_integrand tau
      Q left_cutoff q (\<lambda>_. 1) right_cutoff qt (\<lambda>_. 1)
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * (A z * B z)) x -
        phi x * (A x * B x)) center ::
    ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
  let ?S = "\<lambda>center. ?K0 center + ?K1 center -
    ?K2 center - ?K3 center + ?K4 center"
  have i01: "integrable lborel (\<lambda>x. ?K0 x + ?K1 x)"
    by (rule Bochner_Integration.integrable_add[OF principal_center smooth_center])
  have i012: "integrable lborel (\<lambda>x. ?K0 x + ?K1 x - ?K2 x)"
    by (rule Bochner_Integration.integrable_diff[OF i01 left_center])
  have i0123: "integrable lborel (\<lambda>x. ?K0 x + ?K1 x - ?K2 x - ?K3 x)"
    by (rule Bochner_Integration.integrable_diff[OF i012 right_center])
  have sum_integrable: "integrable lborel ?S"
    by (rule Bochner_Integration.integrable_add[OF i0123 product_center])
  have ae_expansion: "AE center in lborel. ?full_kernel center = ?S center"
    using fibers
  proof eventually_elim
    fix center
    assume data:
      "integrable lborel (?F0 center) \<and>
       integrable lborel (?F1 center) \<and>
       integrable lborel (?F2 center) \<and>
       integrable lborel (?F3 center) \<and>
       integrable lborel (?F4 center)"
    have f0: "integrable lborel (?F0 center)"
      and f1: "integrable lborel (?F1 center)"
      and f2: "integrable lborel (?F2 center)"
      and f3: "integrable lborel (?F3 center)"
      and f4: "integrable lborel (?F4 center)"
      using data by blast+
    show "?full_kernel center = ?S center"
      by (rule slp_mixed_finite_bracket_kernel_expansion(2)[OF f0 f1 f2 f3 f4])
  qed
  show "integrable lborel ?full_kernel"
    by (rule integrable_cong_AE_imp[OF sum_integrable kernel_measurable])
      (use ae_expansion in eventually_elim; simp)
  have sum_measurable: "?S \<in> borel_measurable lborel"
    using sum_integrable by measurable
  have integral_equal: "integral\<^sup>L lborel ?full_kernel = integral\<^sup>L lborel ?S"
    by (rule integral_cong_AE[OF kernel_measurable sum_measurable ae_expansion])
  show "integral\<^sup>L lborel ?full_kernel =
    integral\<^sup>L lborel ?K0 + integral\<^sup>L lborel ?K1 -
    integral\<^sup>L lborel ?K2 - integral\<^sup>L lborel ?K3 +
    integral\<^sup>L lborel ?K4"
    using integral_equal
    by (simp only: Bochner_Integration.integral_add[OF i0123 product_center]
        Bochner_Integration.integral_diff[OF i012 right_center]
        Bochner_Integration.integral_diff[OF i01 left_center]
        Bochner_Integration.integral_add[OF principal_center smooth_center])
qed

end
