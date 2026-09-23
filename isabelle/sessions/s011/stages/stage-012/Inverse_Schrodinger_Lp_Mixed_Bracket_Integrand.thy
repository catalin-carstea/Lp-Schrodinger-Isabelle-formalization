theory Inverse_Schrodinger_Lp_Mixed_Bracket_Integrand
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Mixed_Weighted_Product_Error"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Mixed_Center_Average_Bracket_Algebra"
begin

hide_const (open) Commutative_Ring.norm

section \<open>The literal finite mixed-bracket integrand\<close>

lemma slp_left_branch_list_terminal_factor:
  fixes cutoff q A :: slp_scalar_field
  shows "slp_left_branch_complex_kernel_list cutoff q A pairs origin terminal =
    A terminal *
      slp_left_branch_complex_kernel_list cutoff q (\<lambda>_. 1)
        pairs origin terminal"
proof (induction pairs arbitrary: origin)
  case Nil
  show ?case
    by (simp add: slp_left_branch_complex_terminal_def algebra_simps)
next
  case (Cons pair pairs)
  show ?case
    by (simp only: slp_left_branch_complex_kernel_list.simps Cons.IH;
        simp add: algebra_simps)
qed

lemma slp_branch_joint_terminal_factors:
  fixes coordinates :: "'i::finite slp_left_branch_finite_coordinates"
    and cutoff q A :: slp_scalar_field
  shows left:
    "slp_left_branch_complex_kernel_joint cutoff q A coordinates =
      A (snd (snd coordinates)) *
        slp_left_branch_complex_kernel_joint cutoff q (\<lambda>_. 1) coordinates"
    and right:
    "slp_right_branch_complex_kernel_joint cutoff q A coordinates =
      A (snd (snd coordinates)) *
        slp_right_branch_complex_kernel_joint cutoff q (\<lambda>_. 1) coordinates"
proof -
  have left_factor:
    "slp_left_branch_complex_kernel_joint c v T coordinates =
      T (snd (snd coordinates)) *
        slp_left_branch_complex_kernel_joint c v (\<lambda>_. 1) coordinates"
    for c v T
    unfolding slp_left_branch_complex_kernel_joint_def
      slp_left_branch_complex_kernel_finite_def
    by (rule slp_left_branch_list_terminal_factor)
  show "slp_left_branch_complex_kernel_joint cutoff q A coordinates =
      A (snd (snd coordinates)) *
        slp_left_branch_complex_kernel_joint cutoff q (\<lambda>_. 1) coordinates"
    by (rule left_factor)
  note conjugated = left_factor[of "\<lambda>x. cnj (cutoff x)"
    "\<lambda>x. cnj (q x)" "\<lambda>x. cnj (A x)"]
  show "slp_right_branch_complex_kernel_joint cutoff q A coordinates =
      A (snd (snd coordinates)) *
        slp_right_branch_complex_kernel_joint cutoff q (\<lambda>_. 1) coordinates"
    unfolding slp_right_branch_complex_kernel_joint_def
    by (simp only: conjugated complex_cnj_mult complex_cnj_cnj complex_cnj_one)
qed

lemma slp_mixed_weighted_integrand_terminal_factor:
  fixes coordinates ::
      "('i::finite, 'j::finite) slp_mixed_center_finite_coordinates"
    and tau :: real and center :: slp_point
    and Q left_cutoff q A right_cutoff qt B H :: slp_scalar_field
  shows "slp_mixed_center_finite_weighted_oscillatory_integrand tau
      Q left_cutoff q A right_cutoff qt B H center coordinates =
    slp_parameterized_real_phase_integrand tau slp_mixed_center_finite_residual
      (slp_mixed_center_finite_complex_amplitude Q left_cutoff q right_cutoff qt)
      center coordinates *
      (A (snd (fst (snd coordinates))) *
        B (slp_mixed_center_finite_right_terminal center coordinates) * H center)"
proof -
  let ?left = "fst (slp_mixed_center_finite_inserted_coordinates
    center coordinates)"
  let ?right = "snd (slp_mixed_center_finite_inserted_coordinates
    center coordinates)"
  have left_factor:
    "slp_left_branch_complex_kernel_joint left_cutoff q A ?left =
      A (snd (snd ?left)) *
        slp_left_branch_complex_kernel_joint left_cutoff q (\<lambda>_. 1) ?left"
    by (rule slp_branch_joint_terminal_factors(1))
  have right_factor:
    "slp_right_branch_complex_kernel_joint right_cutoff qt B ?right =
      B (snd (snd ?right)) *
        slp_right_branch_complex_kernel_joint right_cutoff qt (\<lambda>_. 1) ?right"
    by (rule slp_branch_joint_terminal_factors(2))
  show ?thesis
    unfolding slp_mixed_center_finite_weighted_oscillatory_integrand_def
      slp_parameterized_real_phase_integrand_def
      slp_mixed_center_finite_weighted_complex_amplitude_def
      slp_mixed_center_finite_complex_amplitude_def
    apply (simp only: left_factor right_factor)
    by (simp add: slp_mixed_center_finite_inserted_coordinates_def algebra_simps)
qed

definition slp_mixed_center_finite_bracket_integrand ::
  "real \<Rightarrow> slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_point \<Rightarrow>
    ('i::finite, 'j::finite) slp_mixed_center_finite_coordinates \<Rightarrow> complex"
where
  "slp_mixed_center_finite_bracket_integrand tau Q left_cutoff q A
      right_cutoff qt B phi center coordinates =
    slp_parameterized_real_phase_integrand tau slp_mixed_center_finite_residual
      (slp_mixed_center_finite_complex_amplitude Q left_cutoff q right_cutoff qt)
      center coordinates *
      slp_mixed_center_average_bracket tau phi A B center
        (snd (fst (snd coordinates)))
        (slp_mixed_center_finite_right_terminal center coordinates)"

definition slp_mixed_center_finite_bracket_kernel ::
  "'i::finite itself \<Rightarrow> 'j::finite itself \<Rightarrow> real \<Rightarrow>
    slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow> slp_point \<Rightarrow> complex"
where
  "slp_mixed_center_finite_bracket_kernel TYPE('i) TYPE('j) tau
      Q left_cutoff q A right_cutoff qt B phi center =
    integral\<^sup>L lborel
      (slp_mixed_center_finite_bracket_integrand tau Q left_cutoff q A
        right_cutoff qt B phi center ::
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"

theorem slp_mixed_finite_bracket_integrand_decomposition:
  fixes coordinates ::
      "('i::finite, 'j::finite) slp_mixed_center_finite_coordinates"
    and tau :: real and center :: slp_point
    and Q left_cutoff q A right_cutoff qt B phi :: slp_scalar_field
  shows "slp_mixed_center_finite_bracket_integrand tau Q left_cutoff q A
      right_cutoff qt B phi center coordinates =
    slp_mixed_center_finite_weighted_oscillatory_integrand tau
      Q left_cutoff q (\<lambda>x. A x - A center)
      right_cutoff qt (\<lambda>x. B x - B center) phi center coordinates +
    slp_mixed_center_finite_weighted_oscillatory_integrand tau
      Q left_cutoff q A right_cutoff qt B
      (\<lambda>x. slp_center_average tau phi x - phi x) center coordinates -
    slp_mixed_center_finite_weighted_oscillatory_integrand tau
      Q left_cutoff q A right_cutoff qt (\<lambda>_. 1)
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * B z) x -
        phi x * B x) center coordinates -
    slp_mixed_center_finite_weighted_oscillatory_integrand tau
      Q left_cutoff q (\<lambda>_. 1) right_cutoff qt B
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * A z) x -
        phi x * A x) center coordinates +
    slp_mixed_center_finite_weighted_oscillatory_integrand tau
      Q left_cutoff q (\<lambda>_. 1) right_cutoff qt (\<lambda>_. 1)
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * (A z * B z)) x -
        phi x * (A x * B x)) center coordinates"
proof -
  have factor:
    "slp_mixed_center_finite_weighted_oscillatory_integrand tau
        Q left_cutoff q T right_cutoff qt U H center coordinates =
      slp_parameterized_real_phase_integrand tau slp_mixed_center_finite_residual
        (slp_mixed_center_finite_complex_amplitude Q left_cutoff q right_cutoff qt)
        center coordinates *
        (T (snd (fst (snd coordinates))) *
          U (slp_mixed_center_finite_right_terminal center coordinates) * H center)"
    for T U H
    by (rule slp_mixed_weighted_integrand_terminal_factor)
  show ?thesis
    unfolding slp_mixed_center_finite_bracket_integrand_def
    by (simp only: factor slp_mixed_center_average_bracket_decomposition;
        simp add: algebra_simps)
qed

end
