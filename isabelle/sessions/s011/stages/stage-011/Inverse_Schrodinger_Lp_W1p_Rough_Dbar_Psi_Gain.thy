theory Inverse_Schrodinger_Lp_W1p_Rough_Dbar_Psi_Gain
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_Qstar_W1p_Claim"
begin

section \<open>Conjugation preserves local weak gradients\<close>

theorem slp_weak_gradient_on_cnj:
  assumes weak: "slp_weak_gradient_on X u Du"
  shows "slp_weak_gradient_on X (\<lambda>x. cnj (u x)) (slp_conjugate_gradient Du)"
  unfolding slp_weak_gradient_on_def
proof (intro allI impI)
  fix phi i
  assume phi_test: "slp_test_function_on X phi"
  let ?psi = "\<lambda>x. cnj (phi x)"
  have phi_smooth: "smooth_on UNIV phi"
    using phi_test unfolding slp_test_function_on_def by blast
  have psi_test: "slp_test_function_on X ?psi"
    using phi_test by simp
  have source:
      "set_integrable lborel X
          (\<lambda>x. u x * slp_complex_partial_derivative ?psi i x) \<and>
       set_integrable lborel X (\<lambda>x. Du x $ i * ?psi x) \<and>
       set_lebesgue_integral lborel X
          (\<lambda>x. u x * slp_complex_partial_derivative ?psi i x) =
        - set_lebesgue_integral lborel X (\<lambda>x. Du x $ i * ?psi x)"
    using weak psi_test unfolding slp_weak_gradient_on_def by blast
  have indicator_cnj:
      "(\<lambda>x. indicator X x *\<^sub>R cnj (h x)) =
        (\<lambda>x. cnj (indicator X x *\<^sub>R h x))"
    for h :: slp_scalar_field
    by (rule ext) (simp add: indicator_def)
  have set_cnj_integrable:
      "set_integrable lborel X (\<lambda>x. cnj (h x))"
    if h_integrable: "set_integrable lborel X h"
    for h :: slp_scalar_field
    using integrable_cnj[OF h_integrable[unfolded set_integrable_def]]
    unfolding set_integrable_def
    by (simp only: indicator_cnj)
  have set_cnj_integral:
      "set_lebesgue_integral lborel X (\<lambda>x. cnj (h x)) =
        cnj (set_lebesgue_integral lborel X h)"
    for h :: slp_scalar_field
    by (simp only: set_lebesgue_integral_def indicator_cnj
          Bochner_Integration.integral_cnj)
  have first_integrand:
      "(\<lambda>x. cnj (u x * slp_complex_partial_derivative ?psi i x)) =
        (\<lambda>x. cnj (u x) * slp_complex_partial_derivative phi i x)"
    by (rule ext)
      (simp add: slp_complex_partial_derivative_cnj[OF phi_smooth])
  have second_integrand:
      "(\<lambda>x. cnj (Du x $ i * ?psi x)) =
        (\<lambda>x. slp_conjugate_gradient Du x $ i * phi x)"
    by (rule ext) (simp add: slp_conjugate_gradient_def)
  have first_integrable:
      "set_integrable lborel X
        (\<lambda>x. cnj (u x) * slp_complex_partial_derivative phi i x)"
    using set_cnj_integrable[OF conjunct1[OF source]]
    by (simp only: first_integrand)
  have second_integrable:
      "set_integrable lborel X
        (\<lambda>x. slp_conjugate_gradient Du x $ i * phi x)"
    using set_cnj_integrable[OF conjunct1[OF conjunct2[OF source]]]
    by (simp only: second_integrand)
  have source_identity:
      "set_lebesgue_integral lborel X
          (\<lambda>x. u x * slp_complex_partial_derivative ?psi i x) =
        - set_lebesgue_integral lborel X (\<lambda>x. Du x $ i * ?psi x)"
    by (rule conjunct2[OF conjunct2[OF source]])
  have conjugate_identity:
      "set_lebesgue_integral lborel X
          (\<lambda>x. cnj (u x * slp_complex_partial_derivative ?psi i x)) =
        - set_lebesgue_integral lborel X (\<lambda>x. cnj (Du x $ i * ?psi x))"
    by (simp only: set_cnj_integral source_identity; simp)
  have identity:
      "set_lebesgue_integral lborel X
          (\<lambda>x. cnj (u x) * slp_complex_partial_derivative phi i x) =
        - set_lebesgue_integral lborel X
          (\<lambda>x. slp_conjugate_gradient Du x $ i * phi x)"
    using conjugate_identity
    by (simp only: first_integrand second_integrand)
  show "set_integrable lborel X
          (\<lambda>x. cnj (u x) * slp_complex_partial_derivative phi i x) \<and>
        set_integrable lborel X
          (\<lambda>x. slp_conjugate_gradient Du x $ i * phi x) \<and>
        set_lebesgue_integral lborel X
          (\<lambda>x. cnj (u x) * slp_complex_partial_derivative phi i x) =
          - set_lebesgue_integral lborel X
            (\<lambda>x. slp_conjugate_gradient Du x $ i * phi x)"
    by (rule conjI[OF first_integrable conjI[OF second_integrable identity]])
qed


section \<open>Conjugation preserves zero-boundary Sobolev approximation\<close>

theorem slp_w1p_zero_pair_on_cnj:
  assumes zero_pair: "slp_w1p_zero_pair_on p X u Du"
  shows "slp_w1p_zero_pair_on p X (\<lambda>x. cnj (u x)) (slp_conjugate_gradient Du) \<and>
    slp_w1p_norm_on p X (\<lambda>x. cnj (u x)) (slp_conjugate_gradient Du) =
      slp_w1p_norm_on p X u Du"
proof -
  have restrict_cnj:
      "slp_restrict_field X (\<lambda>x. cnj (h x)) =
        (\<lambda>x. cnj (slp_restrict_field X h x))"
    for h :: slp_scalar_field
    by (rule ext) (simp add: slp_restrict_field_def)
  have norm_cnj:
      "slp_w1p_norm_on p X (\<lambda>x. cnj (v x)) (slp_conjugate_gradient Dv) =
        slp_w1p_norm_on p X v Dv"
    for v :: slp_scalar_field and Dv :: slp_gradient_field
    by (simp add: slp_w1p_norm_on_def slp_conjugate_gradient_def restrict_cnj)
  have lp_cnj: "slp_complex_lp_on p X (\<lambda>x. cnj (h x))"
    if h_lp: "slp_complex_lp_on p X h"
    for h :: slp_scalar_field
    using h_lp
    by (simp only: slp_complex_lp_on_def restrict_cnj
          aim_complex_lp_on_plane_cnj_iff)
  have pair_cnj:
      "slp_w1p_pair_on p X (\<lambda>x. cnj (v x)) (slp_conjugate_gradient Dv)"
    if pair: "slp_w1p_pair_on p X v Dv"
    for v :: slp_scalar_field and Dv :: slp_gradient_field
  proof -
    have weak: "slp_weak_gradient_on X (\<lambda>x. cnj (v x)) (slp_conjugate_gradient Dv)"
      by (rule slp_weak_gradient_on_cnj[OF slp_w1p_pair_onD(1)[OF pair]])
    have value_lp: "slp_complex_lp_on p X (\<lambda>x. cnj (v x))"
      by (rule lp_cnj[OF slp_w1p_pair_onD(2)[OF pair]])
    have zero_lp: "slp_complex_lp_on p X (\<lambda>x. cnj (Dv x $ 0))"
      by (rule lp_cnj[OF slp_w1p_pair_onD(3)[OF pair]])
    have one_lp: "slp_complex_lp_on p X (\<lambda>x. cnj (Dv x $ 1))"
      by (rule lp_cnj[OF slp_w1p_pair_onD(4)[OF pair]])
    show ?thesis
      unfolding slp_w1p_pair_on_def
      using weak value_lp zero_lp one_lp
      by (simp add: slp_conjugate_gradient_def)
  qed
  have classical_cnj:
      "slp_classical_gradient (\<lambda>x. cnj (v x)) =
        slp_conjugate_gradient (slp_classical_gradient v)"
    if v_test: "slp_test_function_on X v"
    for v :: slp_scalar_field
  proof -
    have v_smooth: "smooth_on UNIV v"
      using v_test unfolding slp_test_function_on_def by blast
    show ?thesis
      by (rule ext)
        (simp add: slp_classical_gradient_def slp_conjugate_gradient_def
          slp_complex_partial_derivative_cnj[OF v_smooth])
  qed
  have base_pair: "slp_w1p_pair_on p X u Du"
    using zero_pair unfolding slp_w1p_zero_pair_on_def by blast
  obtain phi :: "nat \<Rightarrow> slp_scalar_field" where
    phi_test: "\<And>n. slp_test_function_on X (phi n)"
    and phi_pair: "\<And>n. slp_w1p_pair_on p X (phi n) (slp_classical_gradient (phi n))"
    and source_tail:
      "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
        slp_w1p_norm_on p X (\<lambda>x. phi n x - u x)
          (\<lambda>x. slp_classical_gradient (phi n) x - Du x) < epsilon"
    using zero_pair unfolding slp_w1p_zero_pair_on_def by blast
  let ?psi = "\<lambda>n x. cnj (phi n x)"
  have psi_test: "slp_test_function_on X (?psi n)" for n
    using phi_test[of n] by simp
  have psi_pair:
      "slp_w1p_pair_on p X (?psi n) (slp_classical_gradient (?psi n))"
    for n
    using pair_cnj[OF phi_pair[of n]]
    by (simp only: classical_cnj[OF phi_test[of n]])
  have error_norm:
      "slp_w1p_norm_on p X (\<lambda>x. ?psi n x - cnj (u x))
          (\<lambda>x. slp_classical_gradient (?psi n) x - slp_conjugate_gradient Du x) =
        slp_w1p_norm_on p X (\<lambda>x. phi n x - u x)
          (\<lambda>x. slp_classical_gradient (phi n) x - Du x)"
    for n
  proof -
    have value_difference:
        "(\<lambda>x. cnj (phi n x - u x)) =
          (\<lambda>x. ?psi n x - cnj (u x))"
      by (rule ext) simp
    have gradient_difference:
        "slp_conjugate_gradient (\<lambda>x. slp_classical_gradient (phi n) x - Du x) =
          (\<lambda>x. slp_classical_gradient (?psi n) x - slp_conjugate_gradient Du x)"
      by (rule ext)
        (simp add: classical_cnj[OF phi_test[of n]]
          slp_conjugate_gradient_def vec_eq_iff)
    show ?thesis
      using norm_cnj[of "\<lambda>x. phi n x - u x"
        "\<lambda>x. slp_classical_gradient (phi n) x - Du x"]
      by (simp only: value_difference gradient_difference)
  qed
  have conjugate_tail:
      "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
        slp_w1p_norm_on p X (\<lambda>x. ?psi n x - cnj (u x))
          (\<lambda>x. slp_classical_gradient (?psi n) x - slp_conjugate_gradient Du x)
          < epsilon"
    using source_tail by (simp only: error_norm)
  have conjugate_zero:
      "slp_w1p_zero_pair_on p X (\<lambda>x. cnj (u x)) (slp_conjugate_gradient Du)"
    unfolding slp_w1p_zero_pair_on_def
    by (rule conjI[OF pair_cnj[OF base_pair]], rule exI[of _ ?psi])
      (use psi_test psi_pair conjugate_tail in blast)
  show ?thesis
    by (rule conjI[OF conjugate_zero norm_cnj])
qed


section \<open>The rough estimate for the conjugated Cauchy operator\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_w1p_zero_pair_dbar_psi_gain:
  assumes a_lower: "1 < a" and a_upper: "a < 2"
    and X_bounded: "bounded X"
  shows "\<exists>C::real. 0 < C \<and>
    (\<forall>tau c f Df.
      2 \<le> tau \<and> slp_w1p_zero_pair_on a X f Df
      \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_dbar_psi_inverse tau c (slp_restrict_field X f)) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a)
        (slp_dbar_psi_inverse tau c (slp_restrict_field X f))
        \<le> C * inverse (sqrt tau) * slp_w1p_norm_on a X f Df)"
proof -
  obtain C::real where C_positive: "0 < C"
    and partial_gain:
      "\<And>tau c f Df.
        2 \<le> tau \<Longrightarrow> slp_w1p_zero_pair_on a X f Df \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau c (slp_restrict_field X f)) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau c (slp_restrict_field X f))
          \<le> C * inverse (sqrt tau) * slp_w1p_norm_on a X f Df"
    using slp_w1p_zero_pair_partial_psi_gain[
      OF a_lower a_upper X_bounded] by blast
  have dbar_gain:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_dbar_psi_inverse tau c (slp_restrict_field X f)) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a)
        (slp_dbar_psi_inverse tau c (slp_restrict_field X f))
        \<le> C * inverse (sqrt tau) * slp_w1p_norm_on a X f Df"
    if tau_lower: "2 \<le> tau" and zero_pair: "slp_w1p_zero_pair_on a X f Df"
    for tau c f Df
  proof -
    let ?cf = "\<lambda>x. cnj (f x)"
    let ?cDf = "slp_conjugate_gradient Df"
    note conjugate_data = slp_w1p_zero_pair_on_cnj[OF zero_pair]
    have conjugate_pair: "slp_w1p_zero_pair_on a X ?cf ?cDf"
      by (rule conjunct1[OF conjugate_data])
    have conjugate_norm:
        "slp_w1p_norm_on a X ?cf ?cDf = slp_w1p_norm_on a X f Df"
      by (rule conjunct2[OF conjugate_data])
    note partial_data = partial_gain[OF tau_lower conjugate_pair, of c]
    have input_conjugate:
        "(\<lambda>x. cnj (slp_restrict_field X ?cf x)) = slp_restrict_field X f"
      by (rule ext) (simp add: slp_restrict_field_def)
    let ?P = "slp_partial_psi_inverse tau c (slp_restrict_field X ?cf)"
    let ?D = "slp_dbar_psi_inverse tau c (slp_restrict_field X f)"
    have output_conjugate: "(\<lambda>x. cnj (?P x)) = ?D"
      by (rule ext)
        (simp only: slp_partial_psi_inverse_conjugate input_conjugate)
    have output_lp: "aim_complex_lp_on_plane (aim_hls_target_exponent a) ?D"
      using conjunct1[OF partial_data]
      by (simp only: output_conjugate[symmetric]
            aim_complex_lp_on_plane_cnj_iff)
    have output_bound:
        "aim_complex_lp_norm (aim_hls_target_exponent a) ?D
          \<le> C * inverse (sqrt tau) * slp_w1p_norm_on a X f Df"
      using conjunct2[OF partial_data]
      by (simp only: output_conjugate[symmetric]
            aim_complex_lp_norm_cnj conjugate_norm)
    show ?thesis by (rule conjI[OF output_lp output_bound])
  qed
  show ?thesis
    by (rule exI[of _ C], rule conjI[OF C_positive])
      (use dbar_gain in blast)
qed

end

end
