theory Inverse_Schrodinger_Lp_H1_Zero_W1p_Two
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_H1_Pair_W1p_Descent"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Exponent-two comparison of the project Sobolev norms\<close>

lemma slp_w1p_norm_on_two_eq_h1_squared_distance_root:
  assumes X_measurable: "X \<in> sets (lborel :: slp_point measure)"
    and left_pair: "slp_h1_pair_on X u Du"
    and right_pair: "slp_h1_pair_on X v Dv"
  shows "slp_w1p_norm_on 2 X
      (\<lambda>x. u x - v x) (\<lambda>x. Du x - Dv x) =
    slp_h1_squared_distance X u Du v Dv powr (1 / 2)"
proof -
  let ?e = "\<lambda>x. u x - v x"
  let ?De = "\<lambda>x. Du x - Dv x"
  let ?F = "\<lambda>x. Real_Vector_Spaces.norm
    (slp_restrict_field X ?e x) powr 2"
  let ?G = "\<lambda>x. Real_Vector_Spaces.norm
    (slp_restrict_field X (\<lambda>y. ?De y $ 0) x) powr 2"
  let ?H = "\<lambda>x. Real_Vector_Spaces.norm
    (slp_restrict_field X (\<lambda>y. ?De y $ 1) x) powr 2"
  have left_w1p: "slp_w1p_pair_on 2 X u Du"
    by (rule slp_h1_pair_on_w1p_pair_on_two[OF X_measurable left_pair])
  have right_w1p: "slp_w1p_pair_on 2 X v Dv"
    by (rule slp_h1_pair_on_w1p_pair_on_two[OF X_measurable right_pair])
  have error_pair: "slp_w1p_pair_on 2 X ?e ?De"
    by (rule slp_w1p_pair_on_diff[OF _ left_w1p right_w1p]) simp
  have F_integrable: "integrable lborel ?F"
    using error_pair
    unfolding slp_w1p_pair_on_def slp_complex_lp_on_def
      aim_complex_lp_on_plane_def by blast
  have G_integrable: "integrable lborel ?G"
    using error_pair
    unfolding slp_w1p_pair_on_def slp_complex_lp_on_def
      aim_complex_lp_on_plane_def by blast
  have H_integrable: "integrable lborel ?H"
    using error_pair
    unfolding slp_w1p_pair_on_def slp_complex_lp_on_def
      aim_complex_lp_on_plane_def by blast
  have FG_integrable: "integrable lborel (\<lambda>x. ?F x + ?G x)"
    by (rule Bochner_Integration.integrable_add[OF F_integrable G_integrable])
  have integrand:
      "(\<lambda>x. indicator X x *\<^sub>R
          (Real_Vector_Spaces.norm (?e x) ^ 2 +
            Real_Vector_Spaces.norm (?De x) ^ 2)) =
        (\<lambda>x. ?F x + ?G x + ?H x)"
    by (rule ext)
       (auto simp: indicator_def slp_restrict_field_def powr_nat
          slp_gradient_norm_square_components)
  have integral_sum:
      "integral\<^sup>L lborel (\<lambda>x. ?F x + ?G x + ?H x) =
        integral\<^sup>L lborel ?F + integral\<^sup>L lborel ?G +
          integral\<^sup>L lborel ?H"
  proof -
    have FG_integral:
        "integral\<^sup>L lborel (\<lambda>x. ?F x + ?G x) =
          integral\<^sup>L lborel ?F + integral\<^sup>L lborel ?G"
      by (rule Bochner_Integration.integral_add[OF
            F_integrable G_integrable])
    have FGH_integral:
        "integral\<^sup>L lborel (\<lambda>x. (?F x + ?G x) + ?H x) =
          integral\<^sup>L lborel (\<lambda>x. ?F x + ?G x) +
            integral\<^sup>L lborel ?H"
      by (rule Bochner_Integration.integral_add[OF
            FG_integrable H_integrable])
    show ?thesis
      using FGH_integral by (simp only: FG_integral)
  qed
  have distance_identity:
      "slp_h1_squared_distance X u Du v Dv =
        integral\<^sup>L lborel ?F + integral\<^sup>L lborel ?G +
          integral\<^sup>L lborel ?H"
    unfolding slp_h1_squared_distance_def set_lebesgue_integral_def integrand
    by (rule integral_sum)
  show ?thesis
    unfolding slp_w1p_norm_on_def distance_identity by simp
qed

theorem slp_h1_zero_pair_on_w1p_zero_pair_on_two:
  assumes X_measurable: "X \<in> sets (lborel :: slp_point measure)"
    and zero_pair: "slp_h1_zero_pair_on X u Du"
  shows "slp_w1p_zero_pair_on 2 X u Du"
proof -
  have base_h1: "slp_h1_pair_on X u Du"
    using zero_pair unfolding slp_h1_zero_pair_on_def by blast
  have base_w1p: "slp_w1p_pair_on 2 X u Du"
    by (rule slp_h1_pair_on_w1p_pair_on_two[OF X_measurable base_h1])
  obtain phi :: "nat \<Rightarrow> slp_scalar_field" where
    phi_test: "\<And>n. slp_test_function_on X (phi n)"
    and phi_h1:
      "\<And>n. slp_h1_pair_on X (phi n) (slp_classical_gradient (phi n))"
    and h1_tail:
      "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
        slp_h1_squared_distance X (phi n)
          (slp_classical_gradient (phi n)) u Du < epsilon"
    using zero_pair unfolding slp_h1_zero_pair_on_def by blast
  have phi_w1p:
      "slp_w1p_pair_on 2 X (phi n) (slp_classical_gradient (phi n))"
    for n
    by (rule slp_h1_pair_on_w1p_pair_on_two[OF X_measurable phi_h1])
  have distance_nonnegative:
      "0 \<le> slp_h1_squared_distance X (phi n)
        (slp_classical_gradient (phi n)) u Du" for n
    unfolding slp_h1_squared_distance_def set_lebesgue_integral_def
    by (rule integral_nonneg_AE) simp
  have norm_identity:
      "slp_w1p_norm_on 2 X (\<lambda>x. phi n x - u x)
          (\<lambda>x. slp_classical_gradient (phi n) x - Du x) =
        slp_h1_squared_distance X (phi n)
          (slp_classical_gradient (phi n)) u Du powr (1 / 2)" for n
    by (rule slp_w1p_norm_on_two_eq_h1_squared_distance_root[OF
          X_measurable phi_h1 base_h1])
  have norm_tail:
      "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
        slp_w1p_norm_on 2 X (\<lambda>x. phi n x - u x)
          (\<lambda>x. slp_classical_gradient (phi n) x - Du x) < epsilon"
  proof (intro allI impI)
    fix epsilon :: real
    assume epsilon_positive: "0 < epsilon"
    have epsilon_power_positive: "0 < epsilon powr 2"
      using epsilon_positive by simp
    obtain N where tail:
        "\<forall>n\<ge>N. slp_h1_squared_distance X (phi n)
          (slp_classical_gradient (phi n)) u Du < epsilon powr 2"
      using h1_tail epsilon_power_positive by blast
    show "\<exists>N. \<forall>n\<ge>N.
        slp_w1p_norm_on 2 X (\<lambda>x. phi n x - u x)
          (\<lambda>x. slp_classical_gradient (phi n) x - Du x) < epsilon"
    proof (rule exI[of _ N], intro allI impI)
      fix n
      assume N_le_n: "N \<le> n"
      have powered_less:
          "slp_h1_squared_distance X (phi n)
              (slp_classical_gradient (phi n)) u Du powr (1 / 2) <
            (epsilon powr 2) powr (1 / 2)"
        by (rule powr_less_mono2)
           (use distance_nonnegative[of n] tail N_le_n in auto)
      show "slp_w1p_norm_on 2 X (\<lambda>x. phi n x - u x)
          (\<lambda>x. slp_classical_gradient (phi n) x - Du x) < epsilon"
        using powered_less epsilon_positive
        by (simp add: norm_identity powr_powr)
    qed
  qed
  show ?thesis
    unfolding slp_w1p_zero_pair_on_def
    by (rule conjI[OF base_w1p], rule exI[of _ phi])
       (use phi_test phi_w1p norm_tail in blast)
qed

end
