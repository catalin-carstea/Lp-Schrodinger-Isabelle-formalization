theory Inverse_Schrodinger_Lp_Interpolation_Exponent_Selection
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Nested_Coefficient_Difference_Pointwise"
begin

section \<open>Explicit exponents for the low/high endpoint split\<close>

theorem slp_interpolation_exponents:
  fixes p epsilon :: real
  assumes exponent_lower: "1 < p"
    and exponent_upper: "p < 2"
    and loss_positive: "0 < epsilon"
  shows
    "\<exists>a b theta::real.
      1 < a \<and> a < p \<and> p < 2 \<and> 2 < b
      \<and> 0 < theta \<and> theta < 1
      \<and> 1 / p = (1 - theta) / a + theta / b
      \<and> 1 - 1 / p - epsilon < theta / 2"
proof -
  have p_positive: "0 < p"
    using exponent_lower by linarith
  have inverse_p_below_one: "1 / p < 1"
    using exponent_lower p_positive
    by (simp add: pos_divide_less_eq)
  have half_below_inverse_p: "(1 / 2::real) < 1 / p"
    using exponent_upper p_positive
    by (simp add: pos_less_divide_eq)

  let ?g = "1 - 1 / p"
  let ?d = "min (epsilon / 2) (?g / 2)"
  let ?A = "1 - ?d"
  let ?B = "1 / 2 - ?d"
  let ?a = "inverse ?A"
  let ?b = "inverse ?B"
  let ?theta = "2 * (?g - ?d)"

  have g_positive: "0 < ?g"
    using inverse_p_below_one by linarith
  have g_below_half: "?g < 1 / 2"
    using half_below_inverse_p by linarith
  have d_positive: "0 < ?d"
    using loss_positive g_positive by simp
  have d_le_loss_half: "?d \<le> epsilon / 2"
    by (rule min.cobounded1)
  have d_le_g_half: "?d \<le> ?g / 2"
    by (rule min.cobounded2)
  have d_below_loss: "?d < epsilon"
    using d_le_loss_half loss_positive by linarith
  have two_positive: "0 < (2::real)"
    by simp
  have one_below_two: "(1::real) < 2"
    by simp
  have "?g * 1 < ?g * 2"
    using one_below_two g_positive by (rule mult_strict_left_mono)
  then have g_below_twice: "?g < ?g * 2"
    by (simp only: mult.right_neutral)
  have half_equivalence: "?g / 2 < ?g \<longleftrightarrow> ?g < ?g * 2"
    using two_positive by (rule pos_divide_less_eq)
  have g_half_below_g: "?g / 2 < ?g"
    using iffD2[OF half_equivalence g_below_twice] .
  have d_below_g: "?d < ?g"
    using d_le_g_half g_half_below_g by (rule le_less_trans)
  have d_below_half: "?d < 1 / 2"
    using d_below_g g_below_half by linarith

  have A_positive: "0 < ?A"
    using d_below_half by linarith
  have B_positive: "0 < ?B"
    using d_below_half by linarith
  have inverse_p_below_A: "1 / p < ?A"
    using d_below_g by linarith

  have A_below_one: "?A < 1"
    using d_positive by linarith
  have one_less_a: "1 < ?a"
    using A_positive A_below_one by (rule one_less_inverse)
  have a_less_p: "?a < p"
  proof -
    have inverse_p_positive: "0 < 1 / p"
      using p_positive by (simp only: zero_less_divide_1_iff)
    have "inverse ?A < inverse (1 / p)"
      using inverse_p_below_A inverse_p_positive
      by (rule less_imp_inverse_less)
    then show ?thesis
      by (simp only: divide_inverse mult.left_neutral inverse_inverse_eq)
  qed
  have two_less_b: "2 < ?b"
  proof -
    have B_below_half: "?B < 1 / 2"
      using d_positive by linarith
    have "inverse (1 / 2::real) < inverse ?B"
      using B_below_half B_positive by (rule less_imp_inverse_less)
    then show ?thesis
      by (simp only: divide_inverse mult.left_neutral inverse_inverse_eq)
  qed

  have gap_positive: "0 < ?g - ?d"
    using d_below_g by linarith
  have theta_positive: "0 < ?theta"
    using mult_pos_pos[OF two_positive gap_positive] .
  have gap_below_half: "?g - ?d < 1 / 2"
    using g_below_half d_positive by linarith
  have gap_equivalence:
      "?g - ?d < 1 / 2 \<longleftrightarrow> (?g - ?d) * 2 < 1"
    using two_positive by (rule pos_less_divide_eq)
  have gap_times_two_below_one: "(?g - ?d) * 2 < 1"
    using iffD1[OF gap_equivalence gap_below_half] .
  have theta_below_one: "?theta < 1"
    by (subst mult.commute) (rule gap_times_two_below_one)

  define u :: real where "u = 1 / p"
  define d0 :: real where "d0 = ?d"
  define q :: real where "q = (1 - u) - d0"
  have endpoint_scaled: "2 * (1 / 2 - d0) = 1 - 2 * d0"
    by (simp add: algebra_simps)
  have second_rewrite:
      "2 * q * (1 / 2 - d0) = q * (1 - 2 * d0)"
  proof -
    have "2 * q * (1 / 2 - d0) = q * (2 * (1 / 2 - d0))"
      by (simp only: mult.assoc mult.commute mult.left_commute)
    also have "... = q * (1 - 2 * d0)"
      by (simp only: endpoint_scaled)
    finally show ?thesis .
  qed
  have identity_with_gap:
      "(1 - 2 * q) * (1 - d0) + 2 * q * (1 / 2 - d0) = u"
  proof -
    have "(1 - 2 * q) * (1 - d0) + 2 * q * (1 / 2 - d0)
        = (1 - 2 * q) * (1 - d0) + q * (1 - 2 * d0)"
      by (simp only: second_rewrite)
    also have "... = u"
      unfolding q_def by ring
    finally show ?thesis .
  qed
  have polynomial_identity:
      "(1 - 2 * ((1 - u) - d0)) * (1 - d0)
        + 2 * ((1 - u) - d0) * (1 / 2 - d0) = u"
    using identity_with_gap by (simp only: q_def)
  have weighted_identity:
      "(1 - ?theta) * ?A + ?theta * ?B = 1 / p"
    using polynomial_identity
    by (simp only: u_def d0_def)
  have reciprocal_rewrites:
      "(1 - ?theta) / ?a + ?theta / ?b
        = (1 - ?theta) * ?A + ?theta * ?B"
    by (simp only: divide_inverse inverse_inverse_eq)
  have interpolation_identity:
      "1 / p = (1 - ?theta) / ?a + ?theta / ?b"
  proof -
    have "1 / p = (1 - ?theta) * ?A + ?theta * ?B"
      using weighted_identity by (rule sym)
    also have "... = (1 - ?theta) / ?a + ?theta / ?b"
      using reciprocal_rewrites by (rule sym)
    finally show ?thesis .
  qed

  define h :: real where "h = ?g - ?d"
  have rate_abstract: "(2 * h) / 2 = h"
    by (rule nonzero_mult_div_cancel_left) simp
  have rate_identity: "?theta / 2 = ?g - ?d"
    using rate_abstract by (simp only: h_def)
  have rate_loss: "1 - 1 / p - epsilon < ?theta / 2"
  proof -
    have gap_loss: "?g - epsilon < ?g - ?d"
      using d_below_loss by linarith
    show ?thesis
      by (subst rate_identity) (rule gap_loss)
  qed

  show ?thesis
    using one_less_a a_less_p exponent_upper two_less_b theta_positive
      theta_below_one interpolation_identity rate_loss
    by blast
qed

end
