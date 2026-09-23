theory Inverse_Schrodinger_Lp_Qstar_Exponent_Arithmetic
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Squared_Radial_Annulus_Power_Geometric"
begin

section \<open>Exponent arithmetic for the smooth qstar estimate\<close>

definition slp_qstar_holder_exponent :: "real \<Rightarrow> real" where
  "slp_qstar_holder_exponent a =
    aim_hls_target_exponent a / (aim_hls_target_exponent a - 1)"

theorem slp_qstar_exponent_relations:
  assumes exponent_lower: "1 < a"
    and exponent_upper: "a < 2"
  shows target_above_two: "2 < aim_hls_target_exponent a"
    and holder_lower: "1 < slp_qstar_holder_exponent a"
    and holder_upper: "slp_qstar_holder_exponent a < 2"
    and conjugate:
      "1 / aim_hls_target_exponent a +
        1 / slp_qstar_holder_exponent a = 1"
    and half_target_lower: "1 < aim_hls_target_exponent a / 2"
    and scale_balance:
      "2 / aim_hls_target_exponent a +
        2 / slp_qstar_holder_exponent a = 2"
    and square_scale_balance:
      "(2 / aim_hls_target_exponent a - 1) +
        (2 / slp_qstar_holder_exponent a - 2) = -1"
proof -
  let ?q = "aim_hls_target_exponent a"
  let ?s = "slp_qstar_holder_exponent a"
  have denominator_positive: "0 < 2 - a"
    using exponent_upper by linarith
  have q_above_two: "2 < ?q"
    unfolding aim_hls_target_exponent_def
    using exponent_lower denominator_positive
    by (simp add: less_divide_eq)
  have q_minus_one_positive: "0 < ?q - 1"
    using q_above_two by linarith
  have q_nonzero: "?q \<noteq> 0"
    using q_above_two by linarith
  have q_minus_one_nonzero: "?q - 1 \<noteq> 0"
    using q_minus_one_positive by simp
  have s_formula: "?s = ?q / (?q - 1)"
    unfolding slp_qstar_holder_exponent_def by (rule refl)
  have s_lower: "1 < ?s"
    unfolding s_formula
    apply (rule iffD2[OF pos_less_divide_eq[OF q_minus_one_positive]])
    using q_minus_one_positive
    by (simp only: mult_1_left; linarith)
  have upper_linear: "?q < 2 * (?q - 1)"
    using q_above_two
    by (simp only: mult_2; linarith)
  have s_upper: "?s < 2"
    unfolding s_formula
    apply (rule iffD2[OF pos_divide_less_eq[OF q_minus_one_positive]])
    by (rule upper_linear)
  have s_nonzero: "?s \<noteq> 0"
    using s_lower by linarith
  have inverse_s_formula: "1 / ?s = (?q - 1) / ?q"
    unfolding s_formula
    using q_nonzero q_minus_one_nonzero by simp
  have common_denominator:
      "1 / ?q + (?q - 1) / ?q = (1 + (?q - 1)) / ?q"
    by (rule add_divide_distrib[symmetric])
  have conjugate_relation: "1 / ?q + 1 / ?s = 1"
    using inverse_s_formula common_denominator q_nonzero by simp
  have scale_relation: "2 / ?q + 2 / ?s = 2"
    using conjugate_relation by linarith
  show "2 < ?q"
    by (rule q_above_two)
  show "1 < ?s"
    by (rule s_lower)
  show "?s < 2"
    by (rule s_upper)
  show "1 / ?q + 1 / ?s = 1"
    by (rule conjugate_relation)
  show "1 < ?q / 2"
    using q_above_two by linarith
  show "2 / ?q + 2 / ?s = 2"
    by (rule scale_relation)
  show "(2 / ?q - 1) + (2 / ?s - 2) = -1"
    using scale_relation by linarith
qed

end
