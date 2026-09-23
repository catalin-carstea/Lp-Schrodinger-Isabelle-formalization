theory Inverse_Schrodinger_Lp_Hyperbolic_Frequency_Normalization
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Damped_Center_Hyperbolic_Raw"
begin

section \<open>Real hyperbolic frequency normalization\<close>

lemma slp_hyperbolic_denominator_positive:
  fixes eps tau :: real
  assumes eps: "0 < eps"
  shows "0 < eps ^ 2 + tau ^ 2"
proof -
  have eps_square: "0 < eps ^ 2"
    by (rule zero_less_power[OF eps])
  show ?thesis
    by (rule add_pos_nonneg[OF eps_square zero_le_power2])
qed

lemma slp_hyperbolic_frequency_square_sum:
  "slp_hyperbolic_freq_plus xi ^ 2 +
      slp_hyperbolic_freq_minus xi ^ 2 =
    ((xi $ (0 :: 2)) ^ 2 + (xi $ (1 :: 2)) ^ 2) / 2"
proof -
    have scalar:
      "((a + b) / 2) ^ 2 + ((a - b) / 2) ^ 2 =
        (a ^ 2 + b ^ 2) / 2" for a b :: real
    by (simp add: divide_simps algebra_simps power2_eq_square
        mult_ac add_ac)
  show ?thesis
    unfolding slp_hyperbolic_freq_plus_def
      slp_hyperbolic_freq_minus_def
    by (rule scalar)
qed

lemma slp_hyperbolic_frequency_product:
  "slp_hyperbolic_freq_minus xi *
      slp_hyperbolic_freq_plus xi =
    slp_center_phase 0 xi / 4"
proof -
  have scalar:
      "((a - b) / 2) * ((a + b) / 2) =
        (a ^ 2 - b ^ 2) / 4" for a b :: real
    by (simp add: divide_simps algebra_simps power2_eq_square
        mult_ac add_ac)
  show ?thesis
    unfolding slp_hyperbolic_freq_plus_def
      slp_hyperbolic_freq_minus_def slp_center_phase_def
    using scalar[of "xi $ (0 :: 2)" "xi $ (1 :: 2)"]
    by simp
qed

lemma slp_hyperbolic_translation_phase:
  assumes eps: "0 < eps"
  shows "- slp_hyperbolic_freq_minus xi *
      slp_hyperbolic_second_center eps tau xi =
    - (tau * slp_center_phase 0 xi /
      (4 * (eps ^ 2 + tau ^ 2)))"
proof -
  let ?D = "eps ^ 2 + tau ^ 2"
  have product:
      "slp_hyperbolic_freq_minus xi *
          slp_hyperbolic_freq_plus xi =
        slp_center_phase 0 xi / 4"
    by (rule slp_hyperbolic_frequency_product)
  have regroup:
      "- slp_hyperbolic_freq_minus xi *
          (slp_hyperbolic_freq_plus xi * tau / ?D) =
        - (slp_hyperbolic_freq_minus xi *
          slp_hyperbolic_freq_plus xi) * tau / ?D"
    by (simp add: divide_simps algebra_simps)
  have scalar:
      "- (a / 4) * b / d = - (b * a / (4 * d))"
      for a b d :: real
    by (simp add: divide_simps algebra_simps)
  show ?thesis
    unfolding slp_hyperbolic_second_center_def
    using regroup product scalar[of "slp_center_phase 0 xi" tau ?D]
    by simp
qed

end
