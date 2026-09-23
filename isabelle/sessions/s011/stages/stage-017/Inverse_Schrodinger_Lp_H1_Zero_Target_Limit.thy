theory Inverse_Schrodinger_Lp_H1_Zero_Target_Limit
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_W1p_Zero_Pair_Exponent_Descent"
begin

section \<open>Project H1-zero certificates at subquadratic exponents\<close>

theorem slp_h1_zero_pair_on_w1p_zero_pair_on_below_two:
  assumes a_lower: "1 < (a::real)"
    and a_upper: "a < 2"
    and X_measurable: "X \<in> sets (lborel :: slp_point measure)"
    and X_bounded: "bounded X"
    and zero_h1: "slp_h1_zero_pair_on X u Du"
  shows "slp_w1p_zero_pair_on a X u Du"
proof -
  have a_one_le: "1 \<le> a" using a_lower by linarith
  have zero_two: "slp_w1p_zero_pair_on 2 X u Du"
    by (rule slp_h1_zero_pair_on_w1p_zero_pair_on_two[
          OF X_measurable zero_h1])
  show ?thesis
    by (rule slp_w1p_zero_pair_on_mono_exponent_bounded[
          OF a_one_le a_upper X_measurable X_bounded zero_two])
qed

section \<open>Direct target-exponent closure from project H1-zero data\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_h1_zero_pair_target_limit:
  assumes a_lower: "1 < a"
    and a_upper: "a < 2"
    and X_measurable: "X \<in> sets (lborel :: slp_point measure)"
    and X_bounded: "bounded X"
    and zero_h1: "slp_h1_zero_pair_on X u Du"
  shows "aim_complex_lp_on_plane (aim_hls_target_exponent a)
      (slp_restrict_field X u) \<and>
    (\<exists>psi :: nat \<Rightarrow> slp_scalar_field.
      (\<forall>n. slp_test_function_on X (psi n) \<and>
        slp_w1p_pair_on a X (psi n) (slp_classical_gradient (psi n))) \<and>
      (\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
        slp_w1p_norm_on a X
          (\<lambda>x. psi n x - u x)
          (\<lambda>x. slp_classical_gradient (psi n) x - Du x) < epsilon) \<and>
      (\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
        aim_complex_lp_norm (aim_hls_target_exponent a)
          (\<lambda>x. psi n x - slp_restrict_field X u x) < epsilon))"
proof -
  have zero_a: "slp_w1p_zero_pair_on a X u Du"
    by (rule slp_h1_zero_pair_on_w1p_zero_pair_on_below_two[
          OF a_lower a_upper X_measurable X_bounded zero_h1])
  show ?thesis
    by (rule slp_w1p_zero_pair_target_limit[
          OF a_lower a_upper zero_a])
qed

end

end
