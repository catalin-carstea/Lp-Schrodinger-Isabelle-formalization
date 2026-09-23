theory Inverse_Schrodinger_Lp_CGO_Born_Remainder_Norm
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_CGO_Born_Finite_Expansion"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Pointwise norm control of the nonlinear Neumann remainder\<close>

theorem slp_cgo_born_neumann_remainder_norm_le:
  fixes left_prefix_bound left_tail_bound :: real
    and right_prefix_bound right_tail_bound :: real
  assumes left_prefix:
      "norm (slp_left_neumann_partial_sum X N tau c cutoff coefficient z)
        \<le> left_prefix_bound"
    and left_tail:
      "norm (slp_left_neumann_series_tail X N tau c cutoff coefficient z)
        \<le> left_tail_bound"
    and right_prefix:
      "norm (slp_right_neumann_partial_sum X M tau c cutoff
        coefficient_tilde z) \<le> right_prefix_bound"
    and right_tail:
      "norm (slp_right_neumann_series_tail X M tau c cutoff
        coefficient_tilde z) \<le> right_tail_bound"
  shows
    "norm (slp_cgo_born_neumann_remainder X N M tau c cutoff
        coefficient coefficient_tilde z) \<le>
      left_tail_bound + right_tail_bound +
      left_prefix_bound * right_tail_bound +
      left_tail_bound * right_prefix_bound +
      left_tail_bound * right_tail_bound"
proof -
  let ?lp =
    "slp_left_neumann_partial_sum X N tau c cutoff coefficient z"
  let ?lt =
    "slp_left_neumann_series_tail X N tau c cutoff coefficient z"
  let ?rp =
    "slp_right_neumann_partial_sum X M tau c cutoff coefficient_tilde z"
  let ?rt =
    "slp_right_neumann_series_tail X M tau c cutoff coefficient_tilde z"
  let ?phase = "slp_center_kernel (- tau) c z"
  have lp_nonnegative: "0 \<le> left_prefix_bound"
    by (rule order_trans[OF norm_ge_zero left_prefix])
  have lt_nonnegative: "0 \<le> left_tail_bound"
    by (rule order_trans[OF norm_ge_zero left_tail])
  have rp_nonnegative: "0 \<le> right_prefix_bound"
    by (rule order_trans[OF norm_ge_zero right_prefix])
  have rt_nonnegative: "0 \<le> right_tail_bound"
    by (rule order_trans[OF norm_ge_zero right_tail])
  have lp_rt:
      "norm (?lp * ?rt) \<le> left_prefix_bound * right_tail_bound"
    unfolding norm_mult
    by (rule mult_mono[OF left_prefix right_tail])
      (use norm_ge_zero lp_nonnegative in simp_all)
  have lt_rp:
      "norm (?lt * ?rp) \<le> left_tail_bound * right_prefix_bound"
    unfolding norm_mult
    by (rule mult_mono[OF left_tail right_prefix])
      (use norm_ge_zero lt_nonnegative in simp_all)
  have lt_rt:
      "norm (?lt * ?rt) \<le> left_tail_bound * right_tail_bound"
    unfolding norm_mult
    by (rule mult_mono[OF left_tail right_tail])
      (use norm_ge_zero lt_nonnegative in simp_all)
  have product_triangle:
      "norm (?lp * ?rt + ?lt * ?rp + ?lt * ?rt) \<le>
        norm (?lp * ?rt) + norm (?lt * ?rp) + norm (?lt * ?rt)"
  proof -
    note first = norm_triangle_ineq[of "?lp * ?rt" "?lt * ?rp"]
    note second = norm_triangle_ineq[
      of "?lp * ?rt + ?lt * ?rp" "?lt * ?rt"]
    show ?thesis
      using first second by linarith
  qed
  have product_bound:
      "norm (?lp * ?rt + ?lt * ?rp + ?lt * ?rt) \<le>
        left_prefix_bound * right_tail_bound +
        left_tail_bound * right_prefix_bound +
        left_tail_bound * right_tail_bound"
    using product_triangle lp_rt lt_rp lt_rt by linarith
  have phase_product:
      "norm (?phase * (?lp * ?rt + ?lt * ?rp + ?lt * ?rt)) =
        norm (?lp * ?rt + ?lt * ?rp + ?lt * ?rt)"
    by (simp only: norm_mult slp_center_kernel_norm mult_1_left)
  have outer_triangle:
      "norm (?lt + ?rt +
          ?phase * (?lp * ?rt + ?lt * ?rp + ?lt * ?rt)) \<le>
        norm ?lt + norm ?rt +
        norm (?lp * ?rt + ?lt * ?rp + ?lt * ?rt)"
  proof -
    note first = norm_triangle_ineq[of ?lt ?rt]
    note second = norm_triangle_ineq[
      of "?lt + ?rt" "?phase * (?lp * ?rt + ?lt * ?rp + ?lt * ?rt)"]
    show ?thesis
      using first second phase_product by linarith
  qed
  show ?thesis
    unfolding slp_cgo_born_neumann_remainder_def
    using outer_triangle left_tail right_tail product_bound
    by linarith
qed

end
