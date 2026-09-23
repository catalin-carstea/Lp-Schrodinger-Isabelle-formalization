theory Inverse_Schrodinger_Lp_Qstar_Cutoff_Partial_Support
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Far_Coefficient_Bounds"
begin

section \<open>Annular support of the scaled-cutoff Wirtinger derivative\<close>

context slp_cutoff_profile
begin

lemma slp_scaled_cutoff_partial_support:
  assumes delta_positive: "0 < delta"
    and partial_nonzero:
      "slp_real_wirtinger_partial
        (slp_scaled_cutoff_derivative delta c z) \<noteq> 0"
  shows "delta \<le> norm (z - c) \<and> norm (z - c) \<le> 2 * delta"
proof -
  consider
    (coordinate_zero) "slp_scaled_cutoff_derivative delta c z
      (axis (0 :: 2) 1) \<noteq> 0"
  | (coordinate_one) "slp_scaled_cutoff_derivative delta c z
      (axis (1 :: 2) 1) \<noteq> 0"
    using partial_nonzero
    unfolding slp_real_wirtinger_partial_def
    by auto
  then show ?thesis
  proof cases
    case coordinate_zero
    show ?thesis
      by (rule slp_scaled_cutoff_derivative_support[OF
            delta_positive coordinate_zero])
  next
    case coordinate_one
    show ?thesis
      by (rule slp_scaled_cutoff_derivative_support[OF
            delta_positive coordinate_one])
  qed
qed

end

end
