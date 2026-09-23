theory Inverse_Schrodinger_Lp_Qstar_Smooth_Far_Pointwise_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Qstar_Smooth_Far_Derivative"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Far_Product_Bound"
begin

section \<open>The canonical pointwise bound for the smooth far derivative\<close>

theorem slp_global_far_product_classical_partial_norm_bound:
  assumes delta_positive: "0 < delta"
    and f_test: "slp_test_function_on UNIV f"
    and distance: "delta \<le> norm (z - c)"
  shows
    "norm (slp_classical_wirtinger_partial
        (slp_global_cutoff.slp_far_product delta c f) z) \<le>
      (2 / delta) * norm (slp_classical_wirtinger_partial f z) +
      (slp_global_cutoff_L / delta ^ 2) * norm (f z) +
      (2 / delta ^ 2) * norm (f z)"
proof -
  have away_from_center: "z \<noteq> c"
  proof
    assume "z = c"
    with distance delta_positive show False by simp
  qed
  note derivative = slp_global_far_product_partial_three_term[
      OF delta_positive f_test away_from_center]
  note abstract_bound =
    slp_global_cutoff.slp_far_product_partial_norm_bound[
      OF delta_positive distance,
      where f = f and Df = "frechet_derivative f (at z)"]
  show ?thesis
    apply (subst derivative)
    unfolding slp_classical_wirtinger_partial_frechet
    by (rule abstract_bound[unfolded
          slp_global_cutoff.slp_far_product_partial])
qed

end
