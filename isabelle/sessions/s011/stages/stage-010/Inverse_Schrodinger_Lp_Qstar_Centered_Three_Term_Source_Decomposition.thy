theory Inverse_Schrodinger_Lp_Qstar_Centered_Three_Term_Source_Decomposition
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Far_Amplitude_Derivative_Source"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Centered_Annular_Representation"
begin

section \<open>The centered three-term derivative source\<close>

lemma slp_qstar_centered_far_derivative_source_decomposition:
  assumes delta_positive: "0 < delta"
    and f_test: "slp_test_function_on UNIV f"
    and away_from_center: "y \<noteq> 0"
  shows
    "slp_classical_wirtinger_partial
        (slp_global_cutoff.slp_far_product delta 0 f) y =
      slp_qstar_far_amplitude_derivative_source delta 0 f y -
      slp_qstar_centered_cutoff_partial_source delta f y -
      slp_qstar_centered_square_denominator_source delta f y"
proof -
  note derivative = slp_global_far_product_partial_three_term[
      OF delta_positive f_test away_from_center, unfolded diff_zero]
  show ?thesis
    unfolding slp_qstar_far_amplitude_derivative_source_def
      slp_global_far_coefficient_def
      slp_qstar_centered_cutoff_partial_source_def
      slp_qstar_centered_square_denominator_source_def
    apply (simp only: diff_zero)
    by (rule derivative)
qed

theorem slp_qstar_centered_far_derivative_source_decomposition_AE:
  assumes delta_positive: "0 < delta"
    and f_test: "slp_test_function_on UNIV f"
  shows
    "AE y in (lborel :: slp_point measure).
      slp_classical_wirtinger_partial
          (slp_global_cutoff.slp_far_product delta 0 f) y =
        slp_qstar_far_amplitude_derivative_source delta 0 f y -
        slp_qstar_centered_cutoff_partial_source delta f y -
        slp_qstar_centered_square_denominator_source delta f y"
proof -
  have sphere_negligible: "negligible (sphere (0::slp_point) 0)"
    by (rule negligible_sphere)
  have sphere_null: "sphere (0::slp_point) 0 \<in> null_sets lborel"
    using sphere_negligible
    by (auto simp: negligible_iff_null_sets null_sets_completion_iff)
  have away_from_sphere:
      "AE y in (lborel :: slp_point measure). y \<notin> sphere 0 0"
    by (rule AE_not_in[OF sphere_null])
  show ?thesis
  proof (rule eventually_mono[OF away_from_sphere])
    fix y :: slp_point
    assume outside: "y \<notin> sphere 0 0"
    have away_from_center: "y \<noteq> 0"
      using outside by (simp add: sphere_def)
    show
      "slp_classical_wirtinger_partial
          (slp_global_cutoff.slp_far_product delta 0 f) y =
        slp_qstar_far_amplitude_derivative_source delta 0 f y -
        slp_qstar_centered_cutoff_partial_source delta f y -
        slp_qstar_centered_square_denominator_source delta f y"
      by (rule slp_qstar_centered_far_derivative_source_decomposition[
            OF delta_positive f_test away_from_center])
  qed
qed

end
