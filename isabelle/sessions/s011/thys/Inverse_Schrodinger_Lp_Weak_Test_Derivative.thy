theory Inverse_Schrodinger_Lp_Weak_Test_Derivative
  imports Inverse_Schrodinger_Lp_Weak_Test_Multiplier
begin

section \<open>Cartesian derivatives of weak test functions\<close>

lemma slp_complex_partial_derivative_smooth:
  assumes phi_smooth: "smooth_on UNIV phi"
  shows "smooth_on UNIV (slp_complex_partial_derivative phi i)"
  unfolding slp_complex_partial_derivative_def
  by (rule smooth_on_frechet_derivative[OF phi_smooth])

lemma slp_complex_partial_derivative_support_subset:
  assumes phi_smooth: "smooth_on UNIV phi"
  shows "closure {x. slp_complex_partial_derivative phi i x \<noteq> 0}
      \<subseteq> closure {x. phi x \<noteq> 0}"
proof -
  let ?S = "{x. phi x \<noteq> 0}"
  have phi_differentiable: "\<And>x. phi differentiable at x"
    using smooth_on_imp_differentiable_on[OF phi_smooth]
    by (simp add: differentiable_on_def)
  have nonzero_subset:
    "{x. slp_complex_partial_derivative phi i x \<noteq> 0}
      \<subseteq> closure ?S"
  proof
    fix x
    assume partial_nonzero: "x \<in>
      {x. slp_complex_partial_derivative phi i x \<noteq> 0}"
    show "x \<in> closure ?S"
    proof (rule ccontr)
      assume x_not: "x \<notin> closure ?S"
      have complement_open: "open (- closure ?S)"
        by (rule open_Compl[OF closed_closure])
      have x_complement: "x \<in> - closure ?S"
        using x_not by simp
      have phi_zero: "\<And>y. y \<in> - closure ?S \<Longrightarrow> phi y = 0"
        by auto
      have derivative_zero:
        "frechet_derivative phi (at x) =
          frechet_derivative (\<lambda>_::slp_point. 0) (at x)"
        by (rule frechet_derivative_transform_within_open[OF
              phi_differentiable complement_open x_complement phi_zero])
      have "slp_complex_partial_derivative phi i x = 0"
        unfolding slp_complex_partial_derivative_def derivative_zero by simp
      then show False
        using partial_nonzero by simp
    qed
  qed
  have "closure {x. slp_complex_partial_derivative phi i x \<noteq> 0}
      \<subseteq> closure (closure ?S)"
    by (rule closure_mono[OF nonzero_subset])
  then show ?thesis
    by simp
qed

theorem slp_test_function_on_partial_derivative:
  assumes phi_test: "slp_test_function_on U phi"
  shows "slp_test_function_on U (slp_complex_partial_derivative phi i)"
proof -
  have phi_smooth: "smooth_on UNIV phi"
    using phi_test unfolding slp_test_function_on_def by blast
  have phi_compact: "compact (closure {x. phi x \<noteq> 0})"
    using phi_test unfolding slp_test_function_on_def by blast
  have phi_within: "closure {x. phi x \<noteq> 0} \<subseteq> U"
    using phi_test unfolding slp_test_function_on_def by blast
  have derivative_smooth:
    "smooth_on UNIV (slp_complex_partial_derivative phi i)"
    by (rule slp_complex_partial_derivative_smooth[OF phi_smooth])
  have derivative_closure_subset:
    "closure {x. slp_complex_partial_derivative phi i x \<noteq> 0}
      \<subseteq> closure {x. phi x \<noteq> 0}"
    by (rule slp_complex_partial_derivative_support_subset[OF phi_smooth])
  have derivative_compact:
    "compact (closure {x. slp_complex_partial_derivative phi i x \<noteq> 0})"
    by (rule compact_if_closed_subset_of_compact[OF
          closed_closure phi_compact derivative_closure_subset])
  have derivative_within:
    "closure {x. slp_complex_partial_derivative phi i x \<noteq> 0} \<subseteq> U"
    using derivative_closure_subset phi_within by blast
  show ?thesis
    unfolding slp_test_function_on_def
    by (rule conjI[OF derivative_smooth
          conjI[OF derivative_compact derivative_within]])
qed

end
