theory Inverse_Schrodinger_Lp_Weak_Test_Multiplier
  imports Inverse_Schrodinger_Lp_Cauchy_Weak_Wirtinger
begin

section \<open>Smooth multipliers of weak test functions\<close>

lemma slp_complex_partial_derivative_mult:
  assumes a_smooth: "smooth_on UNIV a"
    and phi_smooth: "smooth_on UNIV phi"
  shows "slp_complex_partial_derivative (\<lambda>y. a y * phi y) i x =
    a x * slp_complex_partial_derivative phi i x +
      slp_complex_partial_derivative a i x * phi x"
proof -
  have a_differentiable: "a differentiable at x"
    using smooth_on_imp_differentiable_on[OF a_smooth]
    by (simp add: differentiable_on_def)
  have phi_differentiable: "phi differentiable at x"
    using smooth_on_imp_differentiable_on[OF phi_smooth]
    by (simp add: differentiable_on_def)
  have a_derivative:
    "(a has_derivative frechet_derivative a (at x)) (at x)"
    using a_differentiable
    by (simp only: frechet_derivative_works)
  have phi_derivative:
    "(phi has_derivative frechet_derivative phi (at x)) (at x)"
    using phi_differentiable
    by (simp only: frechet_derivative_works)
  have product_derivative:
    "((\<lambda>y. a y * phi y) has_derivative
      (\<lambda>h. a x * frechet_derivative phi (at x) h +
        frechet_derivative a (at x) h * phi x)) (at x)"
    by (rule has_derivative_mult[OF a_derivative phi_derivative])
  have product_frechet:
    "frechet_derivative (\<lambda>y. a y * phi y) (at x) =
      (\<lambda>h. a x * frechet_derivative phi (at x) h +
        frechet_derivative a (at x) h * phi x)"
    by (rule sym, rule frechet_derivative_at[OF product_derivative])
  show ?thesis
    unfolding slp_complex_partial_derivative_def product_frechet
    by (rule refl)
qed

lemma slp_test_function_on_mult_left:
  assumes a_smooth: "smooth_on UNIV a"
    and phi_test: "slp_test_function_on U phi"
  shows "slp_test_function_on U (\<lambda>x. a x * phi x)"
proof -
  have phi_smooth: "smooth_on UNIV phi"
    using phi_test unfolding slp_test_function_on_def by blast
  have phi_compact: "compact (closure {x. phi x \<noteq> 0})"
    using phi_test unfolding slp_test_function_on_def by blast
  have phi_within: "closure {x. phi x \<noteq> 0} \<subseteq> U"
    using phi_test unfolding slp_test_function_on_def by blast
  have product_smooth: "smooth_on UNIV (\<lambda>x. a x * phi x)"
    by (rule smooth_on_mult[OF a_smooth phi_smooth open_UNIV])
  have nonzero_subset:
    "{x. a x * phi x \<noteq> 0} \<subseteq> {x. phi x \<noteq> 0}"
    by auto
  have closure_subset:
    "closure {x. a x * phi x \<noteq> 0} \<subseteq>
      closure {x. phi x \<noteq> 0}"
    by (rule closure_mono[OF nonzero_subset])
  have product_compact:
    "compact (closure {x. a x * phi x \<noteq> 0})"
    by (rule compact_if_closed_subset_of_compact[OF
          closed_closure phi_compact closure_subset])
  have product_within:
    "closure {x. a x * phi x \<noteq> 0} \<subseteq> U"
    using closure_subset phi_within by blast
  show ?thesis
    unfolding slp_test_function_on_def
    by (rule conjI[OF product_smooth
          conjI[OF product_compact product_within]])
qed

end
