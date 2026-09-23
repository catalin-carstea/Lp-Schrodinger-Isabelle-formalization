theory Inverse_Schrodinger_Lp_Smooth_Translation_Interface
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Centered_Smooth_Inverse_Sqrt_HLS"
begin

section \<open>Translation invariance for the smooth center bridge\<close>

lemma slp_aim_complex_lp_on_plane_translate:
  assumes f_lp: "aim_complex_lp_on_plane p f"
  shows
    "aim_complex_lp_on_plane p (\<lambda>x. f (c + x)) \<and>
      aim_complex_lp_norm p (\<lambda>x. f (c + x)) =
        aim_complex_lp_norm p f"
proof -
  have f_measurable: "f \<in> borel_measurable lborel"
    and f_power_integrable:
      "integrable lborel (\<lambda>x. norm (f x) powr p)"
    using f_lp unfolding aim_complex_lp_on_plane_def by blast+
  have translated_measurable:
      "(\<lambda>x. f (c + x)) \<in> borel_measurable lborel"
    using f_measurable by measurable
  have translated_power_integrable:
      "integrable lborel (\<lambda>x. norm (f (c + x)) powr p)"
    by (rule slp_lborel_integrable_translate[OF f_power_integrable])
  have translated_lp:
      "aim_complex_lp_on_plane p (\<lambda>x. f (c + x))"
    unfolding aim_complex_lp_on_plane_def
    by (rule conjI[OF translated_measurable translated_power_integrable])
  have translated_power_integral:
      "integral\<^sup>L lborel (\<lambda>x. norm (f (c + x)) powr p) =
        integral\<^sup>L lborel (\<lambda>x. norm (f x) powr p)"
    by (rule slp_lborel_integral_translate[OF f_power_integrable])
  have translated_norm:
      "aim_complex_lp_norm p (\<lambda>x. f (c + x)) =
        aim_complex_lp_norm p f"
    unfolding aim_complex_lp_norm_def
    by (simp only: translated_power_integral)
  show ?thesis
    by (rule conjI[OF translated_lp translated_norm])
qed

lemma slp_test_function_on_UNIV_translate:
  assumes f_test: "slp_test_function_on UNIV f"
  shows "slp_test_function_on UNIV (\<lambda>x. f (c + x))"
proof -
  have f_smooth: "smooth_on UNIV f"
    and f_support_compact: "compact (closure {x. f x \<noteq> 0})"
    using f_test unfolding slp_test_function_on_def by blast+
  have shift_smooth: "smooth_on UNIV (\<lambda>x :: slp_point. c + x)"
    by (rule smooth_on_add[OF smooth_on_const smooth_on_id open_UNIV])
  have translated_smooth:
      "smooth_on UNIV (\<lambda>x. f (c + x))"
  proof -
    have "smooth_on UNIV (f \<circ> (\<lambda>x :: slp_point. c + x))"
      by (rule smooth_on_compose[OF f_smooth shift_smooth]) auto
    then show ?thesis
      by (simp only: o_def)
  qed
  have f_support_bounded: "bounded (closure {x. f x \<noteq> 0})"
    by (rule compact_imp_bounded[OF f_support_compact])
  have identity_image_bounded:
      "bounded ((\<lambda>y. y) ` closure {x. f x \<noteq> 0})"
    using f_support_bounded by simp
  have constant_image_bounded:
    "bounded ((\<lambda>y. c) ` closure {x. f x \<noteq> 0})"
  proof (rule finite_imp_bounded)
    show "finite ((\<lambda>y. c) ` closure {x. f x \<noteq> 0})"
    proof (rule finite_subset[of _ "{c}"])
      show "finite {c}"
        by simp
      show "(\<lambda>y. c) ` closure {x. f x \<noteq> 0} \<subseteq> {c}"
        by auto
    qed
  qed
  have translated_image_bounded:
      "bounded ((\<lambda>y. y - c) ` closure {x. f x \<noteq> 0})"
    by (rule bounded_minus_comp[OF identity_image_bounded
          constant_image_bounded])
  have translated_nonzero_subset:
      "{x. f (c + x) \<noteq> 0} \<subseteq>
        (\<lambda>y. y - c) ` closure {x. f x \<noteq> 0}"
  proof
    fix x
    assume x_nonzero: "x \<in> {x. f (c + x) \<noteq> 0}"
    have translated_in_support:
        "c + x \<in> closure {y. f y \<noteq> 0}"
      by (rule subsetD[OF closure_subset]) (use x_nonzero in simp)
    show "x \<in> (\<lambda>y. y - c) ` closure {x. f x \<noteq> 0}"
      by (rule image_eqI[where x="c + x"])
        (use translated_in_support in simp_all)
  qed
  have translated_nonzero_bounded:
      "bounded {x. f (c + x) \<noteq> 0}"
    by (rule bounded_subset[OF translated_image_bounded
          translated_nonzero_subset])
  have translated_support_bounded:
      "bounded (closure {x. f (c + x) \<noteq> 0})"
    by (rule bounded_closure[OF translated_nonzero_bounded])
  have translated_support_compact:
      "compact (closure {x. f (c + x) \<noteq> 0})"
    using translated_support_bounded
    by (simp add: compact_eq_bounded_closed)
  show ?thesis
    unfolding slp_test_function_on_def
    using translated_smooth translated_support_compact by simp
qed

lemma slp_classical_wirtinger_partial_translate:
  assumes f_smooth: "smooth_on UNIV f"
  shows
    "slp_classical_wirtinger_partial (\<lambda>x. f (c + x)) z =
      slp_classical_wirtinger_partial f (c + z)"
proof -
  have f_differentiable: "f differentiable at (c + z)"
    using smooth_on_imp_differentiable_on[OF f_smooth]
    by (simp add: differentiable_on_def)
  have shift_has_derivative:
      "((\<lambda>x :: slp_point. c + x) has_derivative id) (at z)"
  proof -
    have function_eq:
        "(\<lambda>x :: slp_point. c + x) = (\<lambda>x. id x + c)"
      by (rule ext) (simp only: id_apply add.commute)
    show ?thesis
      unfolding function_eq
      by (rule has_derivative_add_const[OF has_derivative_id])
  qed
  have shift_differentiable:
      "(\<lambda>x :: slp_point. c + x) differentiable at z"
    by (rule differentiableI[OF shift_has_derivative])
  have shift_frechet:
      "frechet_derivative (\<lambda>x :: slp_point. c + x) (at z) = id"
    by (rule sym, rule frechet_derivative_at[OF shift_has_derivative])
  have chain:
      "frechet_derivative (f \<circ> (\<lambda>x :: slp_point. c + x))
          (at z) =
        frechet_derivative f (at (c + z)) \<circ>
          frechet_derivative (\<lambda>x :: slp_point. c + x) (at z)"
    by (rule frechet_derivative_compose[OF shift_differentiable
          f_differentiable])
  have translated_partial:
      "slp_complex_partial_derivative (\<lambda>x. f (c + x)) i z =
        slp_complex_partial_derivative f i (c + z)" for i
    unfolding slp_complex_partial_derivative_def
    using chain shift_frechet by (simp add: o_def)
  show ?thesis
    unfolding slp_classical_wirtinger_partial_def
    by (simp only: translated_partial)
qed

end
