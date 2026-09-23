theory Inverse_Schrodinger_Lp_Annulus_Shell_Additivity
  imports Inverse_Schrodinger_Lp_Squared_Radial_Annulus
begin

section \<open>Monotonicity and multiplicative shell additivity\<close>

lemma slp_squared_radial_annulus_upper_mono:
  assumes delta_positive: "0 < delta"
    and radii: "R \<le> S"
  shows "integral\<^sup>L lborel (slp_squared_radial_annulus delta R) \<le>
    integral\<^sup>L lborel (slp_squared_radial_annulus delta S)"
proof -
  have left_integrable:
    "integrable lborel (slp_squared_radial_annulus delta R)"
    by (rule slp_squared_radial_annulus_integrable[OF delta_positive])
  have right_integrable:
    "integrable lborel (slp_squared_radial_annulus delta S)"
    by (rule slp_squared_radial_annulus_integrable[OF delta_positive])
  show ?thesis
  proof (rule Bochner_Integration.integral_mono[OF left_integrable
        right_integrable])
    fix y :: slp_point
    assume "y \<in> space lborel"
    show "slp_squared_radial_annulus delta R y \<le>
        slp_squared_radial_annulus delta S y"
      unfolding slp_squared_radial_annulus_def
      using radii by auto
  qed
qed

lemma slp_squared_radial_annulus_shell_split:
  assumes a_lower: "1 \<le> a"
    and b_lower: "1 \<le> b"
  shows "integral\<^sup>L lborel (slp_squared_radial_annulus 1 (a * b)) =
      integral\<^sup>L lborel (slp_squared_radial_annulus 1 a) +
      integral\<^sup>L lborel (slp_squared_radial_annulus a (a * b))"
proof -
  have a_nonnegative: "0 \<le> a"
    using a_lower by linarith
  have a_le_product: "a \<le> a * b"
    using mult_left_mono[OF b_lower a_nonnegative] by simp
  have sphere_negligible: "negligible (sphere (0::slp_point) a)"
    by (rule negligible_sphere)
  have sphere_null: "sphere (0::slp_point) a \<in> null_sets lborel"
    using sphere_negligible
    by (auto simp: negligible_iff_null_sets null_sets_completion_iff)
  have outside_sphere:
    "AE y in (lborel :: slp_point measure). y \<notin> sphere 0 a"
    by (rule AE_not_in[OF sphere_null])
  have ae_split:
    "AE y in lborel.
      slp_squared_radial_annulus 1 (a * b) y =
        slp_squared_radial_annulus 1 a y +
        slp_squared_radial_annulus a (a * b) y"
  proof (rule eventually_mono[OF outside_sphere])
    fix y :: slp_point
    assume outside: "y \<notin> sphere 0 a"
    have not_boundary: "norm y \<noteq> a"
      using outside by (simp add: sphere_def dist_norm)
    show "slp_squared_radial_annulus 1 (a * b) y =
        slp_squared_radial_annulus 1 a y +
        slp_squared_radial_annulus a (a * b) y"
      unfolding slp_squared_radial_annulus_def
      using a_lower a_le_product not_boundary
      by (auto split: if_splits; linarith)
  qed
  have left_integrable:
    "integrable lborel (slp_squared_radial_annulus 1 (a * b))"
    by (rule slp_squared_radial_annulus_integrable) simp
  have inner_integrable:
    "integrable lborel (slp_squared_radial_annulus 1 a)"
    by (rule slp_squared_radial_annulus_integrable) simp
  have shell_integrable:
    "integrable lborel (slp_squared_radial_annulus a (a * b))"
    by (rule slp_squared_radial_annulus_integrable)
      (use a_lower in linarith)
  have integral_congruence:
    "integral\<^sup>L lborel (slp_squared_radial_annulus 1 (a * b)) =
      integral\<^sup>L lborel
        (\<lambda>y. slp_squared_radial_annulus 1 a y +
          slp_squared_radial_annulus a (a * b) y)"
  proof (rule integral_cong_AE)
    show "slp_squared_radial_annulus 1 (a * b)
        \<in> borel_measurable lborel"
      by (rule slp_squared_radial_annulus_borel_measurable)
    show "(\<lambda>y. slp_squared_radial_annulus 1 a y +
          slp_squared_radial_annulus a (a * b) y)
        \<in> borel_measurable lborel"
      by measurable
    show "AE y in lborel.
      slp_squared_radial_annulus 1 (a * b) y =
        slp_squared_radial_annulus 1 a y +
        slp_squared_radial_annulus a (a * b) y"
      by (rule ae_split)
  qed
  have integral_additivity:
    "integral\<^sup>L lborel
        (\<lambda>y. slp_squared_radial_annulus 1 a y +
          slp_squared_radial_annulus a (a * b) y) =
      integral\<^sup>L lborel (slp_squared_radial_annulus 1 a) +
        integral\<^sup>L lborel (slp_squared_radial_annulus a (a * b))"
    using inner_integrable shell_integrable by simp
  show ?thesis
    using integral_congruence integral_additivity by simp
qed

lemma slp_squared_radial_annulus_multiplicative_additivity:
  assumes a_lower: "1 \<le> a"
    and b_lower: "1 \<le> b"
  shows "integral\<^sup>L lborel (slp_squared_radial_annulus 1 (a * b)) =
      integral\<^sup>L lborel (slp_squared_radial_annulus 1 a) +
      integral\<^sup>L lborel (slp_squared_radial_annulus 1 b)"
proof -
  have a_positive: "0 < a"
    using a_lower by linarith
  have shell_split:
    "integral\<^sup>L lborel (slp_squared_radial_annulus 1 (a * b)) =
      integral\<^sup>L lborel (slp_squared_radial_annulus 1 a) +
        integral\<^sup>L lborel (slp_squared_radial_annulus a (a * b))"
    by (rule slp_squared_radial_annulus_shell_split[OF a_lower b_lower])
  have shell_scale:
    "integral\<^sup>L lborel (slp_squared_radial_annulus a (a * b)) =
      integral\<^sup>L lborel (slp_squared_radial_annulus 1 b)"
    using slp_squared_radial_annulus_integral_scale[
        OF a_positive, of 1 b]
    by simp
  show ?thesis
    using shell_split shell_scale by simp
qed

end
