theory Inverse_Schrodinger_Lp_Cauchy_HLS_Conjugate
  imports Inverse_Schrodinger_Lp_Cauchy_HLS
begin

section \<open>Conjugated Cauchy orientation\<close>

lemma aim_complex_lp_on_plane_cnj_iff [simp]:
  "aim_complex_lp_on_plane p (\<lambda>x. cnj (f x)) \<longleftrightarrow>
    aim_complex_lp_on_plane p f"
proof -
  have conjugate_continuous: "continuous_on UNIV cnj"
    by (rule continuous_on_cnj[OF continuous_on_id])
  have cnj_borel_measurable: "cnj \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF conjugate_continuous])
  have measurable_iff:
    "(\<lambda>x. cnj (f x)) \<in> borel_measurable lborel \<longleftrightarrow>
      f \<in> borel_measurable lborel"
  proof
    assume conjugated_f_measurable:
      "(\<lambda>x. cnj (f x)) \<in> borel_measurable lborel"
    have "(\<lambda>x. cnj (cnj (f x))) \<in> borel_measurable lborel"
      using measurable_comp[OF conjugated_f_measurable cnj_borel_measurable]
      by (simp add: comp_def)
    moreover have "(\<lambda>x. cnj (cnj (f x))) = f"
      by (rule ext) simp
    ultimately show "f \<in> borel_measurable lborel"
      by simp
  next
    assume f_measurable: "f \<in> borel_measurable lborel"
    then show "(\<lambda>x. cnj (f x)) \<in> borel_measurable lborel"
      using measurable_comp[OF f_measurable cnj_borel_measurable]
      by (simp add: comp_def)
  qed
  show ?thesis
    unfolding aim_complex_lp_on_plane_def
    using measurable_iff by simp
qed

lemma aim_complex_lp_norm_cnj [simp]:
  "aim_complex_lp_norm p (\<lambda>x. cnj (f x)) =
    aim_complex_lp_norm p f"
  by (simp add: aim_complex_lp_norm_def)

lemma slp_partial_inverse_via_dbar_conjugate:
  "slp_partial_inverse f =
    (\<lambda>z. cnj (slp_dbar_inverse (\<lambda>y. cnj (f y)) z))"
proof (rule ext)
  fix z
  let ?g = "\<lambda>y. cnj (f y) *
    inverse (slp_point_as_complex z - slp_point_as_complex y)"
  have conjugated_integral:
    "cnj (integral\<^sup>L lborel ?g) =
      integral\<^sup>L lborel
        (\<lambda>y. f y * inverse
          (cnj (slp_point_as_complex z - slp_point_as_complex y)))"
  proof -
    have "cnj (integral\<^sup>L lborel ?g) =
        integral\<^sup>L lborel (\<lambda>y. cnj (?g y))"
      by (rule sym, rule Bochner_Integration.integral_cnj)
    also have "... = integral\<^sup>L lborel
        (\<lambda>y. f y * inverse
          (cnj (slp_point_as_complex z - slp_point_as_complex y)))"
    proof (rule Bochner_Integration.integral_cong)
      show "lborel = lborel"
        by (rule refl)
    next
      fix y :: slp_point
      assume "y \<in> space lborel"
      show "cnj (?g y) =
          f y * inverse
            (cnj (slp_point_as_complex z - slp_point_as_complex y))"
        apply (subst complex_cnj_mult)
        apply (subst complex_cnj_cnj)
        apply (subst complex_cnj_inverse)
        apply (rule refl)
        done
    qed
    finally show ?thesis .
  qed
  show "slp_partial_inverse f z =
    cnj (slp_dbar_inverse (\<lambda>y. cnj (f y)) z)"
    unfolding slp_cauchy_transform_def slp_cauchy_integrand_def
      slp_cauchy_kernel_def slp_cauchy_denominator_def
    using conjugated_integral
    by (simp add: algebra_simps)
qed

context aim_planar_hls_cauchy
begin

theorem slp_partial_inverse_hls:
  "\<exists>C::real. 0 < C \<and>
    (\<forall>p f. 1 < p \<and> p < 2 \<and> aim_complex_lp_on_plane p f
      \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent p)
        (slp_partial_inverse f) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent p)
          (slp_partial_inverse f)
        \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f)"
proof -
  obtain C::real where C_positive: "0 < C"
    and C_bound:
      "\<And>p f. 1 < p \<Longrightarrow> p < 2 \<Longrightarrow>
        aim_complex_lp_on_plane p f \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent p)
            (slp_dbar_inverse f) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent p)
            (slp_dbar_inverse f)
          \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
    using slp_dbar_inverse_hls by blast
  have all_bound:
    "\<forall>p f. 1 < p \<and> p < 2 \<and> aim_complex_lp_on_plane p f
      \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent p)
        (slp_partial_inverse f) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent p)
          (slp_partial_inverse f)
        \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
  proof (intro allI impI)
    fix p f
    assume hypotheses:
      "1 < p \<and> p < 2 \<and> aim_complex_lp_on_plane p f"
    have conjugate_result:
      "aim_complex_lp_on_plane (aim_hls_target_exponent p)
          (slp_dbar_inverse (\<lambda>y. cnj (f y))) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent p)
            (slp_dbar_inverse (\<lambda>y. cnj (f y)))
          \<le> C / ((p - 1) * (2 - p)) *
            aim_complex_lp_norm p (\<lambda>y. cnj (f y))"
      by (rule C_bound) (use hypotheses in auto)
    from conjugate_result show
      "aim_complex_lp_on_plane (aim_hls_target_exponent p)
        (slp_partial_inverse f) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent p)
          (slp_partial_inverse f)
        \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
      by (simp only: slp_partial_inverse_via_dbar_conjugate
          aim_complex_lp_on_plane_cnj_iff aim_complex_lp_norm_cnj)
  qed
  show ?thesis
    using C_positive all_bound by blast
qed

end

end
