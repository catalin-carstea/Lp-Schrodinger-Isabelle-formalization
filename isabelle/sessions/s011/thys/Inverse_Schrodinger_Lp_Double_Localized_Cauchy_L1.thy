theory Inverse_Schrodinger_Lp_Double_Localized_Cauchy_L1
  imports Inverse_Schrodinger_Lp_Localized_Cauchy_L1
begin

section \<open>Ordinary integrability of the double localized kernel\<close>

theorem slp_double_localized_cauchy_kernel_integrable:
  "integrable lborel (slp_double_localized_cauchy_kernel R)"
proof -
  let ?F = "\<lambda>(y, x).
    slp_localized_cauchy_kernel R y *
      slp_localized_cauchy_kernel R (x - y)"
  have F_measurable:
    "?F \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using slp_localized_cauchy_kernel_borel_measurable
    by measurable
  have fibers_integrable:
    "AE y in lborel. integrable lborel (\<lambda>x. ?F (y, x))"
  proof (rule AE_I2)
    fix y :: slp_point
    have translated_integrable:
      "integrable lborel
        (\<lambda>x. slp_localized_cauchy_kernel R (x - y))"
    proof -
      have translated:
        "integrable lborel
          (\<lambda>x. slp_localized_cauchy_kernel R (-y + x))"
        by (rule slp_lborel_integrable_translate[
              OF slp_localized_cauchy_kernel_integrable])
      show ?thesis
        using translated by (simp add: algebra_simps)
    qed
    have scaled_integrable:
      "integrable lborel
        (\<lambda>x. slp_localized_cauchy_kernel R y *
          slp_localized_cauchy_kernel R (x - y))"
      using translated_integrable by (rule integrable_mult_right)
    show "integrable lborel (\<lambda>x. ?F (y, x))"
      using scaled_integrable by simp
  qed
  have translated_integral:
    "(\<integral>x. slp_localized_cauchy_kernel R (x - y) \<partial>lborel) =
      integral\<^sup>L lborel (slp_localized_cauchy_kernel R)" for y
  proof -
    have translated:
      "(\<integral>x. slp_localized_cauchy_kernel R (-y + x) \<partial>lborel) =
        integral\<^sup>L lborel (slp_localized_cauchy_kernel R)"
      by (rule slp_lborel_integral_translate[
            OF slp_localized_cauchy_kernel_integrable])
    show ?thesis
      using translated by (simp add: algebra_simps)
  qed
  have iterated_integrable:
    "integrable lborel
      (\<lambda>y. \<integral>x. norm (?F (y, x)) \<partial>lborel)"
  proof -
    have fiber_eq:
      "(\<lambda>y. \<integral>x. norm (?F (y, x)) \<partial>lborel) =
        (\<lambda>y. slp_localized_cauchy_kernel R y *
          integral\<^sup>L lborel (slp_localized_cauchy_kernel R))"
    proof (rule ext)
      fix y :: slp_point
      have first_nonnegative:
        "0 \<le> slp_localized_cauchy_kernel R y"
        by (rule slp_localized_cauchy_kernel_nonnegative)
      have second_nonnegative:
        "0 \<le> slp_localized_cauchy_kernel R (x - y)" for x
        by (rule slp_localized_cauchy_kernel_nonnegative)
      have norm_eq:
        "(\<lambda>x. norm (?F (y, x))) =
          (\<lambda>x. slp_localized_cauchy_kernel R y *
            slp_localized_cauchy_kernel R (x - y))"
        by (rule ext) (simp add: first_nonnegative second_nonnegative)
      show "(\<integral>x. norm (?F (y, x)) \<partial>lborel) =
          slp_localized_cauchy_kernel R y *
            integral\<^sup>L lborel (slp_localized_cauchy_kernel R)"
        unfolding norm_eq
        by (simp add: translated_integral)
    qed
    show ?thesis
      unfolding fiber_eq
      using slp_localized_cauchy_kernel_integrable by simp
  qed
  have product_integrable:
    "integrable (lborel \<Otimes>\<^sub>M lborel) ?F"
    by (rule lborel_pair.Fubini_integrable[
          OF F_measurable iterated_integrable fibers_integrable])
  have outer_integrable:
    "integrable lborel
      (\<lambda>x. \<integral>y.
        slp_localized_cauchy_kernel R y *
          slp_localized_cauchy_kernel R (x - y) \<partial>lborel)"
    using lborel_pair.integrable_snd[OF product_integrable] .
  show ?thesis
    using outer_integrable
    unfolding slp_double_localized_cauchy_kernel_def
      slp_real_convolution_def .
qed

end
