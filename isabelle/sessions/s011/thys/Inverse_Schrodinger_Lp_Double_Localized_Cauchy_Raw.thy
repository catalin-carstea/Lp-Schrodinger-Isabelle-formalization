theory Inverse_Schrodinger_Lp_Double_Localized_Cauchy_Raw
  imports Inverse_Schrodinger_Lp_Double_Localized_Cauchy_L1
begin

section \<open>Raw two-kernel product and almost-everywhere fibers\<close>

theorem slp_double_localized_cauchy_raw_product_integrable:
  "integrable (lborel \<Otimes>\<^sub>M lborel)
    (\<lambda>(y, x).
      slp_localized_cauchy_kernel R y *
        slp_localized_cauchy_kernel R (x - y))"
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
  show ?thesis
    by (rule lborel_pair.Fubini_integrable[
          OF F_measurable iterated_integrable fibers_integrable])
qed

corollary slp_double_localized_cauchy_raw_AE_integrable:
  "AE x in lborel.
    integrable lborel
      (\<lambda>y.
        slp_localized_cauchy_kernel R y *
          slp_localized_cauchy_kernel R (x - y))"
proof -
  have product_integrable:
      "integrable (lborel \<Otimes>\<^sub>M lborel)
        (case_prod (\<lambda>y x.
          slp_localized_cauchy_kernel R y *
            slp_localized_cauchy_kernel R (x - y)))"
    using slp_double_localized_cauchy_raw_product_integrable[of R]
    by simp
  show ?thesis
    using lborel_pair.AE_integrable_snd[
      where f = "\<lambda>y x.
        slp_localized_cauchy_kernel R y *
          slp_localized_cauchy_kernel R (x - y)",
      OF product_integrable]
    by simp
qed

corollary slp_double_localized_cauchy_raw_AE_nn_integral:
  "AE x in lborel.
    (\<integral>\<^sup>+ y.
      ennreal
        (slp_localized_cauchy_kernel R y *
          slp_localized_cauchy_kernel R (x - y))
      \<partial>lborel) =
      ennreal (slp_double_localized_cauchy_kernel R x)"
  using slp_double_localized_cauchy_raw_AE_integrable[of R]
proof eventually_elim
  fix x :: slp_point
  assume fiber_integrable:
      "integrable lborel
        (\<lambda>y.
          slp_localized_cauchy_kernel R y *
            slp_localized_cauchy_kernel R (x - y))"
  have raw_nonnegative:
      "0 \<le>
        slp_localized_cauchy_kernel R y *
          slp_localized_cauchy_kernel R (x - y)" for y
    by (intro mult_nonneg_nonneg slp_localized_cauchy_kernel_nonnegative)
  have nn_eq:
      "(\<integral>\<^sup>+ y.
        ennreal
          (slp_localized_cauchy_kernel R y *
            slp_localized_cauchy_kernel R (x - y))
        \<partial>lborel) =
        ennreal
          (\<integral>y.
            slp_localized_cauchy_kernel R y *
              slp_localized_cauchy_kernel R (x - y)
            \<partial>lborel)"
    by (rule nn_integral_eq_integral[OF fiber_integrable])
       (simp add: raw_nonnegative)
  show "(\<integral>\<^sup>+ y.
      ennreal
        (slp_localized_cauchy_kernel R y *
          slp_localized_cauchy_kernel R (x - y))
      \<partial>lborel) =
      ennreal (slp_double_localized_cauchy_kernel R x)"
    using nn_eq
    unfolding slp_double_localized_cauchy_kernel_def
      slp_real_convolution_def
    by simp
qed

end
