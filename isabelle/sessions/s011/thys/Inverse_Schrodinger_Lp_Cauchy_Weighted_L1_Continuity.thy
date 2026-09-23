theory Inverse_Schrodinger_Lp_Cauchy_Weighted_L1_Continuity
  imports Inverse_Schrodinger_Lp_Oscillatory_Cauchy_Sequential_Closure
begin

section \<open>Cauchy-transform continuity from weighted L1 convergence\<close>

lemma slp_cauchy_integrand_subtract:
  "slp_cauchy_integrand orientation (\<lambda>x. f x - g x) z y =
    slp_cauchy_integrand orientation f z y -
      slp_cauchy_integrand orientation g z y"
  unfolding slp_cauchy_integrand_def
  by (simp add: algebra_simps)

theorem slp_cauchy_transform_tendsto_of_weighted_L1:
  assumes source_integrable:
      "\<And>n. slp_cauchy_integrable_at orientation (f n) z"
    and target_integrable:
      "slp_cauchy_integrable_at orientation g z"
    and weighted_L1:
      "((\<lambda>n. \<integral>\<^sup>+y.
          norm (slp_cauchy_integrand orientation
            (\<lambda>x. f n x - g x) z y) \<partial>lborel)
        \<longlongrightarrow> 0) F"
  shows "((\<lambda>n. slp_cauchy_transform orientation (f n) z)
    \<longlongrightarrow> slp_cauchy_transform orientation g z) F"
proof -
  have source_integrands:
      "\<And>n. integrable lborel
        (slp_cauchy_integrand orientation (f n) z)"
    using source_integrable
    unfolding slp_cauchy_integrable_at_def .
  have target_integrand:
      "integrable lborel (slp_cauchy_integrand orientation g z)"
    using target_integrable
    unfolding slp_cauchy_integrable_at_def .
  have integrand_L1:
      "((\<lambda>n. \<integral>\<^sup>+y.
          norm (slp_cauchy_integrand orientation (f n) z y -
            slp_cauchy_integrand orientation g z y) \<partial>lborel)
        \<longlongrightarrow> 0) F"
    using weighted_L1
    by (simp only: slp_cauchy_integrand_subtract)
  have integral_limit:
      "((\<lambda>n. integral\<^sup>L lborel
          (slp_cauchy_integrand orientation (f n) z))
        \<longlongrightarrow>
          integral\<^sup>L lborel (slp_cauchy_integrand orientation g z)) F"
    by (rule tendsto_L1_int[OF source_integrands target_integrand
          integrand_L1])
  have scaled_limit:
      "((\<lambda>n. inverse (of_real pi :: complex) *
          integral\<^sup>L lborel
            (slp_cauchy_integrand orientation (f n) z))
        \<longlongrightarrow>
          inverse (of_real pi :: complex) *
            integral\<^sup>L lborel
              (slp_cauchy_integrand orientation g z)) F"
    by (rule tendsto_mult_left[OF integral_limit])
  show ?thesis
    using scaled_limit
    unfolding slp_cauchy_transform_def .
qed

corollary slp_partial_inverse_tendsto_of_weighted_L1:
  assumes source_integrable:
      "\<And>n. slp_cauchy_integrable_at SLP_Partial_Inverse (f n) z"
    and target_integrable:
      "slp_cauchy_integrable_at SLP_Partial_Inverse g z"
    and weighted_L1:
      "((\<lambda>n. \<integral>\<^sup>+y.
          norm (slp_cauchy_integrand SLP_Partial_Inverse
            (\<lambda>x. f n x - g x) z y) \<partial>lborel)
        \<longlongrightarrow> 0) F"
  shows "((\<lambda>n. slp_partial_inverse (f n) z)
    \<longlongrightarrow> slp_partial_inverse g z) F"
  by (rule slp_cauchy_transform_tendsto_of_weighted_L1[OF
        source_integrable target_integrable weighted_L1])

end
