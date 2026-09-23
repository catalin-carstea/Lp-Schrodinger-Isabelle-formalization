theory Inverse_Schrodinger_Lp_Mixed_Product_Duality_Density_Closure
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Mixed_Product_Duality_Exponents"
begin

section \<open>Density closure for the mixed product-error duality argument\<close>

theorem slp_mixed_product_duality_density_closure:
  fixes pairing :: "real \<Rightarrow> 'a::real_normed_vector \<Rightarrow> complex"
    and approximation_size :: "'a \<Rightarrow> real"
    and test_amplitudes :: "'a set"
    and rough_amplitude :: 'a
    and K :: real
  assumes K_positive: "0 < K"
    and size_nonnegative: "\<And>f. 0 \<le> approximation_size f"
    and approximation:
      "\<And>epsilon. 0 < epsilon \<Longrightarrow>
        \<exists>u\<in>test_amplitudes.
          approximation_size (rough_amplitude - u) < epsilon"
    and uniform_remainder:
      "\<And>tau u. u \<in> test_amplitudes \<Longrightarrow>
        Real_Vector_Spaces.norm
          (pairing tau rough_amplitude - pairing tau u) \<le>
          K * approximation_size (rough_amplitude - u)"
    and test_decay:
      "\<And>u. u \<in> test_amplitudes \<Longrightarrow>
        ((\<lambda>tau. pairing tau u) \<longlongrightarrow> 0) at_top"
  shows
    "((\<lambda>tau. pairing tau rough_amplitude) \<longlongrightarrow> 0) at_top"
proof (unfold tendsto_iff, intro allI impI)
  fix epsilon :: real
  assume epsilon_positive: "0 < epsilon"
  let ?delta = "epsilon / (2 * K)"
  have denominator_positive: "0 < 2 * K"
    using K_positive by simp
  have delta_positive: "0 < ?delta"
    using epsilon_positive denominator_positive by (rule divide_pos_pos)
  obtain u where u_test: "u \<in> test_amplitudes"
    and approximation_error:
      "approximation_size (rough_amplitude - u) < ?delta"
    using approximation[OF delta_positive] by blast
  have u_decay:
      "((\<lambda>tau. pairing tau u) \<longlongrightarrow> 0) at_top"
    by (rule test_decay[OF u_test])
  have half_positive: "0 < epsilon / 2"
    using epsilon_positive by simp
  have eventually_u:
      "eventually (\<lambda>tau. dist (pairing tau u) 0 < epsilon / 2) at_top"
    using u_decay half_positive unfolding tendsto_iff by blast
  show
      "eventually
        (\<lambda>tau. dist (pairing tau rough_amplitude) 0 < epsilon) at_top"
    using eventually_u
  proof eventually_elim
    fix tau
    assume u_small: "dist (pairing tau u) 0 < epsilon / 2"
    have remainder_bound:
        "Real_Vector_Spaces.norm
            (pairing tau rough_amplitude - pairing tau u) \<le>
          K * approximation_size (rough_amplitude - u)"
      by (rule uniform_remainder[OF u_test])
    have scaled_error_small:
        "K * approximation_size (rough_amplitude - u) < epsilon / 2"
    proof -
      have
          "K * approximation_size (rough_amplitude - u) < K * ?delta"
        by (rule mult_strict_left_mono[OF approximation_error K_positive])
      also have "... = epsilon / 2"
        using K_positive by simp
      finally show ?thesis .
    qed
    have remainder_small:
        "Real_Vector_Spaces.norm
            (pairing tau rough_amplitude - pairing tau u) < epsilon / 2"
      using remainder_bound scaled_error_small by linarith
    have test_small:
        "Real_Vector_Spaces.norm (pairing tau u) < epsilon / 2"
      using u_small by (simp add: dist_norm)
    have
        "Real_Vector_Spaces.norm (pairing tau rough_amplitude) \<le>
          Real_Vector_Spaces.norm (pairing tau u) +
            Real_Vector_Spaces.norm
              (pairing tau rough_amplitude - pairing tau u)"
      by (rule norm_triangle_sub)
    also have "... < epsilon / 2 + epsilon / 2"
      using test_small remainder_small by linarith
    also have "... = epsilon"
      by simp
    finally show "dist (pairing tau rough_amplitude) 0 < epsilon"
      by (simp add: dist_norm)
  qed
qed

end
