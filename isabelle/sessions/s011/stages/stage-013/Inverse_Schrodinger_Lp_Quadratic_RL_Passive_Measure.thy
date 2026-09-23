theory Inverse_Schrodinger_Lp_Quadratic_RL_Passive_Measure
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Quadratic_RL_Passive_Affine"
begin

section \<open>Quadratic oscillation with a sigma-finite passive measure\<close>

lemma slp_product_affine_quadratic_phase_integrable_measure:
  fixes M :: "'c measure" and A :: "real^'n::finite^'n"
    and b :: "'c \<Rightarrow> real^'n"
    and p0 :: "'c \<Rightarrow> real"
    and F :: "'c \<Rightarrow> real^'n \<Rightarrow> complex"
    and omega :: real
  assumes b_measurable: "b \<in> borel_measurable M"
    and p0_measurable: "p0 \<in> borel_measurable M"
    and F_integrable: "integrable (M \<Otimes>\<^sub>M lborel) (case_prod F)"
  shows "integrable (M \<Otimes>\<^sub>M lborel)
    (\<lambda>(c,u). exp (\<i> * of_real
      (omega * (inner u (A *v u) / 2 + inner (b c) u + p0 c))) * F c u)"
proof (rule Bochner_Integration.integrable_bound[OF F_integrable])
  have F_measurable:
    "case_prod F \<in> borel_measurable (M \<Otimes>\<^sub>M lborel)"
    using F_integrable by measurable
  have matrix_continuous: "continuous_on UNIV ((*v) A)"
    by (rule matrix_vector_mult_linear_continuous_on)
  have quadratic_continuous: "continuous_on UNIV (\<lambda>u. inner u (A *v u))"
    by (intro continuous_on_inner continuous_on_id matrix_continuous)
  have quadratic_half_continuous:
    "continuous_on UNIV (\<lambda>u. inner u (A *v u) / 2)"
    by (intro continuous_intros quadratic_continuous) simp
  have quadratic_measurable:
    "(\<lambda>u. inner u (A *v u) / 2) \<in> borel_measurable lborel"
    using borel_measurable_continuous_onI[OF quadratic_half_continuous] by simp
  have phase_measurable:
    "(\<lambda>(c,u). exp (\<i> * of_real
      (omega * (inner u (A *v u) / 2 + inner (b c) u + p0 c))))
      \<in> borel_measurable (M \<Otimes>\<^sub>M lborel)"
    using quadratic_measurable b_measurable p0_measurable by measurable
  show "(\<lambda>(c,u). exp (\<i> * of_real
      (omega * (inner u (A *v u) / 2 + inner (b c) u + p0 c))) * F c u)
      \<in> borel_measurable (M \<Otimes>\<^sub>M lborel)"
    using phase_measurable F_measurable by measurable
  show "AE x in M \<Otimes>\<^sub>M lborel.
    norm ((\<lambda>(c,u). exp (\<i> * of_real
      (omega * (inner u (A *v u) / 2 + inner (b c) u + p0 c))) * F c u) x)
      \<le> norm (case_prod F x)"
    by (simp only: split_beta norm_mult norm_exp_i_times mult_1_left
        order_refl eventually_True)
qed

context hormander_quadratic_stationary_phase_decay
begin

theorem slp_passive_affine_quadratic_decay_measure:
  fixes M :: "'c measure" and A :: "real^'n::finite^'n"
    and b :: "'c \<Rightarrow> real^'n"
    and p0 :: "'c \<Rightarrow> real"
    and F :: "'c \<Rightarrow> real^'n \<Rightarrow> complex"
  assumes M_sigma: "sigma_finite_measure M"
    and density: "evans_compact_smooth_l1_density_claim TYPE('n)"
    and symmetric: "hormander_real_symmetric_matrix A"
    and nondegenerate: "hormander_real_nondegenerate_matrix A"
    and b_measurable: "b \<in> borel_measurable M"
    and p0_measurable: "p0 \<in> borel_measurable M"
    and F_integrable: "integrable (M \<Otimes>\<^sub>M lborel) (case_prod F)"
  shows "((\<lambda>omega::real. integral\<^sup>L (M \<Otimes>\<^sub>M lborel)
      (\<lambda>(c,u). exp (\<i> * of_real
        (omega * (inner u (A *v u) / 2 + inner (b c) u + p0 c))) * F c u))
    \<longlongrightarrow> 0) at_top"
proof -
  interpret passive_measure: sigma_finite_measure M by (rule M_sigma)
  interpret pair: pair_sigma_finite M "lborel :: (real^'n) measure" ..
  let ?slice = "\<lambda>omega c. integral\<^sup>L lborel
    (\<lambda>u. exp (\<i> * of_real
      (omega * (inner u (A *v u) / 2 + inner (b c) u + p0 c))) * F c u)"
  let ?bound = "\<lambda>c. integral\<^sup>L lborel (\<lambda>u. norm (F c u))"
  have AE_slice_integrable: "AE c in M. integrable lborel (F c)"
    using pair.AE_integrable_fst[OF F_integrable] .
  have norm_product_integrable:
    "integrable (M \<Otimes>\<^sub>M lborel) (\<lambda>x. norm (case_prod F x))"
    by (rule Bochner_Integration.integrable_norm[OF F_integrable])
  have bound_integrable: "integrable M ?bound"
    using pair.integrable_fst'[OF norm_product_integrable]
    by (simp only: fst_conv snd_conv case_prod_conv)
  have product_integrable: "integrable (M \<Otimes>\<^sub>M lborel)
    (\<lambda>(c,u). exp (\<i> * of_real
      (omega * (inner u (A *v u) / 2 + inner (b c) u + p0 c))) * F c u)"
    for omega
    by (rule slp_product_affine_quadratic_phase_integrable_measure[
        OF b_measurable p0_measurable F_integrable])
  have slice_integrable: "integrable M (?slice omega)" for omega
    using pair.integrable_fst[OF product_integrable[of omega]] by simp
  have slice_measurable: "?slice omega \<in> borel_measurable M" for omega
    using slice_integrable[of omega] by measurable
  have slice_decay: "AE c in M.
    ((\<lambda>omega. ?slice omega c) \<longlongrightarrow> 0) at_top"
    using AE_slice_integrable
  proof eventually_elim
    fix c
    assume c_integrable: "integrable lborel (F c)"
    show "((\<lambda>omega. ?slice omega c) \<longlongrightarrow> 0) at_top"
      by (rule slp_quadratic_decay_affine[
          OF density symmetric nondegenerate c_integrable])
  qed
  have slice_bound: "norm (?slice omega c) \<le> ?bound c" for omega c
  proof -
    have "norm (?slice omega c) \<le> integral\<^sup>L lborel
        (\<lambda>u. norm (exp (\<i> * of_real
          (omega * (inner u (A *v u) / 2 + inner (b c) u + p0 c))) * F c u))"
      by (rule Bochner_Integration.integral_norm_bound)
    also have "... = ?bound c"
      by (rule Bochner_Integration.integral_cong[OF refl])
        (simp only: norm_mult norm_exp_i_times mult_1_left)
    finally show ?thesis .
  qed
  have zero_measurable: "(\<lambda>_::'c. (0::complex)) \<in> borel_measurable M"
    by measurable
  have eventual_bound:
    "\<forall>\<^sub>F omega in at_top. AE c in M. norm (?slice omega c) \<le> ?bound c"
    using slice_bound by simp
  have outer_decay: "((\<lambda>omega. integral\<^sup>L M (?slice omega))
      \<longlongrightarrow> integral\<^sup>L M (\<lambda>_::'c. (0::complex))) at_top"
    by (rule integral_dominated_convergence_at_top[OF zero_measurable
        slice_measurable bound_integrable slice_decay eventual_bound])
  have product_as_slices: "integral\<^sup>L (M \<Otimes>\<^sub>M lborel)
      (\<lambda>(c,u). exp (\<i> * of_real
        (omega * (inner u (A *v u) / 2 + inner (b c) u + p0 c))) * F c u)
      = integral\<^sup>L M (?slice omega)" for omega
    using pair.integral_fst[OF product_integrable[of omega]] by simp
  show ?thesis
    using outer_decay
    by (simp only: product_as_slices Bochner_Integration.integral_zero)
qed

end

end
