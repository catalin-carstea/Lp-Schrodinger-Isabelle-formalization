theory Inverse_Schrodinger_Lp_Quadratic_RL_Passive
  imports
    Inverse_Schrodinger_Lp_Quadratic_RL_Density
begin

section \<open>Passive-center quadratic decay\<close>

lemma slp_product_quadratic_phase_integrable:
  fixes A :: "real^'n::finite^'n"
    and F :: "real^'c::finite \<Rightarrow> real^'n \<Rightarrow> complex"
    and omega :: real
  assumes F_integrable:
    "integrable (lborel \<Otimes>\<^sub>M lborel) (case_prod F)"
  shows "integrable (lborel \<Otimes>\<^sub>M lborel)
    (\<lambda>(c, u). exp (\<i> * of_real
      (omega * inner u (A *v u) / 2)) * F c u)"
proof (rule Bochner_Integration.integrable_bound[OF F_integrable])
  have F_measurable:
    "case_prod F \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using F_integrable by measurable
  have matrix_continuous: "continuous_on UNIV ((*v) A)"
    by (rule matrix_vector_mult_linear_continuous_on)
  have quadratic_continuous:
    "continuous_on UNIV (\<lambda>u. inner u (A *v u))"
    by (intro continuous_on_inner continuous_on_id matrix_continuous)
  have phase_continuous:
    "continuous_on UNIV
      (\<lambda>u. exp (\<i> * of_real
        (omega * inner u (A *v u) / 2)))"
    by (intro continuous_intros quadratic_continuous) simp
  have phase_measurable:
    "(\<lambda>u. exp (\<i> * of_real
      (omega * inner u (A *v u) / 2))) \<in> borel_measurable lborel"
    using borel_measurable_continuous_onI[OF phase_continuous] by simp
  show "(\<lambda>(c, u). exp (\<i> * of_real
      (omega * inner u (A *v u) / 2)) * F c u)
      \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using F_measurable phase_measurable by measurable
  show "AE x in lborel \<Otimes>\<^sub>M lborel.
      norm ((\<lambda>(c, u). exp (\<i> * of_real
        (omega * inner u (A *v u) / 2)) * F c u) x)
      \<le> norm (case_prod F x)"
    by (simp only: split_beta norm_mult norm_exp_i_times mult_1_left
        order_refl eventually_True)
qed

context hormander_quadratic_stationary_phase_decay
begin

lemma slp_passive_quadratic_decay:
  fixes A :: "real^'n::finite^'n"
    and F :: "real^'c::finite \<Rightarrow> real^'n \<Rightarrow> complex"
  assumes density:
      "evans_compact_smooth_l1_density_claim TYPE('n)"
    and symmetric: "hormander_real_symmetric_matrix A"
    and nondegenerate: "hormander_real_nondegenerate_matrix A"
    and F_integrable:
      "integrable (lborel \<Otimes>\<^sub>M lborel) (case_prod F)"
  shows
    "((\<lambda>omega. integral\<^sup>L (lborel \<Otimes>\<^sub>M lborel)
        (\<lambda>(c, u). exp (\<i> * of_real
          (omega * inner u (A *v u) / 2)) * F c u))
      \<longlongrightarrow> 0) at_top"
proof -
  let ?slice = "\<lambda>omega c.
    hormander_quadratic_oscillatory_integral A (F c) omega"
  let ?bound = "\<lambda>c. integral\<^sup>L lborel (\<lambda>u. norm (F c u))"

  have AE_slice_integrable:
    "AE c in lborel. integrable lborel (F c)"
    using lborel_pair.AE_integrable_fst[OF F_integrable] .
  have norm_product_integrable:
    "integrable (lborel \<Otimes>\<^sub>M lborel)
      (\<lambda>x. norm (case_prod F x))"
    using Bochner_Integration.integrable_norm[OF F_integrable]
    by blast
  have bound_integrable: "integrable lborel ?bound"
    using lborel_pair.integrable_fst'[OF norm_product_integrable]
    by (simp only: fst_conv snd_conv case_prod_conv)

  have product_integrable:
    "integrable (lborel \<Otimes>\<^sub>M lborel)
      (\<lambda>(c, u). exp (\<i> * of_real
        (omega * inner u (A *v u) / 2)) * F c u)" for omega
    using slp_product_quadratic_phase_integrable[where A=A and F=F
      and omega=omega, OF F_integrable] .
  have slice_integrable: "integrable lborel (?slice omega)" for omega
    using lborel_pair.integrable_fst[OF product_integrable[of omega]]
    unfolding hormander_quadratic_oscillatory_integral_def by simp
  have slice_measurable:
    "?slice omega \<in> borel_measurable lborel" for omega
    using slice_integrable[of omega] by measurable

  have slice_decay:
    "AE c in lborel. ((\<lambda>omega. ?slice omega c) \<longlongrightarrow> 0) at_top"
    using AE_slice_integrable
  proof eventually_elim
    fix c
    assume c_integrable: "integrable lborel (F c)"
    show "((\<lambda>omega. ?slice omega c) \<longlongrightarrow> 0) at_top"
      using slp_quadratic_decay_integrable[where A=A and F="F c",
        OF density symmetric nondegenerate c_integrable] .
  qed

  have slice_bound:
    "norm (?slice omega c) \<le> ?bound c" for omega c
  proof -
    have
      "norm (integral\<^sup>L lborel
        (\<lambda>u. exp (\<i> * of_real
          (omega * inner u (A *v u) / 2)) * F c u))
      \<le> integral\<^sup>L lborel
        (\<lambda>u. norm (exp (\<i> * of_real
          (omega * inner u (A *v u) / 2)) * F c u))"
      by (rule Bochner_Integration.integral_norm_bound)
    also have "... = ?bound c"
      by (intro Bochner_Integration.integral_cong[OF refl])
        (simp only: norm_mult norm_exp_i_times mult_1_left)
    finally show ?thesis
      unfolding hormander_quadratic_oscillatory_integral_def .
  qed

  have outer_decay:
    "((\<lambda>omega. integral\<^sup>L lborel (?slice omega))
      \<longlongrightarrow> integral\<^sup>L lborel (\<lambda>_. 0)) at_top"
  proof (rule tendsto_at_topI_sequentially)
    fix X :: "nat \<Rightarrow> real"
    assume X_at_top: "filterlim X at_top sequentially"
    have zero_measurable:
      "(\<lambda>_ :: real^'c. (0 :: complex)) \<in> borel_measurable lborel"
      by simp
    have sequence_measurable:
      "(\<lambda>c. ?slice (X n) c) \<in> borel_measurable lborel" for n
      by (rule slice_measurable)
    have sequence_limit:
      "AE c in lborel. (\<lambda>n. ?slice (X n) c) \<longlonglongrightarrow> 0"
      using slice_decay
    proof eventually_elim
      fix c
      assume c_decay:
        "((\<lambda>omega. ?slice omega c) \<longlongrightarrow> 0) at_top"
      show "(\<lambda>n. ?slice (X n) c) \<longlonglongrightarrow> 0"
        using c_decay X_at_top by (rule filterlim_compose)
    qed
    have sequence_bound:
      "\<And>n. AE c in lborel. norm (?slice (X n) c) \<le> ?bound c"
      using slice_bound by simp
    show "(\<lambda>n. integral\<^sup>L lborel (?slice (X n)))
        \<longlonglongrightarrow> integral\<^sup>L lborel (\<lambda>_. 0)"
      using Bochner_Integration.integral_dominated_convergence[
        OF zero_measurable sequence_measurable bound_integrable
          sequence_limit sequence_bound]
      by (simp only: Bochner_Integration.integral_zero)
  qed

  have product_as_slices:
    "integral\<^sup>L (lborel \<Otimes>\<^sub>M lborel)
        (\<lambda>(c, u). exp (\<i> * of_real
          (omega * inner u (A *v u) / 2)) * F c u)
      = integral\<^sup>L lborel (?slice omega)" for omega
    using lborel_pair.integral_fst[OF product_integrable[of omega]]
    unfolding hormander_quadratic_oscillatory_integral_def by simp

  show ?thesis
    using outer_decay
    by (simp only: product_as_slices Bochner_Integration.integral_zero)
qed

end

end
