theory Inverse_Schrodinger_Lp_Born_One_Sided_Passive_Root_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_One_Sided_Packed_Residual_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Residual_Cartesian_Integrability"
begin

section \<open>Passive planar-root lift of one-sided residual decay\<close>

lemma slp_one_sided_packed_residual_measurable:
  "(slp_one_sided_packed_residual ::
      real^((unit + ('i::finite + 'i)) \<times> bool) \<Rightarrow> real)
    \<in> borel_measurable lborel"
proof -
  have generic_measurable:
    "(\<lambda>x :: real^((unit + ('i + 'i)) \<times> bool).
        slp_signed_residual slp_one_sided_branch_sign
          (slp_complex_family_unpack x))
      \<in> borel_measurable lborel"
    by (rule slp_signed_residual_cartesian_measurable)
      (rule slp_one_sided_branch_sign_values)
  have residual_function:
    "(slp_one_sided_packed_residual ::
        real^((unit + ('i + 'i)) \<times> bool) \<Rightarrow> real) =
      (\<lambda>x. slp_signed_residual slp_one_sided_branch_sign
        (slp_complex_family_unpack x))"
    by (rule ext) (rule slp_one_sided_packed_residual_identity)
  show ?thesis
    using generic_measurable
    by (simp only: residual_function)
qed

lemma slp_one_sided_passive_root_phase_integrable:
  fixes F :: "real^bool \<Rightarrow>
    real^((unit + ('i::finite + 'i)) \<times> bool) \<Rightarrow> complex"
    and omega :: real
  assumes F_integrable:
    "integrable (lborel \<Otimes>\<^sub>M lborel) (case_prod F)"
  shows
    "integrable (lborel \<Otimes>\<^sub>M lborel)
      (\<lambda>(root, branch). exp (\<i> * of_real
        (omega * slp_one_sided_packed_residual branch)) * F root branch)"
proof (rule Bochner_Integration.integrable_bound[OF F_integrable])
  have F_measurable:
    "case_prod F \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using F_integrable by measurable
  have phase_measurable:
    "(\<lambda>branch :: real^((unit + ('i + 'i)) \<times> bool).
        exp (\<i> * of_real
          (omega * slp_one_sided_packed_residual branch)))
      \<in> borel_measurable lborel"
    using slp_one_sided_packed_residual_measurable by measurable
  show
    "(\<lambda>(root, branch). exp (\<i> * of_real
        (omega * slp_one_sided_packed_residual branch)) * F root branch)
      \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using F_measurable phase_measurable by measurable
  show
    "AE x in lborel \<Otimes>\<^sub>M lborel.
      norm ((\<lambda>(root, branch). exp (\<i> * of_real
        (omega * slp_one_sided_packed_residual branch)) *
          F root branch) x) \<le> norm (case_prod F x)"
    by (simp only: split_beta norm_mult norm_exp_i_times mult_1_left
        order_refl eventually_True)
qed

theorem slp_one_sided_packed_residual_passive_root_decay:
  fixes F :: "real^bool \<Rightarrow>
    real^((unit + ('i::finite + 'i)) \<times> bool) \<Rightarrow> complex"
  assumes stationary_phase:
      "hormander_quadratic_stationary_phase_decay_claim
        TYPE(('i + 'i) \<times> bool)"
    and density:
      "evans_compact_smooth_l1_density_claim TYPE(('i + 'i) \<times> bool)"
    and F_integrable:
      "integrable (lborel \<Otimes>\<^sub>M lborel) (case_prod F)"
  shows
    "((\<lambda>omega. integral\<^sup>L (lborel \<Otimes>\<^sub>M lborel)
        (\<lambda>(root, branch). exp (\<i> * of_real
          (omega * slp_one_sided_packed_residual branch)) *
            F root branch))
      \<longlongrightarrow> 0) at_top"
proof -
  let ?slice = "\<lambda>omega root. integral\<^sup>L lborel
    (\<lambda>branch. exp (\<i> * of_real
      (omega * slp_one_sided_packed_residual branch)) * F root branch)"
  let ?bound = "\<lambda>root. integral\<^sup>L lborel
    (\<lambda>branch. norm (F root branch))"

  have AE_slice_integrable:
    "AE root in lborel. integrable lborel (F root)"
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
      (\<lambda>(root, branch). exp (\<i> * of_real
        (omega * slp_one_sided_packed_residual branch)) *
          F root branch)" for omega
    by (rule slp_one_sided_passive_root_phase_integrable[
        where F = F and omega = omega, OF F_integrable])
  have slice_integrable: "integrable lborel (?slice omega)" for omega
    using lborel_pair.integrable_fst[OF product_integrable[of omega]]
    by simp
  have slice_measurable:
    "?slice omega \<in> borel_measurable lborel" for omega
    using slice_integrable[of omega] by measurable

  have slice_decay:
    "AE root in lborel.
      ((\<lambda>omega. ?slice omega root) \<longlongrightarrow> 0) at_top"
    using AE_slice_integrable
  proof eventually_elim
    fix root
    assume root_integrable: "integrable lborel (F root)"
    show "((\<lambda>omega. ?slice omega root) \<longlongrightarrow> 0) at_top"
      by (rule slp_one_sided_packed_residual_decay[
          where F = "F root", OF stationary_phase density root_integrable])
  qed

  have slice_bound:
    "norm (?slice omega root) \<le> ?bound root" for omega root
  proof -
    have
      "norm (integral\<^sup>L lborel
        (\<lambda>branch. exp (\<i> * of_real
          (omega * slp_one_sided_packed_residual branch)) *
            F root branch))
      \<le> integral\<^sup>L lborel
        (\<lambda>branch. norm (exp (\<i> * of_real
          (omega * slp_one_sided_packed_residual branch)) *
            F root branch))"
      by (rule Bochner_Integration.integral_norm_bound)
    also have "... = ?bound root"
      by (intro Bochner_Integration.integral_cong[OF refl])
        (simp only: norm_mult norm_exp_i_times mult_1_left)
    finally show ?thesis .
  qed

  have outer_decay:
    "((\<lambda>omega. integral\<^sup>L lborel (?slice omega))
      \<longlongrightarrow> integral\<^sup>L lborel (\<lambda>_. 0)) at_top"
  proof (rule tendsto_at_topI_sequentially)
    fix X :: "nat \<Rightarrow> real"
    assume X_at_top: "filterlim X at_top sequentially"
    have zero_measurable:
      "(\<lambda>_ :: real^bool. (0 :: complex)) \<in>
        borel_measurable lborel"
      by simp
    have sequence_measurable:
      "(\<lambda>root. ?slice (X n) root) \<in>
        borel_measurable lborel" for n
      by (rule slice_measurable)
    have sequence_limit:
      "AE root in lborel.
        (\<lambda>n. ?slice (X n) root) \<longlonglongrightarrow> 0"
      using slice_decay
    proof eventually_elim
      fix root
      assume root_decay:
        "((\<lambda>omega. ?slice omega root) \<longlongrightarrow> 0) at_top"
      show "(\<lambda>n. ?slice (X n) root) \<longlonglongrightarrow> 0"
        using root_decay X_at_top by (rule filterlim_compose)
    qed
    have sequence_bound:
      "\<And>n. AE root in lborel.
        norm (?slice (X n) root) \<le> ?bound root"
      using slice_bound by simp
    show
      "(\<lambda>n. integral\<^sup>L lborel (?slice (X n)))
        \<longlonglongrightarrow> integral\<^sup>L lborel (\<lambda>_. 0)"
      using Bochner_Integration.integral_dominated_convergence[
        OF zero_measurable sequence_measurable bound_integrable
          sequence_limit sequence_bound]
      by (simp only: Bochner_Integration.integral_zero)
  qed

  have product_as_slices:
    "integral\<^sup>L (lborel \<Otimes>\<^sub>M lborel)
        (\<lambda>(root, branch). exp (\<i> * of_real
          (omega * slp_one_sided_packed_residual branch)) *
            F root branch)
      = integral\<^sup>L lborel (?slice omega)" for omega
    using lborel_pair.integral_fst[OF product_integrable[of omega]]
    by simp

  show ?thesis
    using outer_decay
    by (simp only: product_as_slices Bochner_Integration.integral_zero)
qed

end
