theory Inverse_Schrodinger_Lp_Quadratic_RL_Affine
  imports
    Inverse_Schrodinger_Lp_Quadratic_RL_Density
begin

section \<open>Affine active-fiber quadratic decay\<close>

lemma slp_lborel_integrable_translate:
  fixes f :: "real^'n::finite \<Rightarrow> 'a::{banach, second_countable_topology}"
  assumes f_integrable: "integrable lborel f"
  shows "integrable lborel (\<lambda>x. f (a + x))"
proof -
  have add_measurable: "(+) a \<in> measurable lborel borel"
    by measurable
  have f_measurable: "f \<in> borel_measurable borel"
    using f_integrable by measurable
  have distr_integrable: "integrable (distr lborel borel ((+) a)) f"
    using f_integrable by (simp only: lborel_distr_plus)
  show ?thesis
    using Bochner_Integration.integrable_distr_eq[
      OF add_measurable f_measurable]
      distr_integrable by blast
qed

lemma slp_lborel_integral_translate:
  fixes f :: "real^'n::finite \<Rightarrow> 'a::{banach, second_countable_topology}"
  assumes f_integrable: "integrable lborel f"
  shows "integral\<^sup>L lborel (\<lambda>x. f (a + x)) = integral\<^sup>L lborel f"
proof -
  have add_measurable: "(+) a \<in> measurable lborel borel"
    by measurable
  have f_measurable: "f \<in> borel_measurable borel"
    using f_integrable by measurable
  have distr_formula:
    "integral\<^sup>L (distr lborel borel ((+) a)) f =
      integral\<^sup>L lborel (\<lambda>x. f (a + x))"
    by (rule Bochner_Integration.integral_distr[
      OF add_measurable f_measurable])
  show ?thesis
    using distr_formula by (simp only: lborel_distr_plus)
qed

lemma slp_quadratic_phase_integrable:
  fixes A :: "real^'n::finite^'n"
    and F :: "real^'n \<Rightarrow> complex"
    and omega :: real
  assumes F_integrable: "integrable lborel F"
  shows "integrable lborel
    (\<lambda>u. exp (\<i> * of_real
      (omega * inner u (A *v u) / 2)) * F u)"
proof (rule Bochner_Integration.integrable_bound[OF F_integrable])
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
  have F_measurable: "F \<in> borel_measurable lborel"
    using F_integrable by measurable
  show "(\<lambda>u. exp (\<i> * of_real
      (omega * inner u (A *v u) / 2)) * F u)
      \<in> borel_measurable lborel"
    using phase_measurable F_measurable by measurable
  show "AE u in lborel.
      norm (exp (\<i> * of_real
        (omega * inner u (A *v u) / 2)) * F u) \<le> norm (F u)"
    by (simp only: norm_mult norm_exp_i_times mult_1_left order_refl
        eventually_True)
qed

context hormander_quadratic_stationary_phase_decay
begin

lemma slp_quadratic_decay_affine:
  fixes A :: "real^'n::finite^'n"
    and b :: "real^'n"
    and p0 :: real
    and F :: "real^'n \<Rightarrow> complex"
  assumes density:
      "evans_compact_smooth_l1_density_claim TYPE('n)"
    and symmetric: "hormander_real_symmetric_matrix A"
    and nondegenerate: "hormander_real_nondegenerate_matrix A"
    and F_integrable: "integrable lborel F"
  shows
    "((\<lambda>omega. integral\<^sup>L lborel
        (\<lambda>u. exp (\<i> * of_real
          (omega * (inner u (A *v u) / 2 + inner b u + p0))) * F u))
      \<longlongrightarrow> 0) at_top"
proof -
  have A_linear: "linear ((*v) A)"
    by (rule matrix_vector_mul_linear)
  have A_injective: "inj ((*v) A)"
    using nondegenerate
    unfolding hormander_real_nondegenerate_matrix_def
    linear_injective_0[OF A_linear] by blast
  have A_surjective: "surj ((*v) A)"
    using linear_injective_imp_surjective[OF A_linear A_injective] by simp
  obtain h where hA: "b = A *v h"
    using A_surjective unfolding surj_def by blast
  have Ah: "A *v h = b"
    using hA by simp

  have transpose_A: "transpose A = A"
    using symmetric
    unfolding hormander_real_symmetric_matrix_def transpose_def
    by (simp add: vec_eq_iff)
  have cross_left: "inner h (A *v u) = inner b u" for u
  proof -
    have "inner h (A *v u) = inner (h v* A) u"
      by (rule dot_lmul_matrix[symmetric])
    also have "... = inner (transpose A *v h) u"
      by simp
    also have "... = inner (A *v h) u"
      by (simp only: transpose_A)
    also have "... = inner b u"
      by (simp only: Ah)
    finally show ?thesis .
  qed
  have cross_right: "inner u (A *v h) = inner b u" for u
  proof -
    have "inner u (A *v h) = inner (A *v h) u"
      by (rule inner_commute)
    also have "... = inner b u"
      by (simp only: Ah)
    finally show ?thesis .
  qed
  have square_identity:
    "inner (h + u) (A *v (h + u)) / 2 =
      inner u (A *v u) / 2 + inner b u +
        inner h (A *v h) / 2" for u
  proof -
    have expanded:
      "inner (h + u) (A *v (h + u)) =
        inner h (A *v h) + inner h (A *v u) +
          inner u (A *v h) + inner u (A *v u)"
      by (simp only: matrix_vector_right_distrib inner_add_left
          inner_add_right)
    show ?thesis
      using expanded cross_left[of u] cross_right[of u] by linarith
  qed
  have scalar_phase:
    "inner u (A *v u) / 2 + inner b u + p0 =
      inner (h + u) (A *v (h + u)) / 2 +
        (p0 - inner h (A *v h) / 2)" for u
    using square_identity[of u] by linarith

  define G where "G v = F (v - h)" for v
  have G_integrable: "integrable lborel G"
    using slp_lborel_integrable_translate[OF F_integrable, of "-h"]
    unfolding G_def by (simp add: add.commute)
  have G_decay:
    "((\<lambda>omega. hormander_quadratic_oscillatory_integral A G omega)
      \<longlongrightarrow> 0) at_top"
    by (rule slp_quadratic_decay_integrable[
      OF density symmetric nondegenerate G_integrable])

  let ?constant = "\<lambda>omega. exp (\<i> * of_real
    (omega * (p0 - inner h (A *v h) / 2)))"
  have integral_identity:
    "integral\<^sup>L lborel
        (\<lambda>u. exp (\<i> * of_real
          (omega * (inner u (A *v u) / 2 + inner b u + p0))) * F u)
      = ?constant omega *
        hormander_quadratic_oscillatory_integral A G omega" for omega
  proof -
    let ?pure = "\<lambda>v. exp (\<i> * of_real
      (omega * inner v (A *v v) / 2)) * G v"
    have pure_integrable: "integrable lborel ?pure"
      by (rule slp_quadratic_phase_integrable[OF G_integrable])
    have translated:
      "integral\<^sup>L lborel (\<lambda>u. ?pure (h + u)) =
        integral\<^sup>L lborel ?pure"
      by (rule slp_lborel_integral_translate[OF pure_integrable])
    have exponential_split:
      "exp (\<i> * of_real
          (omega * (inner u (A *v u) / 2 + inner b u + p0))) =
        ?constant omega * exp (\<i> * of_real
          (omega * inner (h + u) (A *v (h + u)) / 2))" for u
    proof -
      have scalar_split:
        "omega * (inner u (A *v u) / 2 + inner b u + p0) =
          omega * (p0 - inner h (A *v h) / 2) +
            omega * inner (h + u) (A *v (h + u)) / 2"
      proof -
        have "omega * (inner u (A *v u) / 2 + inner b u + p0) =
            omega * (inner (h + u) (A *v (h + u)) / 2 +
              (p0 - inner h (A *v h) / 2))"
          by (simp only: scalar_phase)
        also have "... = omega * (p0 - inner h (A *v h) / 2) +
            omega * inner (h + u) (A *v (h + u)) / 2"
          by (simp only: distrib_left add.commute)
        finally show ?thesis .
      qed
      have "exp (\<i> * of_real
          (omega * (inner u (A *v u) / 2 + inner b u + p0))) =
        exp (\<i> * of_real
          (omega * (p0 - inner h (A *v h) / 2) +
            omega * inner (h + u) (A *v (h + u)) / 2))"
        by (simp only: scalar_split)
      also have "... = exp
          (\<i> * of_real (omega * (p0 - inner h (A *v h) / 2)) +
            \<i> * of_real
              (omega * inner (h + u) (A *v (h + u)) / 2))"
        by (simp only: of_real_add distrib_left)
      also have "... = ?constant omega * exp (\<i> * of_real
          (omega * inner (h + u) (A *v (h + u)) / 2))"
        by (simp only: exp_add)
      finally show ?thesis .
    qed
    have pointwise:
      "exp (\<i> * of_real
          (omega * (inner u (A *v u) / 2 + inner b u + p0))) * F u =
        ?constant omega * ?pure (h + u)" for u
      using exponential_split[of u]
      by (simp add: G_def algebra_simps)
    have "integral\<^sup>L lborel
        (\<lambda>u. exp (\<i> * of_real
          (omega * (inner u (A *v u) / 2 + inner b u + p0))) * F u) =
      integral\<^sup>L lborel (\<lambda>u. ?constant omega * ?pure (h + u))"
      by (intro Bochner_Integration.integral_cong[OF refl])
        (simp only: pointwise)
    also have "... =
        ?constant omega * integral\<^sup>L lborel (\<lambda>u. ?pure (h + u))"
      by simp
    also have "... = ?constant omega * integral\<^sup>L lborel ?pure"
      by (simp only: translated)
    also have "... =
        ?constant omega * hormander_quadratic_oscillatory_integral A G omega"
      by (simp only: hormander_quadratic_oscillatory_integral_def)
    finally show ?thesis .
  qed

  have norm_decay:
    "((\<lambda>omega. norm
        (hormander_quadratic_oscillatory_integral A G omega))
      \<longlongrightarrow> 0) at_top"
    using tendsto_norm[OF G_decay] by simp
  have target_norm_decay:
    "((\<lambda>omega. norm (integral\<^sup>L lborel
        (\<lambda>u. exp (\<i> * of_real
          (omega * (inner u (A *v u) / 2 + inner b u + p0))) * F u)))
      \<longlongrightarrow> 0) at_top"
    using norm_decay
    by (simp only: integral_identity norm_mult norm_exp_i_times mult_1_left)
  show ?thesis
    using target_norm_decay by (rule tendsto_norm_zero_cancel)
qed

end

end
