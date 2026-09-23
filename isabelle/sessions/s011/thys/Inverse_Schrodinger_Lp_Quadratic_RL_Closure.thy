theory Inverse_Schrodinger_Lp_Quadratic_RL_Closure
  imports
    "Paper_ISLP_Hormander_Quadratic_Stationary_Phase.Hormander_Quadratic_Stationary_Phase_Interface"
begin

section \<open>Quadratic oscillatory decay under \<open>L1\<close> approximation\<close>

lemma slp_quadratic_phase_integrable:
  fixes A :: "real^'n::finite^'n"
    and F :: "real^'n \<Rightarrow> complex"
    and omega :: real
  assumes F_integrable: "integrable lborel F"
  shows "integrable lborel
    (\<lambda>x. exp (\<i> * of_real
      (omega * inner x (A *v x) / 2)) * F x)"
proof (rule Bochner_Integration.integrable_bound[OF F_integrable])
  have F_measurable: "F \<in> borel_measurable lborel"
    using F_integrable by measurable
  have matrix_continuous: "continuous_on UNIV ((*v) A)"
    by (rule matrix_vector_mult_linear_continuous_on)
  have quadratic_continuous:
    "continuous_on UNIV (\<lambda>x. inner x (A *v x))"
    by (intro continuous_on_inner continuous_on_id matrix_continuous)
  have phase_continuous:
    "continuous_on UNIV
      (\<lambda>x. exp (\<i> * of_real
        (omega * inner x (A *v x) / 2)))"
    by (intro continuous_intros quadratic_continuous) simp
  have phase_measurable_borel:
    "(\<lambda>x. exp (\<i> * of_real
      (omega * inner x (A *v x) / 2))) \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF phase_continuous])
  have phase_measurable:
    "(\<lambda>x. exp (\<i> * of_real
      (omega * inner x (A *v x) / 2))) \<in> borel_measurable lborel"
    using phase_measurable_borel by simp
  show "(\<lambda>x. exp (\<i> * of_real
      (omega * inner x (A *v x) / 2)) * F x)
      \<in> borel_measurable lborel"
    using phase_measurable F_measurable by measurable
  show "AE x in lborel.
      norm (exp (\<i> * of_real
        (omega * inner x (A *v x) / 2)) * F x) \<le> norm (F x)"
    by (simp only: norm_mult norm_exp_i_times mult_1_left order_refl
        eventually_True)
qed

lemma slp_quadratic_oscillatory_integral_l1_lipschitz:
  fixes A :: "real^'n::finite^'n"
    and F G :: "real^'n \<Rightarrow> complex"
    and omega :: real
  assumes F_integrable: "integrable lborel F"
    and G_integrable: "integrable lborel G"
  shows
    "norm (hormander_quadratic_oscillatory_integral A F omega -
      hormander_quadratic_oscillatory_integral A G omega)
      \<le> integral\<^sup>L lborel (\<lambda>x. norm (F x - G x))"
proof -
  let ?phase = "\<lambda>x. exp (\<i> * of_real
    (omega * inner x (A *v x) / 2))"
  have phase_norm [simp]: "norm (?phase x) = 1" for x
    by (simp only: norm_exp_i_times)
  have F_phase_integrable: "integrable lborel (\<lambda>x. ?phase x * F x)"
    using slp_quadratic_phase_integrable[where A=A and F=F and omega=omega,
      OF F_integrable] .
  have G_phase_integrable: "integrable lborel (\<lambda>x. ?phase x * G x)"
    using slp_quadratic_phase_integrable[where A=A and F=G and omega=omega,
      OF G_integrable] .
  have difference:
    "hormander_quadratic_oscillatory_integral A F omega -
       hormander_quadratic_oscillatory_integral A G omega =
     integral\<^sup>L lborel (\<lambda>x. ?phase x * (F x - G x))"
    unfolding hormander_quadratic_oscillatory_integral_def
    using Bochner_Integration.integral_diff
      [OF F_phase_integrable G_phase_integrable]
    by (simp add: algebra_simps)
  have
    "norm (integral\<^sup>L lborel (\<lambda>x. ?phase x * (F x - G x)))
      \<le> integral\<^sup>L lborel
        (\<lambda>x. norm (?phase x * (F x - G x)))"
    by (rule Bochner_Integration.integral_norm_bound)
  also have "... = integral\<^sup>L lborel (\<lambda>x. norm (F x - G x))"
    by (intro Bochner_Integration.integral_cong[OF refl])
      (simp only: norm_mult phase_norm mult_1_left)
  finally show ?thesis
    using difference by simp
qed

context hormander_quadratic_stationary_phase_decay
begin

lemma slp_quadratic_decay_of_l1_approximation:
  fixes A :: "real^'n::finite^'n"
    and F :: "real^'n \<Rightarrow> complex"
  assumes symmetric: "hormander_real_symmetric_matrix A"
    and nondegenerate: "hormander_real_nondegenerate_matrix A"
    and F_integrable: "integrable lborel F"
    and approximation:
      "\<And>epsilon. 0 < epsilon \<Longrightarrow>
        \<exists>u. hormander_compact_smooth_amplitude u \<and>
          integral\<^sup>L lborel (\<lambda>x. norm (F x - u x)) < epsilon"
  shows
    "((\<lambda>omega. hormander_quadratic_oscillatory_integral A F omega)
      \<longlongrightarrow> 0) at_top"
proof (unfold tendsto_iff, intro allI impI)
  fix epsilon :: real
  assume epsilon_positive: "0 < epsilon"
  then have half_positive: "0 < epsilon / 2"
    by simp
  obtain u where u_amplitude: "hormander_compact_smooth_amplitude u"
    and approximation_error:
      "integral\<^sup>L lborel (\<lambda>x. norm (F x - u x)) < epsilon / 2"
    using approximation[OF half_positive] by blast
  have u_integrable: "integrable lborel u"
    using u_amplitude
    unfolding hormander_compact_smooth_amplitude_def by blast
  have u_decay:
    "((\<lambda>omega. hormander_quadratic_oscillatory_integral A u omega)
      \<longlongrightarrow> 0) at_top"
    using hormander_quadratic_stationary_phase_decay
      symmetric nondegenerate u_amplitude
    unfolding hormander_quadratic_stationary_phase_decay_claim_def
    by blast
  have eventually_u:
    "eventually
      (\<lambda>omega. dist
        (hormander_quadratic_oscillatory_integral A u omega) 0 < epsilon / 2)
      at_top"
    using u_decay half_positive
    unfolding tendsto_iff by blast
  show "eventually
      (\<lambda>omega.
        dist (hormander_quadratic_oscillatory_integral A F omega) 0 < epsilon)
      at_top"
    using eventually_u
  proof eventually_elim
    fix omega
    assume u_event:
      "dist (hormander_quadratic_oscillatory_integral A u omega) 0 <
        epsilon / 2"
    have lipschitz:
      "norm (hormander_quadratic_oscillatory_integral A F omega -
        hormander_quadratic_oscillatory_integral A u omega)
        \<le> integral\<^sup>L lborel (\<lambda>x. norm (F x - u x))"
      using slp_quadratic_oscillatory_integral_l1_lipschitz[where A=A and F=F
        and G=u and omega=omega, OF F_integrable u_integrable] .
    have difference_small:
      "norm (hormander_quadratic_oscillatory_integral A F omega -
        hormander_quadratic_oscillatory_integral A u omega) < epsilon / 2"
      using lipschitz approximation_error by linarith
    have u_small:
      "norm (hormander_quadratic_oscillatory_integral A u omega) < epsilon / 2"
      using u_event by (simp add: dist_norm)
    have
      "norm (hormander_quadratic_oscillatory_integral A F omega)
        \<le> norm (hormander_quadratic_oscillatory_integral A u omega) +
          norm (hormander_quadratic_oscillatory_integral A F omega -
            hormander_quadratic_oscillatory_integral A u omega)"
      by (rule norm_triangle_sub)
    also have "... < epsilon / 2 + epsilon / 2"
      using u_small difference_small by linarith
    also have "... = epsilon"
      by simp
    finally show
      "dist (hormander_quadratic_oscillatory_integral A F omega) 0 < epsilon"
      by (simp add: dist_norm)
  qed
qed

end

end
