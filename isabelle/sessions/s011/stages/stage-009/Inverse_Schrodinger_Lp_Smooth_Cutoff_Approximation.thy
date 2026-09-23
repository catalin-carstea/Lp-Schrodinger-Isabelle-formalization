theory Inverse_Schrodinger_Lp_Smooth_Cutoff_Approximation
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Complex_Lp_Product_Closures"
    "Smooth_Manifolds.Partition_Of_Unity"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Centered-ball tails and smooth compact cutoffs\<close>

lemma slp_integrable_nonnegative_cball_tail:
  fixes g :: "slp_point \<Rightarrow> real"
    and epsilon :: real
  assumes g_integrable: "integrable lborel g"
    and g_nonnegative: "\<And>x. 0 \<le> g x"
    and epsilon_positive: "0 < epsilon"
  shows
    "\<exists>n :: nat.
      integral\<^sup>L lborel
        (\<lambda>x. indicator (UNIV - cball 0 (real n)) x * g x) < epsilon"
proof -
  let ?tail =
    "\<lambda>n :: nat. \<lambda>x :: slp_point.
      indicator (UNIV - cball 0 (real n)) x * g x"
  have g_measurable: "g \<in> borel_measurable lborel"
    using g_integrable by measurable
  have tail_set_measurable:
      "UNIV - cball (0 :: slp_point) (real n) \<in> sets lborel" for n
    by measurable
  have tail_measurable:
      "?tail n \<in> borel_measurable lborel" for n
    using tail_set_measurable[of n] g_measurable by measurable
  have tail_bound:
      "AE x in lborel. norm_class.norm (?tail n x) \<le> g x" for n
    using g_nonnegative by (auto simp: indicator_def)
  have tail_pointwise:
      "AE x in lborel. (\<lambda>n. ?tail n x) \<longlonglongrightarrow> 0"
  proof (rule AE_I2)
    fix x :: slp_point
    obtain N :: nat where N: "norm_class.norm x < real N"
      using reals_Archimedean2 by blast
    have eventually_inside:
        "\<forall>\<^sub>F n in sequentially. x \<in> cball 0 (real n)"
      using eventually_ge_at_top[of N]
    proof eventually_elim
      fix n
      assume "N \<le> n"
      with N show "x \<in> cball 0 (real n)"
        by (auto simp: dist_norm)
    qed
    show "(\<lambda>n. ?tail n x) \<longlonglongrightarrow> 0"
    proof (rule tendsto_eventually)
      show "\<forall>\<^sub>F n in sequentially. ?tail n x = 0"
        using eventually_inside
        by eventually_elim (auto simp: indicator_def)
    qed
  qed
  have tail_limit:
      "(\<lambda>n. integral\<^sup>L lborel (?tail n)) \<longlonglongrightarrow> 0"
  proof -
    have
      "(\<lambda>n. integral\<^sup>L lborel (?tail n)) \<longlonglongrightarrow>
        integral\<^sup>L lborel (\<lambda>_ :: slp_point. (0 :: real))"
      apply (rule integral_dominated_convergence[where w=g])
      subgoal by measurable
      subgoal using tail_measurable .
      subgoal using g_integrable .
      subgoal using tail_pointwise .
      subgoal using tail_bound .
      done
    then show ?thesis by simp
  qed
  from order_tendstoD(2)[OF tail_limit epsilon_positive]
  obtain n :: nat where
      "integral\<^sup>L lborel (?tail n) < epsilon"
    by (auto simp: eventually_sequentially)
  then show ?thesis by blast
qed

theorem slp_aim_complex_lp_on_plane_smooth_cutoff_approximation:
  fixes q epsilon :: real
    and F :: "slp_point \<Rightarrow> complex"
  assumes q_positive: "0 < q"
    and F_lp: "aim_complex_lp_on_plane q F"
    and epsilon_positive: "0 < epsilon"
  shows
    "\<exists>phi. slp_test_function_on UNIV phi \<and>
      (integral\<^sup>L lborel
        (\<lambda>x. norm_class.norm (F x - phi x * F x) powr q))
        powr (1 / q) < epsilon"
proof -
  let ?g = "\<lambda>x. norm_class.norm (F x) powr q"
  have g_integrable: "integrable lborel ?g"
    using F_lp unfolding aim_complex_lp_on_plane_def by blast
  have g_nonnegative: "0 \<le> ?g x" for x
    by simp
  have epsilon_power_positive: "0 < epsilon powr q"
    using epsilon_positive by simp
  obtain n :: nat where tail_less:
      "integral\<^sup>L lborel
        (\<lambda>x. indicator (UNIV - cball 0 (real n)) x * ?g x)
        < epsilon powr q"
    using slp_integrable_nonnegative_cball_tail[OF g_integrable
      g_nonnegative epsilon_power_positive] by blast

  have closed_inner:
      "closedin
        (top_of_set (manifold_eucl.carrier :: slp_point set))
        (cball 0 (real n))"
    by simp
  have inner_subset_outer:
      "cball (0 :: slp_point) (real n) \<subseteq>
        ball 0 (real n + 1)"
    by (auto simp: subset_iff)
  have outer_subset_carrier:
      "ball (0 :: slp_point) (real n + 1) \<subseteq>
        (manifold_eucl.carrier :: slp_point set)"
    by simp
  have outer_open: "open (ball (0 :: slp_point) (real n + 1))"
    by simp
  from manifold_eucl.smooth_bump_functionE[
      OF closed_inner inner_subset_outer outer_subset_carrier outer_open,
      where k=infinity]
  obtain psi :: "slp_point \<Rightarrow> real" where
      psi_diff: "diff_fun infinity charts_eucl psi"
    and psi_nonnegative: "\<And>x. 0 \<le> psi x"
    and psi_at_most_one: "\<And>x. psi x \<le> 1"
    and psi_one: "\<And>x. x \<in> cball 0 (real n) \<Longrightarrow> psi x = 1"
    and psi_support:
      "csupport_on UNIV psi \<subseteq> ball 0 (real n + 1)"
    by auto

  define phi :: "slp_point \<Rightarrow> complex" where
    "phi x = psi x *\<^sub>R (1 :: complex)" for x
  have psi_smooth: "smooth_on UNIV psi"
    using diff_fun_charts_euclD[OF psi_diff] by simp
  have phi_smooth: "smooth_on UNIV phi"
    unfolding phi_def
    by (intro smooth_on_scaleR psi_smooth smooth_on_const) simp
  have phi_support_subset:
      "closure {x. phi x \<noteq> 0} \<subseteq> ball 0 (real n + 1)"
    using psi_support
    by (simp add: phi_def csupport_on_def support_on_def)
  have phi_support_bounded: "bounded (closure {x. phi x \<noteq> 0})"
    by (rule bounded_subset[OF bounded_ball phi_support_subset])
  have phi_support_compact: "compact (closure {x. phi x \<noteq> 0})"
    using phi_support_bounded by (simp add: compact_eq_bounded_closed)
  have phi_test: "slp_test_function_on UNIV phi"
    unfolding slp_test_function_on_def
    using phi_smooth phi_support_compact by simp

  have F_measurable: "F \<in> borel_measurable lborel"
    using F_lp unfolding aim_complex_lp_on_plane_def by blast
  have phi_integrable: "integrable lborel phi"
    by (rule slp_test_function_integrable_bounded(1)[OF phi_test])
  have phi_measurable: "phi \<in> borel_measurable lborel"
    using phi_integrable by measurable

  let ?error =
    "\<lambda>x. norm_class.norm (F x - phi x * F x) powr q"
  let ?tail =
    "\<lambda>x. indicator (UNIV - cball 0 (real n)) x * ?g x"
  have difference_norm_le:
      "norm_class.norm (F x - phi x * F x) \<le>
        norm_class.norm (F x)" for x
  proof -
    have one_minus_nonnegative: "0 \<le> 1 - psi x"
      using psi_at_most_one by simp
    have one_minus_at_most_one: "1 - psi x \<le> 1"
      using psi_nonnegative by simp
    have difference:
        "F x - phi x * F x = (1 - psi x) *\<^sub>R F x"
      by (simp add: phi_def scaleR_conv_of_real algebra_simps)
    have abs_one_minus: "\<bar>1 - psi x\<bar> = 1 - psi x"
      by (rule abs_of_nonneg[OF one_minus_nonnegative])
    have
      "norm_class.norm (F x - phi x * F x) =
        (1 - psi x) * norm_class.norm (F x)"
      by (simp add: difference norm_scaleR abs_one_minus)
    also have "... \<le> 1 * norm_class.norm (F x)"
      by (rule mult_right_mono[OF one_minus_at_most_one]) simp
    finally show ?thesis by simp
  qed
  have pointwise_bound: "?error x \<le> ?tail x" for x
  proof (cases "x \<in> cball (0 :: slp_point) (real n)")
    case True
    then have "psi x = 1" by (rule psi_one)
    with True show ?thesis
      by (simp add: phi_def indicator_def)
  next
    case False
    have
      "norm_class.norm (F x - phi x * F x) powr q \<le>
        norm_class.norm (F x) powr q"
      by (rule powr_mono2)
        (use q_positive difference_norm_le[of x] in \<open>auto\<close>)
    with False show ?thesis by (simp add: indicator_def)
  qed

  have error_measurable: "?error \<in> borel_measurable lborel"
    using F_measurable phi_measurable by measurable
  have tail_set_measurable:
      "UNIV - cball (0 :: slp_point) (real n) \<in> sets lborel"
    by measurable
  have tail_integrable: "integrable lborel ?tail"
    using integrable_real_mult_indicator[OF tail_set_measurable g_integrable]
    by (simp add: mult.commute)
  have error_integrable: "integrable lborel ?error"
  proof (rule Bochner_Integration.integrable_bound[
      OF tail_integrable error_measurable])
    show "AE x in lborel.
        norm_class.norm (?error x) \<le> norm_class.norm (?tail x)"
      using pointwise_bound g_nonnegative
      by (auto simp: indicator_def)
  qed
  have error_integral_nonnegative:
      "0 \<le> integral\<^sup>L lborel ?error"
    by (rule integral_nonneg_AE) simp
  have error_integral_le_tail:
      "integral\<^sup>L lborel ?error \<le> integral\<^sup>L lborel ?tail"
    by (rule integral_mono_AE[OF error_integrable tail_integrable])
      (use pointwise_bound in auto)
  have error_integral_less:
      "integral\<^sup>L lborel ?error < epsilon powr q"
    using error_integral_le_tail tail_less by linarith
  have rooted_error_less:
      "(integral\<^sup>L lborel ?error) powr (1 / q) < epsilon"
  proof -
    have inverse_q_positive: "0 < 1 / q"
      using q_positive by simp
    have
      "(integral\<^sup>L lborel ?error) powr (1 / q) <
        (epsilon powr q) powr (1 / q)"
      by (rule powr_less_mono2[OF inverse_q_positive
            error_integral_nonnegative error_integral_less])
    also have "... = epsilon"
      using q_positive epsilon_positive
      by (simp add: powr_powr)
    finally show ?thesis .
  qed
  show ?thesis
    using phi_test rooted_error_less by blast
qed

end
