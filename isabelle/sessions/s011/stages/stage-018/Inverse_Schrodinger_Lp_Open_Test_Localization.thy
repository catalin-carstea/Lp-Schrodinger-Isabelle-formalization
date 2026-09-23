theory Inverse_Schrodinger_Lp_Open_Test_Localization
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_018.Inverse_Schrodinger_Lp_Common_CGO_Test_Pairing_Zero"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Weak_Test_Multiplier"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_One_Sided_Smooth_Error_Limits"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Smooth localization of global tests inside an open set\<close>

theorem slp_open_test_cutoff_sequence:
  fixes U :: "slp_point set"
  assumes U_open: "open U"
  obtains chi :: "nat \<Rightarrow> slp_scalar_field"
  where "\<And>n. slp_test_function_on U (chi n)"
    and "\<And>n x. norm (chi n x) \<le> 1"
    and
      "\<And>x. x \<in> U \<Longrightarrow> eventually (\<lambda>n. chi n x = 1) sequentially"
proof -
  obtain C :: "nat \<Rightarrow> slp_point set" where
      C_compact: "\<And>n. compact (C n)"
    and C_subset_U: "\<And>n. C n \<subseteq> U"
    and C_inside: "\<And>n. C n \<subseteq> interior (C (Suc n))"
    and C_union: "\<Union> (range C) = U"
    and C_cofinal:
      "\<And>K. compact K \<Longrightarrow> K \<subseteq> U \<Longrightarrow>
        \<exists>N. \<forall>n\<ge>N. K \<subseteq> C n"
    using open_Union_compact_subsets[OF U_open] by blast

  have bump_exists:
    "\<exists>f :: slp_point \<Rightarrow> real.
      diff_fun infinity charts_eucl f \<and>
      (\<forall>x. 0 \<le> f x) \<and>
      (\<forall>x. f x \<le> 1) \<and>
      (\<forall>x \<in> C n. f x = 1) \<and>
      csupport_on UNIV f \<subseteq> interior (C (Suc n))" for n
  proof -
    have C_closedin:
      "closedin
        (top_of_set (manifold_eucl.carrier :: slp_point set)) (C n)"
      using compact_imp_closed[OF C_compact[of n]] by simp
    have outer_carrier:
      "interior (C (Suc n)) \<subseteq>
        (manifold_eucl.carrier :: slp_point set)"
      by simp
    have outer_open: "open (interior (C (Suc n)))"
      by simp
    from manifold_eucl.smooth_bump_functionE[
        OF C_closedin C_inside[of n] outer_carrier outer_open,
        where k=infinity]
    obtain f :: "slp_point \<Rightarrow> real" where
        f_diff: "diff_fun infinity charts_eucl f"
      and f_nonnegative: "\<And>x. 0 \<le> f x"
      and f_at_most_one: "\<And>x. f x \<le> 1"
      and f_one: "\<And>x. x \<in> C n \<Longrightarrow> f x = 1"
      and f_support:
        "csupport_on UNIV f \<subseteq> interior (C (Suc n))"
      by auto
    show ?thesis
      using f_diff f_nonnegative f_at_most_one f_one f_support by blast
  qed

  define psi :: "nat \<Rightarrow> slp_point \<Rightarrow> real" where
    "psi n = (SOME f :: slp_point \<Rightarrow> real.
      diff_fun infinity charts_eucl f \<and>
      (\<forall>x. 0 \<le> f x) \<and>
      (\<forall>x. f x \<le> 1) \<and>
      (\<forall>x \<in> C n. f x = 1) \<and>
      csupport_on UNIV f \<subseteq> interior (C (Suc n)))" for n
  have psi_properties:
    "diff_fun infinity charts_eucl (psi n) \<and>
      (\<forall>x. 0 \<le> psi n x) \<and>
      (\<forall>x. psi n x \<le> 1) \<and>
      (\<forall>x \<in> C n. psi n x = 1) \<and>
      csupport_on UNIV (psi n) \<subseteq> interior (C (Suc n))" for n
    unfolding psi_def
    by (rule someI_ex[OF bump_exists[of n]])
  have psi_diff: "diff_fun infinity charts_eucl (psi n)" for n
    using psi_properties[of n] by blast
  have psi_nonnegative: "0 \<le> psi n x" for n x
    using psi_properties[of n] by blast
  have psi_at_most_one: "psi n x \<le> 1" for n x
    using psi_properties[of n] by blast
  have psi_one: "x \<in> C n \<Longrightarrow> psi n x = 1" for n x
    using psi_properties[of n] by blast
  have psi_support:
    "csupport_on UNIV (psi n) \<subseteq> interior (C (Suc n))" for n
    using psi_properties[of n] by blast

  define chi :: "nat \<Rightarrow> slp_scalar_field" where
    "chi n x = psi n x *\<^sub>R (1 :: complex)" for n x
  have chi_test: "slp_test_function_on U (chi n)" for n
  proof -
    have psi_smooth: "smooth_on UNIV (psi n)"
      using diff_fun_charts_euclD[OF psi_diff[of n]] by simp
    have chi_smooth: "smooth_on UNIV (chi n)"
      unfolding chi_def
      by (intro smooth_on_scaleR psi_smooth smooth_on_const) simp
    have support_inside:
      "closure {x. chi n x \<noteq> 0} \<subseteq> interior (C (Suc n))"
      using psi_support[of n]
      by (simp add: chi_def csupport_on_def support_on_def)
    have support_in_compact:
      "closure {x. chi n x \<noteq> 0} \<subseteq> C (Suc n)"
      using support_inside interior_subset by blast
    have support_compact: "compact (closure {x. chi n x \<noteq> 0})"
      by (rule compact_if_closed_subset_of_compact[
          OF closed_closure C_compact[of "Suc n"] support_in_compact])
    have support_within: "closure {x. chi n x \<noteq> 0} \<subseteq> U"
      using support_in_compact C_subset_U[of "Suc n"] by blast
    show ?thesis
      unfolding slp_test_function_on_def
      by (rule conjI[OF chi_smooth conjI[OF support_compact support_within]])
  qed
  have chi_bound: "norm (chi n x) \<le> 1" for n x
  proof -
    have psi_abs: "\<bar>psi n x\<bar> = psi n x"
      by (rule abs_of_nonneg[OF psi_nonnegative])
    show ?thesis
      using psi_at_most_one[of n x]
      by (simp add: chi_def norm_scaleR psi_abs)
  qed
  have chi_eventually_one:
    "eventually (\<lambda>n. chi n x = 1) sequentially" if x_in: "x \<in> U" for x
  proof -
    have cofinal_singleton: "\<exists>N. \<forall>n\<ge>N. {x} \<subseteq> C n"
      by (rule C_cofinal) (use x_in in simp_all)
    obtain N where N: "\<forall>n\<ge>N. {x} \<subseteq> C n"
      using cofinal_singleton by blast
    show ?thesis
      using eventually_ge_at_top[of N]
    proof eventually_elim
      fix n :: nat
      assume "N \<le> n"
      then have "x \<in> C n"
        using N by blast
      then have "psi n x = 1"
        by (rule psi_one)
      then show "chi n x = 1"
        by (simp add: chi_def)
    qed
  qed
  show thesis
    by (rule that[OF chi_test chi_bound chi_eventually_one])
qed

theorem slp_interior_test_pairing_extends_global:
  fixes U :: "slp_point set"
    and Q phi :: slp_scalar_field
  assumes U_open: "open U"
    and Q_integrable: "integrable lborel Q"
    and Q_outside: "\<And>x. x \<notin> U \<Longrightarrow> Q x = 0"
    and pairing_zero:
      "\<And>psi. slp_test_function_on U psi \<Longrightarrow>
        integral\<^sup>L lborel (\<lambda>x. Q x * psi x) = 0"
    and phi_test: "slp_test_function_on UNIV phi"
  shows "integral\<^sup>L lborel (\<lambda>x. Q x * phi x) = 0"
proof -
  obtain chi :: "nat \<Rightarrow> slp_scalar_field" where
      chi_test: "\<And>n. slp_test_function_on U (chi n)"
    and chi_bound: "\<And>n x. norm (chi n x) \<le> 1"
    and chi_eventually_one:
      "\<And>x. x \<in> U \<Longrightarrow> eventually (\<lambda>n. chi n x = 1) sequentially"
    using slp_open_test_cutoff_sequence[OF U_open] by blast
  have phi_smooth: "smooth_on UNIV phi"
    using phi_test unfolding slp_test_function_on_def by blast
  have phi_integrable: "integrable lborel phi"
    by (rule slp_test_function_integrable_bounded(1)[OF phi_test])
  have phi_measurable: "phi \<in> borel_measurable lborel"
    using phi_integrable by measurable
  have phi_bounded: "bounded (range phi)"
    by (rule slp_test_function_integrable_bounded(2)[OF phi_test])
  obtain B where phi_bound: "\<And>x. norm (phi x) \<le> B"
    using phi_bounded unfolding bounded_iff by auto
  have B_nonnegative: "0 \<le> B"
    using norm_ge_zero[of "phi 0"] phi_bound[of 0] by linarith
  have target_integrable: "integrable lborel (\<lambda>x. Q x * phi x)"
    by (rule slp_integrable_bilinear_mult_bounded[
        OF Q_integrable phi_measurable B_nonnegative phi_bound])
  have target_measurable:
    "(\<lambda>x. Q x * phi x) \<in> borel_measurable lborel"
    using target_integrable by measurable
  have dominator_integrable:
    "integrable lborel (\<lambda>x. norm (Q x * phi x))"
    using target_integrable by simp

  have sequence_test:
    "slp_test_function_on U (\<lambda>x. phi x * chi n x)" for n
    by (rule slp_test_function_on_mult_left[OF phi_smooth chi_test[of n]])
  have sequence_zero:
    "integral\<^sup>L lborel (\<lambda>x. Q x * (phi x * chi n x)) = 0" for n
    by (rule pairing_zero[OF sequence_test[of n]])
  have sequence_measurable:
    "(\<lambda>x. Q x * (phi x * chi n x)) \<in> borel_measurable lborel" for n
  proof -
    have chi_test_UNIV: "slp_test_function_on UNIV (chi n)"
      using chi_test[of n] unfolding slp_test_function_on_def by blast
    have chi_integrable: "integrable lborel (chi n)"
      by (rule slp_test_function_integrable_bounded(1)[OF chi_test_UNIV])
    show ?thesis
      using Q_integrable phi_integrable chi_integrable by measurable
  qed
  have sequence_limit:
    "AE x in lborel.
      (\<lambda>n. Q x * (phi x * chi n x)) \<longlonglongrightarrow> Q x * phi x"
  proof (rule AE_I2)
    fix x
    have eventually_equal:
      "eventually
        (\<lambda>n. Q x * (phi x * chi n x) = Q x * phi x) sequentially"
    proof (cases "x \<in> U")
      case True
      show ?thesis
        using chi_eventually_one[OF True]
        by eventually_elim simp
    next
      case False
      then have "Q x = 0"
        by (rule Q_outside)
      then show ?thesis by simp
    qed
    show "(\<lambda>n. Q x * (phi x * chi n x)) \<longlonglongrightarrow> Q x * phi x"
      by (rule tendsto_eventually[OF eventually_equal])
  qed
  have sequence_bound:
    "\<And>n. AE x in lborel.
      norm (Q x * (phi x * chi n x)) \<le> norm (Q x * phi x)"
  proof (intro allI AE_I2)
    fix n x
    have inner_bound:
      "norm (phi x) * norm (chi n x) \<le> norm (phi x) * 1"
      by (rule mult_left_mono[OF chi_bound[of n x] norm_ge_zero])
    have outer_bound:
      "norm (Q x) * (norm (phi x) * norm (chi n x)) \<le>
        norm (Q x) * (norm (phi x) * 1)"
      by (rule mult_left_mono[OF inner_bound norm_ge_zero])
    show "norm (Q x * (phi x * chi n x)) \<le> norm (Q x * phi x)"
      using outer_bound by (simp only: norm_mult mult_1_right)
  qed
  have integral_limit:
    "(\<lambda>n. integral\<^sup>L lborel (\<lambda>x. Q x * (phi x * chi n x)))
      \<longlonglongrightarrow> integral\<^sup>L lborel (\<lambda>x. Q x * phi x)"
    using Bochner_Integration.integral_dominated_convergence[
      OF target_measurable sequence_measurable dominator_integrable
        sequence_limit sequence_bound] .
  have zero_limit:
    "(\<lambda>n. integral\<^sup>L lborel (\<lambda>x. Q x * (phi x * chi n x)))
      \<longlonglongrightarrow> 0"
    using sequence_zero by simp
  show ?thesis
    by (rule tendsto_unique[
        OF trivial_limit_sequentially integral_limit zero_limit])
qed

end
