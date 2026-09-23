theory Inverse_Schrodinger_Lp_Supported_Value_Truncations
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_L2_Density_Error_Pairing"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Value truncations of planar Lp fields\<close>

lemma slp_value_truncation_lp:
  fixes a :: real and f :: slp_scalar_field and n :: nat
  assumes exponent_positive: "0 < a"
    and field_lp: "aim_complex_lp_on_plane a f"
  shows "aim_complex_lp_on_plane a
      (\<lambda>x. if norm (f x) \<le> real (Suc n) then f x else 0)"
    "aim_complex_lp_on_plane a
      (\<lambda>x. f x - (if norm (f x) \<le> real (Suc n) then f x else 0))"
proof -
  let ?Y = "{x. norm (f x) \<le> real (Suc n)}"
  let ?g = "\<lambda>x. if norm (f x) \<le> real (Suc n) then f x else 0"
  have measurable: "f \<in> borel_measurable lborel"
    using field_lp unfolding aim_complex_lp_on_plane_def by blast
  have set_measurable: "?Y \<in> sets lborel"
    using measurable by measurable
  have restricted_lp: "aim_complex_lp_on_plane a (slp_restrict_field ?Y f)"
    by (rule slp_restriction_lp_norm_contraction(1)[OF
        exponent_positive set_measurable field_lp])
  have restriction_identity: "slp_restrict_field ?Y f = ?g"
    by (rule ext) (simp add: slp_restrict_field_def)
  have truncated_lp: "aim_complex_lp_on_plane a ?g"
    using restricted_lp by (simp only: restriction_identity)
  show "aim_complex_lp_on_plane a ?g" by (rule truncated_lp)
  show "aim_complex_lp_on_plane a (\<lambda>x. f x - ?g x)"
    by (rule aim_complex_lp_on_plane_diff[OF exponent_positive field_lp truncated_lp])
qed

lemma slp_value_truncation_norm_tendsto_zero:
  fixes a :: real and f :: slp_scalar_field
  assumes exponent_positive: "0 < a"
    and field_lp: "aim_complex_lp_on_plane a f"
  shows "(\<lambda>n::nat. aim_complex_lp_norm a
      (\<lambda>x. f x - (if norm (f x) \<le> real (Suc n) then f x else 0)))
      \<longlonglongrightarrow> 0"
proof -
  let ?g = "\<lambda>n::nat. \<lambda>x. if norm (f x) \<le> real (Suc n) then f x else 0"
  let ?E = "\<lambda>n::nat. \<lambda>x. norm (f x - ?g n x) powr a"
  let ?w = "\<lambda>x. norm (f x) powr a"
  have field_measurable: "f \<in> borel_measurable lborel"
    and weight_integrable: "integrable lborel ?w"
    using field_lp unfolding aim_complex_lp_on_plane_def by blast+
  have error_measurable: "?E n \<in> borel_measurable lborel" for n
    using field_measurable by measurable
  have error_bound: "AE x in lborel. norm (?E n x) \<le> ?w x" for n
    by (rule AE_I2) (simp add: abs_of_nonneg split: if_splits)
  have error_pointwise: "AE x in lborel. (\<lambda>n. ?E n x) \<longlonglongrightarrow> 0"
  proof (rule AE_I2)
    fix x :: slp_point
    obtain N :: nat where N: "norm (f x) \<le> real N"
      using real_arch_simple by blast
    have eventually_equal: "eventually (\<lambda>n. ?g n x = f x) sequentially"
      using eventually_ge_at_top[of N]
    proof eventually_elim
      fix n :: nat
      assume n: "N \<le> n"
      have N_bound: "real N \<le> real (Suc n)"
        by (rule of_nat_mono[OF le_SucI[OF n]])
      have "norm (f x) \<le> real (Suc n)"
        by (rule order_trans[OF N N_bound])
      then show "?g n x = f x" by simp
    qed
    show "(\<lambda>n. ?E n x) \<longlonglongrightarrow> 0"
    proof (rule tendsto_eventually)
      show "eventually (\<lambda>n. ?E n x = 0) sequentially"
        using eventually_equal by eventually_elim simp
    qed
  qed
  have integral_decay: "(\<lambda>n. integral\<^sup>L lborel (?E n)) \<longlonglongrightarrow> 0"
  proof -
    have "(\<lambda>n. integral\<^sup>L lborel (?E n)) \<longlonglongrightarrow>
        integral\<^sup>L lborel (\<lambda>_::slp_point. (0::real))"
      apply (rule integral_dominated_convergence[where w="?w"])
      subgoal by measurable
      subgoal using error_measurable .
      subgoal using weight_integrable .
      subgoal using error_pointwise .
      subgoal using error_bound .
      done
    then show ?thesis by simp
  qed
  have integral_nonnegative: "0 \<le> integral\<^sup>L lborel (?E n)" for n
    by (rule integral_nonneg_AE) simp
  have inverse_positive: "0 < 1 / a" using exponent_positive by simp
  have rooted_decay:
      "(\<lambda>n. (integral\<^sup>L lborel (?E n)) powr (1 / a))
        \<longlonglongrightarrow> 0 powr (1 / a)"
    by (rule tendsto_powr2[OF integral_decay tendsto_const _ inverse_positive])
      (use integral_nonnegative in auto)
  show ?thesis using rooted_decay unfolding aim_complex_lp_norm_def by simp
qed

theorem slp_supported_l1_l2_value_approximation:
  fixes a :: real and Y :: "slp_point set" and f :: slp_scalar_field
  assumes exponent_positive: "0 < a"
    and set_measurable: "Y \<in> sets lborel"
    and set_bounded: "bounded Y"
    and field_lp: "aim_complex_lp_on_plane a f"
    and field_support: "\<And>x. f x \<noteq> 0 \<Longrightarrow> x \<in> Y"
  shows "\<exists>g::nat \<Rightarrow> slp_scalar_field.
      (\<forall>n. aim_complex_lp_on_plane a (g n) \<and> integrable lborel (g n) \<and>
        aim_complex_lp_on_plane 2 (g n) \<and> (\<forall>x. g n x \<noteq> 0 \<longrightarrow> x \<in> Y)) \<and>
      ((\<lambda>n. aim_complex_lp_norm a (\<lambda>x. f x - g n x)) \<longlonglongrightarrow> 0)"
proof -
  let ?g = "\<lambda>n::nat. \<lambda>x. if norm (f x) \<le> real (Suc n) then f x else 0"
  have field_measurable: "f \<in> borel_measurable lborel"
    using field_lp unfolding aim_complex_lp_on_plane_def by blast
  have g_measurable: "?g n \<in> borel_measurable lborel" for n
    using field_measurable by measurable
  have g_support: "x \<in> Y" if "?g n x \<noteq> 0" for n x
    using that field_support[of x] by (auto split: if_splits)
  have g_bound: "norm (?g n x) \<le> real (Suc n)" for n x
    by (simp split: if_splits)
  have g_restricted: "slp_restrict_field Y (?g n) = ?g n" for n
  proof (rule ext)
    fix x :: slp_point
    show "slp_restrict_field Y (?g n) x = ?g n x"
    proof (cases "x \<in> Y")
      case True
      show ?thesis using True by (simp add: slp_restrict_field_def)
    next
      case False
      have zero: "?g n x = 0"
        using g_support[where n=n and x=x] False by blast
      show ?thesis using False zero by (simp add: slp_restrict_field_def)
    qed
  qed
  have g_l2: "aim_complex_lp_on_plane 2 (?g n)" for n
  proof -
    have restricted_l2: "aim_complex_lp_on_plane 2 (slp_restrict_field Y (?g n))"
      by (rule slp_bounded_restriction_lp_norm(1)[
          where A="real (Suc n)", OF _ set_measurable set_bounded g_measurable])
        (simp_all add: g_bound)
    show ?thesis using restricted_l2 by (simp only: g_restricted)
  qed
  have g_integrable: "integrable lborel (?g n)" for n
    by (rule slp_bounded_supported_lp_integrable[
        where p=2 and Y=Y, OF _ set_measurable set_bounded g_l2 g_support]) simp
  have g_lp: "aim_complex_lp_on_plane a (?g n)" for n
    by (rule slp_value_truncation_lp(1)[OF exponent_positive field_lp])
  have data: "\<forall>n. aim_complex_lp_on_plane a (?g n) \<and> integrable lborel (?g n) \<and>
      aim_complex_lp_on_plane 2 (?g n) \<and> (\<forall>x. ?g n x \<noteq> 0 \<longrightarrow> x \<in> Y)"
    using g_lp g_integrable g_l2 g_support by blast
  have approximation:
      "(\<lambda>n. aim_complex_lp_norm a (\<lambda>x. f x - ?g n x)) \<longlonglongrightarrow> 0"
    by (rule slp_value_truncation_norm_tendsto_zero[OF exponent_positive field_lp])
  show ?thesis by (rule exI[of _ ?g], rule conjI[OF data approximation])
qed

end
