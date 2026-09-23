theory Inverse_Schrodinger_Lp_Supported_Value_Approximation_Two_Exponents
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Supported_Value_Truncations"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Simultaneous low/high value approximation of a supported coefficient\<close>

theorem slp_supported_value_approximation_two_exponents:
  fixes p a b :: real
    and Y :: "slp_point set"
    and f :: slp_scalar_field
  assumes p_positive: "0 < p"
    and a_positive: "0 < a"
    and b_positive: "0 < b"
    and Y_measurable: "Y \<in> sets lborel"
    and Y_bounded: "bounded Y"
    and f_lp: "aim_complex_lp_on_plane p f"
    and f_support: "\<And>x. f x \<noteq> 0 \<Longrightarrow> x \<in> Y"
  shows
    "\<exists>g::nat \<Rightarrow> slp_scalar_field.
      (\<forall>n x. g n x =
        (if norm (f x) \<le> real (Suc n) then f x else 0))
      \<and> (\<forall>n.
        aim_complex_lp_on_plane p (g n)
        \<and> aim_complex_lp_on_plane a (g n)
        \<and> aim_complex_lp_on_plane b (g n)
        \<and> (\<forall>x. g n x \<noteq> 0 \<longrightarrow> x \<in> Y))
      \<and> ((\<lambda>n. aim_complex_lp_norm p (\<lambda>x. f x - g n x))
        \<longlonglongrightarrow> 0)"
proof -
  let ?g = "\<lambda>n::nat. \<lambda>x.
    if norm (f x) \<le> real (Suc n) then f x else 0"
  have f_measurable: "f \<in> borel_measurable lborel"
    using f_lp unfolding aim_complex_lp_on_plane_def by blast
  have g_measurable: "?g n \<in> borel_measurable lborel" for n
    using f_measurable by measurable
  have g_bound: "norm (?g n x) \<le> real (Suc n)" for n x
    by (simp split: if_splits)
  have g_support: "?g n x \<noteq> 0 \<Longrightarrow> x \<in> Y" for n x
    by (auto intro: f_support split: if_splits)
  have g_restricted: "slp_restrict_field Y (?g n) = ?g n" for n
  proof (rule ext)
    fix x :: slp_point
    show "slp_restrict_field Y (?g n) x = ?g n x"
    proof (cases "x \<in> Y")
      case True
      then show ?thesis by (simp add: slp_restrict_field_def)
    next
      case False
      have "?g n x = 0"
        using False g_support[where n=n and x=x] by blast
      with False show ?thesis by (simp add: slp_restrict_field_def)
    qed
  qed
  have g_at_exponent:
      "aim_complex_lp_on_plane r (?g n)"
    if r_positive: "0 < r" for r n
  proof -
    have restricted:
        "aim_complex_lp_on_plane r (slp_restrict_field Y (?g n))"
      by (rule slp_bounded_restriction_lp_norm(1)[
            where A="real (Suc n)", OF r_positive Y_measurable Y_bounded
              g_measurable])
        (simp_all add: g_bound)
    show ?thesis using restricted by (simp only: g_restricted)
  qed
  have g_p: "aim_complex_lp_on_plane p (?g n)" for n
    by (rule slp_value_truncation_lp(1)[OF p_positive f_lp])
  have g_a: "aim_complex_lp_on_plane a (?g n)" for n
    by (rule g_at_exponent[OF a_positive])
  have g_b: "aim_complex_lp_on_plane b (?g n)" for n
    by (rule g_at_exponent[OF b_positive])
  have approximation:
      "((\<lambda>n. aim_complex_lp_norm p (\<lambda>x. f x - ?g n x))
        \<longlonglongrightarrow> 0)"
    by (rule slp_value_truncation_norm_tendsto_zero[OF p_positive f_lp])
  show ?thesis
    by (rule exI[of _ ?g])
      (use g_p g_a g_b g_support approximation in auto)
qed

end
