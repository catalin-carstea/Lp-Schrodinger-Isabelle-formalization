theory Inverse_Schrodinger_Lp_Born_Root_Bounded_Support
  imports Inverse_Schrodinger_Lp_Born_One_Sided_Root_Density
begin

section \<open>Finite propagation of positive branch-output densities\<close>

lemma slp_positive_output_density_outside:
  assumes radius_nonnegative: "0 \<le> R"
    and output_outside:
      "real (Suc n) * R < norm (out - origin)"
  shows
    "slp_positive_output_density R cutoff potential terminal_weight n
        origin out = 0"
  using output_outside
proof (induction n arbitrary: origin out)
  case 0
  have kernel_zero:
      "slp_localized_cauchy_kernel R (origin - out) = 0"
  proof (rule slp_localized_cauchy_kernel_outside)
    have "R < norm (out - origin)"
      using 0 radius_nonnegative by simp
    then show "R < norm (origin - out)"
      by (simp only: norm_minus_commute)
  qed
  show ?case
    by (simp add: kernel_zero)
next
  case (Suc n)
  have integrand_zero:
      "ennreal (slp_localized_cauchy_kernel R (origin - pos_point)) *
          ennreal (norm (cutoff pos_point)) *
          ennreal (slp_localized_cauchy_kernel R (pos_point - neg_point)) *
          ennreal (norm (potential neg_point)) *
          slp_positive_output_density R cutoff potential terminal_weight n
            neg_point (out - pos_point + neg_point) = 0"
    for pos_point neg_point
  proof (cases "R < norm (origin - pos_point)")
    case True
    then have
      "slp_localized_cauchy_kernel R (origin - pos_point) = 0"
      by (rule slp_localized_cauchy_kernel_outside)
    then show ?thesis by simp
  next
    case False
    have near_origin: "norm (pos_point - origin) \<le> R"
      using False by (simp add: norm_minus_commute)
    have triangle:
        "norm (out - origin) \<le>
          norm (out - pos_point) + norm (pos_point - origin)"
      using norm_triangle_ineq[of "out - pos_point" "pos_point - origin"]
      by (simp add: algebra_simps)
    have recursive_outside:
        "real (Suc n) * R <
          norm ((out - pos_point + neg_point) - neg_point)"
      using Suc.prems triangle near_origin radius_nonnegative
      by (simp add: algebra_simps of_nat_Suc; linarith)
    have recursive_zero:
        "slp_positive_output_density R cutoff potential terminal_weight n
            neg_point (out - pos_point + neg_point) = 0"
      by (rule Suc.IH[OF recursive_outside])
    show ?thesis by (simp add: recursive_zero)
  qed
  show ?case
    by (simp add: integrand_zero)
qed

theorem slp_positive_root_output_density_bounded_support:
  assumes radius_nonnegative: "0 \<le> R"
    and root_support: "bounded {root. root_weight root \<noteq> 0}"
  shows
    "bounded {out.
      slp_positive_root_output_density R cutoff potential terminal_weight n
        root_weight out \<noteq> 0}"
proof -
  obtain B where root_bound:
      "\<And>root. root_weight root \<noteq> 0 \<Longrightarrow> norm root \<le> B"
    using root_support unfolding bounded_iff by auto
  let ?B = "max 0 B"
  let ?K = "?B + real (Suc n) * R"
  have K_nonnegative: "0 \<le> ?K"
    using radius_nonnegative by simp
  have output_bound:
      "norm out \<le> ?K"
    if output_nonzero:
      "slp_positive_root_output_density R cutoff potential terminal_weight n
        root_weight out \<noteq> 0"
    for out
  proof (rule ccontr)
    assume not_bounded: "\<not> norm out \<le> ?K"
    have integrand_zero:
        "ennreal (norm (root_weight root)) *
          slp_positive_output_density R cutoff potential terminal_weight n
            root out = 0"
      for root
    proof (cases "root_weight root = 0")
      case True
      then show ?thesis by simp
    next
      case False
      have root_bound_max: "norm root \<le> ?B"
        using root_bound[OF False] by simp
      have triangle:
          "norm out \<le> norm (out - root) + norm root"
        using norm_triangle_ineq[of "out - root" root]
        by simp
      have outside:
          "real (Suc n) * R < norm (out - root)"
        using not_bounded triangle root_bound_max by linarith
      have density_zero:
          "slp_positive_output_density R cutoff potential terminal_weight n
            root out = 0"
        by (rule slp_positive_output_density_outside[OF
              radius_nonnegative outside])
      show ?thesis by (simp add: density_zero)
    qed
    have root_density_zero:
        "slp_positive_root_output_density R cutoff potential terminal_weight n
          root_weight out = 0"
      unfolding slp_positive_root_output_density_def
      by (simp add: integrand_zero)
    show False using output_nonzero root_density_zero by contradiction
  qed
  show ?thesis
    unfolding bounded_iff
  proof (rule exI[of _ ?K], intro ballI)
    fix out
    assume out_in:
      "out \<in> {out.
        slp_positive_root_output_density R cutoff potential terminal_weight n
          root_weight out \<noteq> 0}"
    show "norm out \<le> ?K"
      by (rule output_bound) (use out_in in simp)
  qed
qed

end
