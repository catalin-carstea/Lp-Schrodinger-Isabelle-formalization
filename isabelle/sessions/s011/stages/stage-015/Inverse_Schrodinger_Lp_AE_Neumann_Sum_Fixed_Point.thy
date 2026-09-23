theory Inverse_Schrodinger_Lp_AE_Neumann_Sum_Fixed_Point
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Measurable_Geometric_Series_Esssup_Tail"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Almost-everywhere Neumann sums under a raw contraction\<close>

definition slp_ae_bounded_measurable ::
    "'x measure \<Rightarrow> real \<Rightarrow> ('x \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> bool" where
  "slp_ae_bounded_measurable M K f \<longleftrightarrow>
    0 \<le> K \<and> f \<in> borel_measurable M \<and> (AE x in M. norm (f x) \<le> K)"

lemma slp_ae_bounded_measurable_zero:
  "slp_ae_bounded_measurable M 0
    (\<lambda>_ :: 'x. 0 :: 'b::{real_normed_vector, second_countable_topology})"
  unfolding slp_ae_bounded_measurable_def
  by measurable

lemma slp_ae_bounded_measurable_add:
  fixes f g :: "'x \<Rightarrow> 'b::{real_normed_vector, second_countable_topology}"
  assumes f_bound: "slp_ae_bounded_measurable M K f"
    and g_bound: "slp_ae_bounded_measurable M L g"
  shows "slp_ae_bounded_measurable M (K + L) (\<lambda>x. f x + g x)"
proof -
  have K_nonnegative: "0 \<le> K"
    and f_measurable: "f \<in> borel_measurable M"
    and f_AE: "AE x in M. norm (f x) \<le> K"
    using f_bound unfolding slp_ae_bounded_measurable_def by blast+
  have L_nonnegative: "0 \<le> L"
    and g_measurable: "g \<in> borel_measurable M"
    and g_AE: "AE x in M. norm (g x) \<le> L"
    using g_bound unfolding slp_ae_bounded_measurable_def by blast+
  have sum_AE: "AE x in M. norm (f x + g x) \<le> K + L"
    using f_AE g_AE
  proof eventually_elim
    fix x
    assume fx: "norm (f x) \<le> K" and gx: "norm (g x) \<le> L"
    have "norm (f x + g x) \<le> norm (f x) + norm (g x)"
      by (rule norm_triangle_ineq)
    also have "... \<le> K + L"
      using fx gx by simp
    finally show "norm (f x + g x) \<le> K + L" .
  qed
  show ?thesis
    unfolding slp_ae_bounded_measurable_def
  proof (intro conjI)
    show "0 \<le> K + L"
      using K_nonnegative L_nonnegative by simp
    show "(\<lambda>x. f x + g x) \<in> borel_measurable M"
      using f_measurable g_measurable by measurable
    show "AE x in M. norm (f x + g x) \<le> K + L"
      by (rule sum_AE)
  qed
qed

lemma slp_ae_bounded_measurable_diff:
  fixes f g :: "'x \<Rightarrow> 'b::{real_normed_vector, second_countable_topology}"
  assumes f_bound: "slp_ae_bounded_measurable M K f"
    and g_bound: "slp_ae_bounded_measurable M L g"
  shows "slp_ae_bounded_measurable M (K + L) (\<lambda>x. f x - g x)"
proof -
  have L_nonnegative: "0 \<le> L"
    and g_measurable: "g \<in> borel_measurable M"
    and g_AE: "AE x in M. norm (g x) \<le> L"
    using g_bound unfolding slp_ae_bounded_measurable_def by blast+
  have minus_measurable: "(\<lambda>x. - g x) \<in> borel_measurable M"
    using g_measurable by measurable
  have minus_AE: "AE x in M. norm (- g x) \<le> L"
    using g_AE by eventually_elim simp
  have minus_g:
      "slp_ae_bounded_measurable M L (\<lambda>x. - g x)"
    unfolding slp_ae_bounded_measurable_def
    using L_nonnegative minus_measurable minus_AE by blast
  have "slp_ae_bounded_measurable M (K + L)
      (\<lambda>x. f x + (- g x))"
    by (rule slp_ae_bounded_measurable_add[OF f_bound minus_g])
  then show ?thesis
    by simp
qed

theorem slp_ae_neumann_sum_fixed_point:
  fixes M :: "'x measure"
    and U :: "nat \<Rightarrow> 'x \<Rightarrow> 'b::{banach, second_countable_topology}"
    and S :: "('x \<Rightarrow> 'b) \<Rightarrow> 'x \<Rightarrow> 'b"
    and W :: "'x \<Rightarrow> 'b"
    and P rho kappa :: real
  assumes terms_measurable:
      "\<And>j. U j \<in> borel_measurable M"
    and P_nonnegative: "0 \<le> P"
    and rho_nonnegative: "0 \<le> rho"
    and rho_strict: "rho < 1"
    and term_bound:
      "\<And>j. AE x in M. norm (U j x) \<le> P * rho ^ j"
    and recurrence:
      "\<And>j. AE x in M. U (Suc j) x = S (U j) x"
    and kappa_nonnegative: "0 \<le> kappa"
    and kappa_strict: "kappa < 1"
    and operator_closed:
      "\<And>K f. slp_ae_bounded_measurable M K f \<Longrightarrow>
        S f \<in> borel_measurable M"
    and operator_difference:
      "\<And>K L f g.
        slp_ae_bounded_measurable M K f \<Longrightarrow>
        slp_ae_bounded_measurable M L g \<Longrightarrow>
        AE x in M. S (\<lambda>y. f y - g y) x = S f x - S g x"
    and operator_contraction:
      "\<And>K f. slp_ae_bounded_measurable M K f \<Longrightarrow>
        AE x in M. norm (S f x) \<le> kappa * K"
  defines W_def: "W \<equiv> (\<lambda>x. \<Sum>j. U j x)"
  shows operator_sum_measurable:
      "S W \<in> borel_measurable M"
    and operator_series_summable_AE:
      "AE x in M. summable (\<lambda>j. S (U j) x)"
    and operator_transports_sum_AE:
      "AE x in M. S W x = (\<Sum>j. S (U j) x)"
    and fixed_point_AE:
      "AE x in M. W x = U 0 x + S W x"
proof -
  have geometric:
      "summable (\<lambda>j. rho ^ j)"
  proof -
    have "norm rho < 1"
      using rho_nonnegative rho_strict
      by (simp add: real_norm_def abs_of_nonneg)
    then show ?thesis
      by (rule summable_geometric)
  qed
  have majorant_summable:
      "summable (\<lambda>j. P * rho ^ j)"
    by (rule summable_mult[OF geometric])
  have denominator_positive: "0 < 1 - rho"
    using rho_strict by simp
  have denominator_nonnegative: "0 \<le> 1 - rho"
    using denominator_positive by simp
  have all_bounds:
      "AE x in M. \<forall>j. norm (U j x) \<le> P * rho ^ j"
    using term_bound unfolding AE_all_countable by blast

  note bridge = slp_measurable_geometric_series_esssup_tail[
    OF terms_measurable P_nonnegative rho_nonnegative rho_strict term_bound]
  have W_measurable: "W \<in> borel_measurable M"
    unfolding W_def by (rule bridge(1))
  have U_summable_AE:
      "AE x in M. summable (\<lambda>j. U j x)"
    by (rule bridge(3))

  let ?B = "\<lambda>N. \<Sum>j<N. P * rho ^ j"
  let ?partial = "\<lambda>N x. \<Sum>j<N. U j x"
  have term_admissible:
      "slp_ae_bounded_measurable M (P * rho ^ j) (U j)" for j
    unfolding slp_ae_bounded_measurable_def
    using P_nonnegative rho_nonnegative terms_measurable[of j] term_bound[of j]
    by simp
  have partial_admissible:
      "slp_ae_bounded_measurable M (?B N) (?partial N)" for N
  proof (induct N)
    case 0
    show ?case
      by (simp add: slp_ae_bounded_measurable_zero)
  next
    case (Suc N)
    have added:
        "slp_ae_bounded_measurable M (?B N + P * rho ^ N)
          (\<lambda>x. ?partial N x + U N x)"
      by (rule slp_ae_bounded_measurable_add[
            OF Suc term_admissible])
    show ?case
      using added by (simp add: sum.lessThan_Suc)
  qed

  have W_bound_AE:
      "AE x in M. norm (W x) \<le> P / (1 - rho)"
  proof -
    have esssup_bound:
        "esssup M (\<lambda>x. ereal (norm (W x)))
          \<le> ereal (P / (1 - rho))"
      using bridge(4)[of 0]
      unfolding W_def by simp
    have below:
        "AE x in M. ereal (norm (W x)) \<le>
          esssup M (\<lambda>y. ereal (norm (W y)))"
      by (rule esssup_AE)
    show ?thesis
      using below
    proof eventually_elim
      fix x
      assume at_x:
          "ereal (norm (W x)) \<le>
            esssup M (\<lambda>y. ereal (norm (W y)))"
      have "ereal (norm (W x)) \<le> ereal (P / (1 - rho))"
        by (rule order_trans[OF at_x esssup_bound])
      then show "norm (W x) \<le> P / (1 - rho)"
        by simp
    qed
  qed
  have W_admissible:
      "slp_ae_bounded_measurable M (P / (1 - rho)) W"
    unfolding slp_ae_bounded_measurable_def
    using P_nonnegative denominator_nonnegative W_measurable W_bound_AE
    by simp

  have S_W_measurable: "S W \<in> borel_measurable M"
    by (rule operator_closed[OF W_admissible])

  have zero_image_AE:
      "AE x in M. S (\<lambda>_ :: 'x. 0 :: 'b) x = 0"
  proof -
    have contracted:
        "AE x in M. norm (S (\<lambda>_ :: 'x. 0 :: 'b) x)
          \<le> kappa * 0"
      by (rule operator_contraction[OF slp_ae_bounded_measurable_zero])
    show ?thesis
      using contracted by eventually_elim simp
  qed

  have operator_add:
      "slp_ae_bounded_measurable M K f \<Longrightarrow>
       slp_ae_bounded_measurable M L g \<Longrightarrow>
       AE x in M. S (\<lambda>y. f y + g y) x = S f x + S g x"
    for K L f g
  proof -
    assume f_admissible: "slp_ae_bounded_measurable M K f"
      and g_admissible: "slp_ae_bounded_measurable M L g"
    have fg_admissible:
        "slp_ae_bounded_measurable M (K + L) (\<lambda>x. f x + g x)"
      by (rule slp_ae_bounded_measurable_add[
            OF f_admissible g_admissible])
    have difference_AE:
        "AE x in M.
          S (\<lambda>y. (f y + g y) - g y) x =
            S (\<lambda>y. f y + g y) x - S g x"
      by (rule operator_difference[OF fg_admissible g_admissible])
    show ?thesis
      using difference_AE
      by eventually_elim (simp add: eq_diff_eq)
  qed

  have finite_transport:
      "AE x in M.
        S (?partial N) x = (\<Sum>j<N. U (Suc j) x)" for N
  proof (induct N)
    case 0
    show ?case
      using zero_image_AE by simp
  next
    case (Suc N)
    have add_AE:
        "AE x in M.
          S (\<lambda>y. ?partial N y + U N y) x =
            S (?partial N) x + S (U N) x"
      by (rule operator_add[OF partial_admissible term_admissible])
    show ?case
      using Suc add_AE recurrence[of N]
      by eventually_elim (simp add: sum.lessThan_Suc)
  qed
  have finite_transport_all:
      "AE x in M. \<forall>N.
        S (?partial N) x = (\<Sum>j<N. U (Suc j) x)"
    using finite_transport unfolding AE_all_countable by blast
  have recurrence_all:
      "AE x in M. \<forall>j. U (Suc j) x = S (U j) x"
    using recurrence unfolding AE_all_countable by blast

  have tail_admissible:
      "slp_ae_bounded_measurable M
        (P * rho ^ N / (1 - rho))
        (\<lambda>x. W x - ?partial N x)" for N
  proof -
    have rate_nonnegative:
        "0 \<le> P * rho ^ N / (1 - rho)"
      using P_nonnegative rho_nonnegative denominator_nonnegative by simp
    have tail_measurable:
        "(\<lambda>x. W x - ?partial N x) \<in> borel_measurable M"
      using W_measurable terms_measurable by measurable
    have esssup_bound:
        "esssup M
          (\<lambda>x. ereal (norm (W x - ?partial N x)))
          \<le> ereal (P * rho ^ N / (1 - rho))"
      using bridge(4)[of N]
      unfolding W_def by simp
    have below:
        "AE x in M.
          ereal (norm (W x - ?partial N x)) \<le>
            esssup M (\<lambda>y. ereal (norm (W y - ?partial N y)))"
      by (rule esssup_AE)
    have tail_AE:
        "AE x in M.
          norm (W x - ?partial N x)
            \<le> P * rho ^ N / (1 - rho)"
      using below
    proof eventually_elim
      fix x
      assume at_x:
          "ereal (norm (W x - ?partial N x)) \<le>
            esssup M (\<lambda>y. ereal (norm (W y - ?partial N y)))"
      have "ereal (norm (W x - ?partial N x))
          \<le> ereal (P * rho ^ N / (1 - rho))"
        by (rule order_trans[OF at_x esssup_bound])
      then show
          "norm (W x - ?partial N x)
            \<le> P * rho ^ N / (1 - rho)"
        by simp
    qed
    show ?thesis
      unfolding slp_ae_bounded_measurable_def
      using rate_nonnegative tail_measurable tail_AE by blast
  qed

  have operator_tail_AE:
      "AE x in M.
        norm (S W x - S (?partial N) x)
          \<le> kappa * (P * rho ^ N / (1 - rho))" for N
  proof -
    have difference_AE:
        "AE x in M.
          S (\<lambda>y. W y - ?partial N y) x =
            S W x - S (?partial N) x"
      by (rule operator_difference[OF W_admissible partial_admissible])
    have contracted_AE:
        "AE x in M.
          norm (S (\<lambda>y. W y - ?partial N y) x)
            \<le> kappa * (P * rho ^ N / (1 - rho))"
      by (rule operator_contraction[OF tail_admissible])
    show ?thesis
      using difference_AE contracted_AE
      by eventually_elim simp
  qed
  have operator_tail_all:
      "AE x in M. \<forall>N.
        norm (S W x - S (?partial N) x)
          \<le> kappa * (P * rho ^ N / (1 - rho))"
    using operator_tail_AE unfolding AE_all_countable by blast

  have numerator_limit:
      "((\<lambda>N. P * rho ^ N) \<longlongrightarrow> 0) sequentially"
    by (rule summable_LIMSEQ_zero[OF majorant_summable])
  have denominator_limit:
      "((\<lambda>_ :: nat. 1 - rho) \<longlongrightarrow> 1 - rho) sequentially"
    by (rule tendsto_const)
  have denominator_nonzero: "1 - rho \<noteq> 0"
    using denominator_positive by simp
  have tail_rate_limit:
      "((\<lambda>N. P * rho ^ N / (1 - rho)) \<longlongrightarrow> 0)
        sequentially"
    using tendsto_divide[
      OF numerator_limit denominator_limit denominator_nonzero]
    by simp
  have contracted_tail_limit:
      "((\<lambda>N. kappa * (P * rho ^ N / (1 - rho)))
        \<longlongrightarrow> 0) sequentially"
    using tendsto_mult_left[OF tail_rate_limit] by simp

  have image_sum_AE:
      "AE x in M.
        S W x = (\<Sum>j. U (Suc j) x)"
    using finite_transport_all operator_tail_all
  proof eventually_elim
    fix x
    assume finite_at_x:
        "\<forall>N. S (?partial N) x = (\<Sum>j<N. U (Suc j) x)"
      and tail_at_x:
        "\<forall>N. norm (S W x - S (?partial N) x)
          \<le> kappa * (P * rho ^ N / (1 - rho))"
    have norm_limit:
        "((\<lambda>N. norm (S W x - S (?partial N) x))
          \<longlongrightarrow> 0) sequentially"
    proof (rule tendsto_sandwich[
        where f = "\<lambda>_. 0" and
          h = "\<lambda>N. kappa * (P * rho ^ N / (1 - rho))"])
      show "\<forall>\<^sub>F N in sequentially.
          0 \<le> norm (S W x - S (?partial N) x)"
        by simp
      show "\<forall>\<^sub>F N in sequentially.
          norm (S W x - S (?partial N) x)
            \<le> kappa * (P * rho ^ N / (1 - rho))"
      proof (rule eventuallyI)
        fix N
        show "norm (S W x - S (?partial N) x)
            \<le> kappa * (P * rho ^ N / (1 - rho))"
          by (rule tail_at_x[rule_format])
      qed
      show "((\<lambda>_ :: nat. 0 :: real) \<longlongrightarrow> 0) sequentially"
        by (rule tendsto_const)
      show "((\<lambda>N. kappa * (P * rho ^ N / (1 - rho)))
          \<longlongrightarrow> 0) sequentially"
        by (rule contracted_tail_limit)
    qed
    have difference_limit:
        "((\<lambda>N. S W x - S (?partial N) x)
          \<longlongrightarrow> 0) sequentially"
      using norm_limit tendsto_norm_zero_iff by blast
    have reversed_limit:
        "((\<lambda>N. - (S W x - S (?partial N) x))
          \<longlongrightarrow> - 0) sequentially"
      by (rule tendsto_minus[OF difference_limit])
    have constant_image_limit:
        "((\<lambda>_ :: nat. S W x) \<longlongrightarrow> S W x) sequentially"
      by (rule tendsto_const)
    have partial_limit:
        "((\<lambda>N. S (?partial N) x) \<longlongrightarrow> S W x)
          sequentially"
      using tendsto_add[OF reversed_limit constant_image_limit]
      by simp
    have shifted_sums:
        "(\<lambda>j. U (Suc j) x) sums S W x"
      unfolding sums_def
      using partial_limit finite_at_x by simp
    show "S W x = (\<Sum>j. U (Suc j) x)"
      by (rule sums_unique[OF shifted_sums])
  qed

  have operator_series_summable:
      "AE x in M. summable (\<lambda>j. S (U j) x)"
    using U_summable_AE recurrence_all
  proof eventually_elim
    fix x
    assume U_summable: "summable (\<lambda>j. U j x)"
      and recurrence_at_x: "\<forall>j. U (Suc j) x = S (U j) x"
    have shifted_summable: "summable (\<lambda>j. U (Suc j) x)"
      by (subst summable_Suc_iff) (rule U_summable)
    have sequence_eq:
        "(\<lambda>j. S (U j) x) = (\<lambda>j. U (Suc j) x)"
      using recurrence_at_x by auto
    show "summable (\<lambda>j. S (U j) x)"
      unfolding sequence_eq by (rule shifted_summable)
  qed

  have operator_transports_sum:
      "AE x in M. S W x = (\<Sum>j. S (U j) x)"
    using image_sum_AE recurrence_all
  proof eventually_elim
    fix x
    assume image_sum: "S W x = (\<Sum>j. U (Suc j) x)"
      and recurrence_at_x: "\<forall>j. U (Suc j) x = S (U j) x"
    have sequence_eq:
        "(\<lambda>j. S (U j) x) = (\<lambda>j. U (Suc j) x)"
      using recurrence_at_x by auto
    show "S W x = (\<Sum>j. S (U j) x)"
      using image_sum unfolding sequence_eq .
  qed

  have fixed_point:
      "AE x in M. W x = U 0 x + S W x"
    using U_summable_AE image_sum_AE
  proof eventually_elim
    fix x
    assume U_summable: "summable (\<lambda>j. U j x)"
      and image_sum: "S W x = (\<Sum>j. U (Suc j) x)"
    have tail_split:
        "(\<Sum>j. U (Suc j) x) = (\<Sum>j. U j x) - U 0 x"
      by (rule suminf_split_head[OF U_summable])
    have split:
        "(\<Sum>j. U j x) = U 0 x + (\<Sum>j. U (Suc j) x)"
      using tail_split by simp
    have W_value: "W x = (\<Sum>j. U j x)"
      unfolding W_def by simp
    show "W x = U 0 x + S W x"
      using split image_sum W_value by simp
  qed

  show "S W \<in> borel_measurable M"
    by (rule S_W_measurable)
  show "AE x in M. summable (\<lambda>j. S (U j) x)"
    by (rule operator_series_summable)
  show "AE x in M. S W x = (\<Sum>j. S (U j) x)"
    by (rule operator_transports_sum)
  show "AE x in M. W x = U 0 x + S W x"
    by (rule fixed_point)
qed

end
