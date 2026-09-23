theory Inverse_Schrodinger_Lp_AE_Fixed_Point_Uniqueness
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_AE_Neumann_Sum_Fixed_Point"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Almost-everywhere uniqueness for contractive fixed points\<close>

theorem slp_ae_contraction_fixed_zero:
  fixes M :: "'x measure"
    and S :: "('x \<Rightarrow> 'b::{real_normed_vector, second_countable_topology})
      \<Rightarrow> 'x \<Rightarrow> 'b"
    and h :: "'x \<Rightarrow> 'b"
    and K kappa :: real
  assumes h_bound: "slp_ae_bounded_measurable M K h"
    and h_fixed: "AE x in M. h x = S h x"
    and kappa_nonnegative: "0 \<le> kappa"
    and kappa_strict: "kappa < 1"
    and operator_contraction:
      "\<And>J f. slp_ae_bounded_measurable M J f \<Longrightarrow>
        AE x in M. norm (S f x) \<le> kappa * J"
  shows "AE x in M. h x = 0"
proof -
  have improve_bound:
      "slp_ae_bounded_measurable M J h \<Longrightarrow>
        slp_ae_bounded_measurable M (kappa * J) h"
    for J
  proof -
    assume admissible: "slp_ae_bounded_measurable M J h"
    have J_nonnegative: "0 \<le> J"
      and h_measurable: "h \<in> borel_measurable M"
      using admissible unfolding slp_ae_bounded_measurable_def by blast+
    have contracted:
        "AE x in M. norm (S h x) \<le> kappa * J"
      by (rule operator_contraction[OF admissible])
    have improved_AE:
        "AE x in M. norm (h x) \<le> kappa * J"
      using h_fixed contracted
      by eventually_elim simp
    show ?thesis
      unfolding slp_ae_bounded_measurable_def
      using kappa_nonnegative J_nonnegative h_measurable improved_AE
      by simp
  qed

  have iterated_bound:
      "slp_ae_bounded_measurable M (kappa ^ n * K) h"
    for n
  proof (induct n)
    case 0
    show ?case
      using h_bound by simp
  next
    case (Suc n)
    have "slp_ae_bounded_measurable M
        (kappa * (kappa ^ n * K)) h"
      by (rule improve_bound[OF Suc])
    then show ?case
      by (simp add: power_Suc mult.assoc)
  qed

  have each_bound:
      "\<And>n. AE x in M. norm (h x) \<le> kappa ^ n * K"
    using iterated_bound unfolding slp_ae_bounded_measurable_def by blast
  have all_bounds:
      "AE x in M. \<forall>n. norm (h x) \<le> kappa ^ n * K"
    using each_bound unfolding AE_all_countable by blast

  have kappa_norm: "norm kappa < 1"
    using kappa_nonnegative kappa_strict
    by (simp add: real_norm_def abs_of_nonneg)
  have power_limit: "(\<lambda>n. kappa ^ n) \<longlonglongrightarrow> 0"
    by (rule LIMSEQ_power_zero[OF kappa_norm])
  have scaled_limit: "(\<lambda>n. kappa ^ n * K) \<longlonglongrightarrow> 0"
    using tendsto_mult_right[OF power_limit, where c=K]
    by simp

  show ?thesis
    using all_bounds
  proof eventually_elim
    fix x
    assume at_x: "\<forall>n. norm (h x) \<le> kappa ^ n * K"
    have nonpositive: "norm (h x) \<le> 0"
    proof (rule tendsto_lowerbound[OF scaled_limit])
      show "eventually (\<lambda>n. norm (h x) \<le> kappa ^ n * K)
          sequentially"
        using at_x by simp
      show "\<not> trivial_limit sequentially"
        by (rule trivial_limit_sequentially)
    qed
    show "h x = 0"
      using nonpositive by simp
  qed
qed

theorem slp_ae_affine_fixed_point_unique:
  fixes M :: "'x measure"
    and S :: "('x \<Rightarrow> 'b::{real_normed_vector, second_countable_topology})
      \<Rightarrow> 'x \<Rightarrow> 'b"
    and B f g :: "'x \<Rightarrow> 'b"
    and K L kappa :: real
  assumes f_bound: "slp_ae_bounded_measurable M K f"
    and g_bound: "slp_ae_bounded_measurable M L g"
    and f_fixed: "AE x in M. f x = B x + S f x"
    and g_fixed: "AE x in M. g x = B x + S g x"
    and kappa_nonnegative: "0 \<le> kappa"
    and kappa_strict: "kappa < 1"
    and operator_difference:
      "\<And>J H p q.
        slp_ae_bounded_measurable M J p \<Longrightarrow>
        slp_ae_bounded_measurable M H q \<Longrightarrow>
        AE x in M. S (\<lambda>y. p y - q y) x = S p x - S q x"
    and operator_contraction:
      "\<And>J h. slp_ae_bounded_measurable M J h \<Longrightarrow>
        AE x in M. norm (S h x) \<le> kappa * J"
  shows "AE x in M. f x = g x"
proof -
  have difference_bound:
      "slp_ae_bounded_measurable M (K + L) (\<lambda>x. f x - g x)"
    by (rule slp_ae_bounded_measurable_diff[OF f_bound g_bound])
  have difference_operator:
      "AE x in M.
        S (\<lambda>y. f y - g y) x = S f x - S g x"
    by (rule operator_difference[OF f_bound g_bound])
  have difference_fixed:
      "AE x in M.
        f x - g x = S (\<lambda>y. f y - g y) x"
    using f_fixed g_fixed difference_operator
    by eventually_elim simp
  have difference_zero:
      "AE x in M. f x - g x = 0"
    by (rule slp_ae_contraction_fixed_zero[
          where M=M and S=S and h="\<lambda>x. f x - g x"
            and K="K + L" and kappa=kappa,
          OF difference_bound difference_fixed kappa_nonnegative
            kappa_strict operator_contraction])
  show ?thesis
    using difference_zero by eventually_elim simp
qed

end
