theory Inverse_Schrodinger_Lp_Neumann_Tails
  imports Inverse_Schrodinger_Lp_Mixed_Tail
begin

section \<open>Conditional analytic Neumann-tail closure\<close>

lemma slp_tendsto_zero_of_eventual_nonnegative_le:
  fixes actual model :: "real \<Rightarrow> real"
  assumes actual_nonnegative:
      "eventually (\<lambda>tau. 0 \<le> actual tau) at_top"
    and actual_le_model:
      "eventually (\<lambda>tau. actual tau \<le> model tau) at_top"
    and model_limit: "(model \<longlongrightarrow> 0) at_top"
  shows "(actual \<longlongrightarrow> 0) at_top"
proof -
  have zero_limit:
    "((\<lambda>_ :: real. 0 :: real) \<longlongrightarrow> 0) at_top"
    by (rule tendsto_const)
  show ?thesis
    by (rule tendsto_sandwich[
          OF actual_nonnegative actual_le_model zero_limit model_limit])
qed

theorem slp_neumann_tail_estimates_of_model_domination:
  fixes left_tail right_tail mixed_tail :: "real \<Rightarrow> real"
    and C C_tilde alpha s :: real
  assumes alpha_positive: "0 < alpha"
    and C_nonnegative: "0 \<le> C"
    and C_tilde_nonnegative: "0 \<le> C_tilde"
    and s_at_most_one: "s \<le> 1"
    and left_nonnegative:
      "eventually (\<lambda>tau. 0 \<le> left_tail tau) at_top"
    and right_nonnegative:
      "eventually (\<lambda>tau. 0 \<le> right_tail tau) at_top"
    and mixed_nonnegative:
      "eventually (\<lambda>tau. 0 \<le> mixed_tail tau) at_top"
    and left_domination:
      "eventually
        (\<lambda>tau.
          left_tail tau \<le> slp_one_sided_model_tail C alpha s tau)
        at_top"
    and right_domination:
      "eventually
        (\<lambda>tau.
          right_tail tau \<le>
            slp_one_sided_model_tail C_tilde alpha s tau)
        at_top"
    and mixed_domination:
      "eventually
        (\<lambda>tau.
          mixed_tail tau \<le>
            slp_mixed_model_tail C C_tilde alpha s tau)
        at_top"
  shows
    "(left_tail \<longlongrightarrow> 0) at_top \<and>
      (right_tail \<longlongrightarrow> 0) at_top \<and>
      (mixed_tail \<longlongrightarrow> 0) at_top"
proof -
  have left_model_limit:
    "(slp_one_sided_model_tail C alpha s \<longlongrightarrow> 0) at_top"
    by (rule slp_one_sided_model_tail_tendsto_zero[
          OF alpha_positive C_nonnegative s_at_most_one])
  have right_model_limit:
    "(slp_one_sided_model_tail C_tilde alpha s \<longlongrightarrow> 0)
      at_top"
    by (rule slp_one_sided_model_tail_tendsto_zero[
          OF alpha_positive C_tilde_nonnegative s_at_most_one])
  have mixed_model_limit:
    "(slp_mixed_model_tail C C_tilde alpha s \<longlongrightarrow> 0)
      at_top"
    by (rule slp_mixed_model_tail_tendsto_zero[
          OF alpha_positive C_nonnegative C_tilde_nonnegative])
  have left_limit: "(left_tail \<longlongrightarrow> 0) at_top"
    by (rule slp_tendsto_zero_of_eventual_nonnegative_le[
          OF left_nonnegative left_domination left_model_limit])
  have right_limit: "(right_tail \<longlongrightarrow> 0) at_top"
    by (rule slp_tendsto_zero_of_eventual_nonnegative_le[
          OF right_nonnegative right_domination right_model_limit])
  have mixed_limit: "(mixed_tail \<longlongrightarrow> 0) at_top"
    by (rule slp_tendsto_zero_of_eventual_nonnegative_le[
          OF mixed_nonnegative mixed_domination mixed_model_limit])
  show ?thesis
    using left_limit right_limit mixed_limit by blast
qed

end
