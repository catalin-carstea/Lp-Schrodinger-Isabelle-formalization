theory Inverse_Schrodinger_Lp_NN_Integral_Fatou_Finite
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Damped_Center_Multiplier_L2_Limit"
begin

section \<open>A reusable nonnegative Fatou finiteness interface\<close>

lemma slp_nn_integral_le_liminf_of_AE_tendsto:
  fixes M :: "'a measure"
    and u :: "nat \<Rightarrow> 'a \<Rightarrow> ennreal"
    and v :: "'a \<Rightarrow> ennreal"
  assumes u_measurable:
      "\<And>n. u n \<in> borel_measurable M"
    and pointwise_limit:
      "AE x in M. (\<lambda>n. u n x) \<longlonglongrightarrow> v x"
  shows "(\<integral>\<^sup>+x. v x \<partial>M) \<le>
    liminf (\<lambda>n. \<integral>\<^sup>+x. u n x \<partial>M)"
proof -
  have ae_liminf:
      "AE x in M. liminf (\<lambda>n. u n x) = v x"
    using pointwise_limit
  proof eventually_elim
    fix x
    assume x_limit: "(\<lambda>n. u n x) \<longlonglongrightarrow> v x"
    show "liminf (\<lambda>n. u n x) = v x"
      by (rule lim_imp_Liminf[OF trivial_limit_sequentially x_limit])
  qed
  have "(\<integral>\<^sup>+x. v x \<partial>M) =
      (\<integral>\<^sup>+x. liminf (\<lambda>n. u n x) \<partial>M)"
    using ae_liminf by (intro nn_integral_cong_AE) auto
  also have "... \<le> liminf (\<lambda>n. \<integral>\<^sup>+x. u n x \<partial>M)"
    by (rule nn_integral_liminf[OF u_measurable])
  finally show ?thesis .
qed

lemma slp_nn_integral_finite_of_AE_tendsto:
  fixes M :: "'a measure"
    and u :: "nat \<Rightarrow> 'a \<Rightarrow> ennreal"
    and v :: "'a \<Rightarrow> ennreal"
  assumes u_measurable:
      "\<And>n. u n \<in> borel_measurable M"
    and pointwise_limit:
      "AE x in M. (\<lambda>n. u n x) \<longlonglongrightarrow> v x"
    and finite_liminf:
      "liminf (\<lambda>n. \<integral>\<^sup>+x. u n x \<partial>M) < \<infinity>"
  shows "(\<integral>\<^sup>+x. v x \<partial>M) < \<infinity>"
proof -
  have target_le:
      "(\<integral>\<^sup>+x. v x \<partial>M) \<le>
        liminf (\<lambda>n. \<integral>\<^sup>+x. u n x \<partial>M)"
    by (rule slp_nn_integral_le_liminf_of_AE_tendsto[OF
          u_measurable pointwise_limit])
  show ?thesis
    by (rule order_le_less_trans[OF target_le finite_liminf])
qed

end
