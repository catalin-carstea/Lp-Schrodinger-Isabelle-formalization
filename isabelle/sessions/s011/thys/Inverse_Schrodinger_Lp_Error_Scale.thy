theory Inverse_Schrodinger_Lp_Error_Scale
  imports Inverse_Schrodinger_Lp_Cauchy_Holder_Continuity
begin

section \<open>Positive scales for vanishing power errors\<close>

definition slp_regularized_error_scale ::
    "real \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real" where
  "slp_regularized_error_scale b e n =
    (e n + inverse (real (Suc n))) powr (1 / (2 * b))"

lemma slp_regularized_error_scale_positive:
  assumes exponent: "2 < b"
    and error_nonnegative: "\<And>n. 0 \<le> e n"
  shows "0 < slp_regularized_error_scale b e n"
proof -
  have inverse_positive: "0 < inverse (real (Suc n))"
    by simp
  have base_positive: "0 < e n + inverse (real (Suc n))"
    using error_nonnegative[of n] inverse_positive by linarith
  show ?thesis
    using base_positive
    by (simp add: slp_regularized_error_scale_def)
qed

lemma slp_regularized_error_scale_tendsto_zero:
  assumes exponent: "2 < b"
    and error_nonnegative: "\<And>n. 0 \<le> e n"
    and error_limit: "(e \<longlongrightarrow> 0) sequentially"
  shows "((\<lambda>n. slp_regularized_error_scale b e n)
    \<longlongrightarrow> 0) sequentially"
proof -
  have b_positive: "0 < b"
    using exponent by linarith
  have exponent_positive: "0 < 1 / (2 * b)"
    using b_positive by (intro divide_pos_pos) auto
  have regularized_limit:
      "((\<lambda>n. e n + inverse (real (Suc n)))
        \<longlongrightarrow> 0) sequentially"
    using tendsto_add[OF error_limit LIMSEQ_inverse_real_of_nat]
    by simp
  have regularized_nonnegative:
      "\<And>n. 0 \<le> e n + inverse (real (Suc n))"
    using error_nonnegative by simp
  have "((\<lambda>n. (e n + inverse (real (Suc n))) powr
        (1 / (2 * b))) \<longlongrightarrow>
      0 powr (1 / (2 * b))) sequentially"
    by (rule tendsto_powr2[OF regularized_limit tendsto_const])
       (use regularized_nonnegative exponent_positive in auto)
  then show ?thesis
    using exponent_positive
    by (simp add: slp_regularized_error_scale_def)
qed

lemma slp_regularized_error_scale_cancellation:
  fixes b x :: real
  assumes exponent: "2 < b"
    and x_positive: "0 < x"
  shows "x * (inverse (x powr (1 / (2 * b)))) powr b =
    x powr (1 / 2)"
proof -
  have b_nonzero: "b \<noteq> 0"
    using exponent by linarith
  have "x * (inverse (x powr (1 / (2 * b)))) powr b =
        x * (x powr (- (1 / (2 * b)))) powr b"
    by (simp only: powr_minus[symmetric])
  also have "... = x * x powr (- (1 / (2 * b)) * b)"
    by (simp only: powr_powr)
  also have "... = x powr (1 + (- (1 / (2 * b)) * b))"
    by (rule powr_mult_base) (use x_positive in linarith)
  also have "... = x powr (1 / 2)"
    using b_nonzero by (simp add: field_simps)
  finally show ?thesis .
qed

theorem slp_regularized_error_scale_absorbs_error:
  assumes exponent: "2 < b"
    and error_nonnegative: "\<And>n. 0 \<le> e n"
    and error_limit: "(e \<longlongrightarrow> 0) sequentially"
  shows "((\<lambda>n. e n *
      (inverse (slp_regularized_error_scale b e n)) powr b)
    \<longlongrightarrow> 0) sequentially"
proof -
  let ?s = "\<lambda>n. e n + inverse (real (Suc n))"
  have regularized_limit: "(?s \<longlongrightarrow> 0) sequentially"
    using tendsto_add[OF error_limit LIMSEQ_inverse_real_of_nat]
    by simp
  have regularized_positive: "0 < ?s n" for n
    using error_nonnegative[of n] inverse_Suc[of n, where 'a = real]
    by linarith
  have regularized_nonnegative: "0 \<le> ?s n" for n
    using regularized_positive[of n] by linarith
  have upper_limit:
      "((\<lambda>n. ?s n powr (1 / 2)) \<longlongrightarrow> 0) sequentially"
  proof -
    have "((\<lambda>n. ?s n powr (1 / 2)) \<longlongrightarrow>
        0 powr (1 / 2)) sequentially"
      by (rule tendsto_powr2[OF regularized_limit tendsto_const])
         (use regularized_nonnegative in auto)
    then show ?thesis by simp
  qed
  have scaled_nonnegative:
      "0 \<le> e n *
        (inverse (slp_regularized_error_scale b e n)) powr b" for n
  proof (rule mult_nonneg_nonneg)
    show "0 \<le> e n"
      by (rule error_nonnegative)
    show "0 \<le> (inverse (slp_regularized_error_scale b e n)) powr b"
      by simp
  qed
  have scaled_upper:
      "e n * (inverse (slp_regularized_error_scale b e n)) powr b
        \<le> ?s n powr (1 / 2)" for n
  proof -
    have error_le: "e n \<le> ?s n"
      by simp
    have "e n * (inverse (slp_regularized_error_scale b e n)) powr b
        \<le> ?s n *
          (inverse (slp_regularized_error_scale b e n)) powr b"
      by (rule mult_right_mono[OF error_le]) simp
    also have "... = ?s n powr (1 / 2)"
      unfolding slp_regularized_error_scale_def
      by (rule slp_regularized_error_scale_cancellation[OF
            exponent regularized_positive])
    finally show ?thesis .
  qed
  show ?thesis
    by (rule tendsto_sandwich[where f = "\<lambda>_. 0" and
          h = "\<lambda>n. ?s n powr (1 / 2)"])
       (use scaled_nonnegative scaled_upper upper_limit in auto)
qed

end
