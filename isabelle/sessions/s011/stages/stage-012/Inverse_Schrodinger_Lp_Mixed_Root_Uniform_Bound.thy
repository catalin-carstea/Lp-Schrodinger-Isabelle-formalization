theory Inverse_Schrodinger_Lp_Mixed_Root_Uniform_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_All_Order_Restricted_Born_Gain"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Quantitative_Complex_Lp_Product"
begin

hide_const (open) Commutative_Ring.norm

section \<open>The common three-factor Holder estimate\<close>

lemma slp_complex_triple_holder_integral_bound:
  fixes p :: real and Q L R :: slp_scalar_field
  assumes p_lower: "1 < p"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and L_lp: "aim_complex_lp_on_plane (2 * slp_holder_conjugate p) L"
    and R_lp: "aim_complex_lp_on_plane (2 * slp_holder_conjugate p) R"
  shows "integrable lborel (\<lambda>x. Q x * L x * R x)"
    "norm (integral\<^sup>L lborel (\<lambda>x. Q x * L x * R x)) \<le>
      aim_complex_lp_norm p Q *
      aim_complex_lp_norm (2 * slp_holder_conjugate p) L *
      aim_complex_lp_norm (2 * slp_holder_conjugate p) R"
proof -
  let ?r = "slp_holder_conjugate p"
  let ?s = "2 * ?r"
  have r_lower: "1 < ?r"
    by (rule slp_holder_conjugate_lower_and_pair(1)[OF p_lower])
  have r_positive: "0 < ?r" using r_lower by linarith
  have r_nonzero: "?r \<noteq> 0" using r_positive by simp
  have scale_lower: "1 < ?s / ?r" using r_nonzero by simp
  have scale_pair: "1 / (?s / ?r) + 1 / (?s / ?r) = 1"
    using r_nonzero by simp
  have conjugate: "1 / p + 1 / ?r = 1"
    using slp_holder_conjugate_lower_and_pair(2)[OF p_lower]
    by (simp only: add.commute)
  have product_lp: "aim_complex_lp_on_plane ?r (\<lambda>x. L x * R x)"
    by (rule slp_aim_complex_lp_on_plane_product_norm_bound(1)[OF
        r_positive scale_lower scale_lower scale_pair L_lp R_lp])
  have product_bound: "aim_complex_lp_norm ?r (\<lambda>x. L x * R x) \<le>
      aim_complex_lp_norm ?s L * aim_complex_lp_norm ?s R"
    by (rule slp_aim_complex_lp_on_plane_product_norm_bound(2)[OF
        r_positive scale_lower scale_lower scale_pair L_lp R_lp])
  have grouped_integrable: "integrable lborel (\<lambda>x. Q x * (L x * R x))"
    by (rule slp_aim_complex_lp_on_plane_holder_integral_bound(1)[OF
        p_lower r_lower conjugate Q_lp product_lp])
  have grouped_bound: "norm (integral\<^sup>L lborel (\<lambda>x. Q x * (L x * R x)))
      \<le> aim_complex_lp_norm p Q * aim_complex_lp_norm ?r (\<lambda>x. L x * R x)"
    using slp_aim_complex_lp_on_plane_holder_integral_bound(2)[OF
        p_lower r_lower conjugate Q_lp product_lp]
    by (simp only: aim_complex_lp_norm_def)
  have Q_norm_nonnegative: "0 \<le> aim_complex_lp_norm p Q"
    by (simp add: aim_complex_lp_norm_def)
  have norm_product_bound:
      "aim_complex_lp_norm p Q * aim_complex_lp_norm ?r (\<lambda>x. L x * R x) \<le>
        aim_complex_lp_norm p Q *
          (aim_complex_lp_norm ?s L * aim_complex_lp_norm ?s R)"
    by (rule mult_left_mono[OF product_bound Q_norm_nonnegative])
  show "integrable lborel (\<lambda>x. Q x * L x * R x)"
    using grouped_integrable by (simp only: mult.assoc)
  show "norm (integral\<^sup>L lborel (\<lambda>x. Q x * L x * R x)) \<le>
      aim_complex_lp_norm p Q * aim_complex_lp_norm ?s L * aim_complex_lp_norm ?s R"
    using order_trans[OF grouped_bound norm_product_bound]
    by (simp only: mult.assoc)
qed

lemma slp_mixed_root_integral_restricted_holder:
  fixes p tau :: real and center :: slp_point and Q L R :: slp_scalar_field
    and Y :: "slp_point set"
  assumes p_lower: "1 < p"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> x \<in> Y"
    and L_lp: "aim_complex_lp_on_plane (2 * slp_holder_conjugate p) (slp_restrict_field Y L)"
    and R_lp: "aim_complex_lp_on_plane (2 * slp_holder_conjugate p) (slp_restrict_field Y R)"
  shows "integrable lborel (\<lambda>x. Q x * slp_center_kernel (-tau) center x * L x * R x)"
    "norm (integral\<^sup>L lborel (\<lambda>x. Q x * slp_center_kernel (-tau) center x * L x * R x))
      \<le> aim_complex_lp_norm p Q *
        aim_complex_lp_norm (2 * slp_holder_conjugate p) (slp_restrict_field Y L) *
        aim_complex_lp_norm (2 * slp_holder_conjugate p) (slp_restrict_field Y R)"
proof -
  let ?Q = "slp_oscillatory_modulation (-tau) center Q"
  let ?L = "slp_restrict_field Y L"
  let ?R = "slp_restrict_field Y R"
  have modulated_lp: "aim_complex_lp_on_plane p ?Q" using Q_lp by simp
  have identity:
      "(\<lambda>x. Q x * slp_center_kernel (-tau) center x * L x * R x) =
        (\<lambda>x. ?Q x * ?L x * ?R x)"
  proof (rule ext)
    fix x
    show "Q x * slp_center_kernel (-tau) center x * L x * R x =
        ?Q x * ?L x * ?R x"
    proof (cases "x \<in> Y")
      case True
      show ?thesis
        by (simp add: slp_restrict_field_def slp_oscillatory_modulation_def
            True mult.commute mult.left_commute mult.assoc)
    next
      case False
      have zero: "Q x = 0" using Q_support False by blast
      show ?thesis by (simp add: zero slp_oscillatory_modulation_def)
    qed
  qed
  show "integrable lborel (\<lambda>x. Q x * slp_center_kernel (-tau) center x * L x * R x)"
    unfolding identity
    by (rule slp_complex_triple_holder_integral_bound(1)[OF p_lower modulated_lp L_lp R_lp])
  show "norm (integral\<^sup>L lborel (\<lambda>x. Q x * slp_center_kernel (-tau) center x * L x * R x))
      \<le> aim_complex_lp_norm p Q *
        aim_complex_lp_norm (2 * slp_holder_conjugate p) ?L *
        aim_complex_lp_norm (2 * slp_holder_conjugate p) ?R"
    using slp_complex_triple_holder_integral_bound(2)[OF p_lower modulated_lp L_lp R_lp]
    by (simp only: identity slp_oscillatory_modulation_lp_norm)
qed

section \<open>Uniform normalized root bound for every pair of natural orders\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_mixed_recursive_root_uniform_bound:
  fixes p :: real and cutoff :: slp_scalar_field and Y :: "slp_point set"
    and j k :: nat
  assumes p_lower: "1 < p" and p_upper: "p < 2"
    and target_bounded: "bounded Y" and target_measurable: "Y \<in> sets lborel"
    and cutoff_test: "slp_test_function_on Y cutoff"
  shows "\<exists>C::real. 0 < C \<and> (\<forall>tau center q qt Q.
    2 \<le> tau \<and> aim_complex_lp_on_plane p q \<and>
      aim_complex_lp_on_plane p qt \<and> aim_complex_lp_on_plane p Q \<and>
      (\<forall>x. cutoff x * q x = q x) \<and>
      (\<forall>x. cutoff x * qt x = qt x) \<and> (\<forall>x. Q x \<noteq> 0 \<longrightarrow> x \<in> Y) \<longrightarrow>
    integrable lborel (\<lambda>x. Q x * slp_center_kernel (-tau) center x *
      slp_left_recursive_branch j tau center cutoff q (\<lambda>_. 1) x *
      slp_right_recursive_branch k tau center cutoff qt (\<lambda>_. 1) x) \<and>
    norm (of_real (tau / pi) * integral\<^sup>L lborel (\<lambda>x. Q x * slp_center_kernel (-tau) center x *
      slp_left_recursive_branch j tau center cutoff q (\<lambda>_. 1) x *
      slp_right_recursive_branch k tau center cutoff qt (\<lambda>_. 1) x))
      \<le> C * aim_complex_lp_norm p Q *
        (aim_complex_lp_norm p q)^j * (aim_complex_lp_norm p qt)^k)"
proof -
  let ?s = "2 * slp_holder_conjugate p"
  have dual_lower: "1 < slp_holder_conjugate p"
    by (rule slp_holder_conjugate_lower_and_pair(1)[OF p_lower])
  have s_lower: "2 < ?s" using dual_lower by linarith
  obtain A::real where A_positive: "0 < A"
    and A_gain: "\<And>tau c q. 2 \<le> tau \<Longrightarrow>
      aim_complex_lp_on_plane p q \<Longrightarrow> (\<forall>x. cutoff x * q x = q x) \<Longrightarrow>
      aim_complex_lp_on_plane ?s
        (slp_restrict_field Y (slp_left_recursive_branch j tau c cutoff q (\<lambda>_. 1))) \<and>
      aim_complex_lp_on_plane ?s
        (slp_restrict_field Y (slp_right_recursive_branch j tau c cutoff q (\<lambda>_. 1))) \<and>
      aim_complex_lp_norm ?s
        (slp_restrict_field Y (slp_left_recursive_branch j tau c cutoff q (\<lambda>_. 1)))
        \<le> A * inverse (sqrt tau) * (aim_complex_lp_norm p q)^j \<and>
      aim_complex_lp_norm ?s
        (slp_restrict_field Y (slp_right_recursive_branch j tau c cutoff q (\<lambda>_. 1)))
        \<le> A * inverse (sqrt tau) * (aim_complex_lp_norm p q)^j"
    using slp_all_order_born_branches_restricted_gain[OF p_lower p_upper
      s_lower target_bounded target_measurable cutoff_test, where m=j] by blast
  obtain B::real where B_positive: "0 < B"
    and B_gain: "\<And>tau c q. 2 \<le> tau \<Longrightarrow>
      aim_complex_lp_on_plane p q \<Longrightarrow> (\<forall>x. cutoff x * q x = q x) \<Longrightarrow>
      aim_complex_lp_on_plane ?s
        (slp_restrict_field Y (slp_left_recursive_branch k tau c cutoff q (\<lambda>_. 1))) \<and>
      aim_complex_lp_on_plane ?s
        (slp_restrict_field Y (slp_right_recursive_branch k tau c cutoff q (\<lambda>_. 1))) \<and>
      aim_complex_lp_norm ?s
        (slp_restrict_field Y (slp_left_recursive_branch k tau c cutoff q (\<lambda>_. 1)))
        \<le> B * inverse (sqrt tau) * (aim_complex_lp_norm p q)^k \<and>
      aim_complex_lp_norm ?s
        (slp_restrict_field Y (slp_right_recursive_branch k tau c cutoff q (\<lambda>_. 1)))
        \<le> B * inverse (sqrt tau) * (aim_complex_lp_norm p q)^k"
    using slp_all_order_born_branches_restricted_gain[OF p_lower p_upper
      s_lower target_bounded target_measurable cutoff_test, where m=k] by blast
  let ?C = "A * B / pi"
  have C_positive: "0 < ?C"
    using A_positive B_positive by (intro divide_pos_pos mult_pos_pos) simp_all
  have all: "\<forall>tau center q qt Q.
    2 \<le> tau \<and> aim_complex_lp_on_plane p q \<and>
      aim_complex_lp_on_plane p qt \<and> aim_complex_lp_on_plane p Q \<and>
      (\<forall>x. cutoff x * q x = q x) \<and>
      (\<forall>x. cutoff x * qt x = qt x) \<and> (\<forall>x. Q x \<noteq> 0 \<longrightarrow> x \<in> Y) \<longrightarrow>
    integrable lborel (\<lambda>x. Q x * slp_center_kernel (-tau) center x *
      slp_left_recursive_branch j tau center cutoff q (\<lambda>_. 1) x *
      slp_right_recursive_branch k tau center cutoff qt (\<lambda>_. 1) x) \<and>
    norm (of_real (tau / pi) * integral\<^sup>L lborel (\<lambda>x. Q x * slp_center_kernel (-tau) center x *
      slp_left_recursive_branch j tau center cutoff q (\<lambda>_. 1) x *
      slp_right_recursive_branch k tau center cutoff qt (\<lambda>_. 1) x))
      \<le> ?C * aim_complex_lp_norm p Q *
        (aim_complex_lp_norm p q)^j * (aim_complex_lp_norm p qt)^k"
  proof (intro allI impI)
    fix tau :: real and center :: slp_point and q qt Q :: slp_scalar_field
    assume hypotheses: "2 \<le> tau \<and> aim_complex_lp_on_plane p q \<and>
      aim_complex_lp_on_plane p qt \<and> aim_complex_lp_on_plane p Q \<and>
      (\<forall>x. cutoff x * q x = q x) \<and>
      (\<forall>x. cutoff x * qt x = qt x) \<and> (\<forall>x. Q x \<noteq> 0 \<longrightarrow> x \<in> Y)"
    have tau_lower: "2 \<le> tau" and q_lp: "aim_complex_lp_on_plane p q"
      and qt_lp: "aim_complex_lp_on_plane p qt" and Q_lp: "aim_complex_lp_on_plane p Q"
      and cutoff_q: "\<forall>x. cutoff x * q x = q x"
      and cutoff_qt: "\<forall>x. cutoff x * qt x = qt x"
      and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> x \<in> Y"
      using hypotheses by blast+
    let ?L = "slp_left_recursive_branch j tau center cutoff q (\<lambda>_. 1)"
    let ?R = "slp_right_recursive_branch k tau center cutoff qt (\<lambda>_. 1)"
    let ?LR = "slp_restrict_field Y ?L"
    let ?RR = "slp_restrict_field Y ?R"
    let ?H = "(\<lambda>x. Q x * slp_center_kernel (-tau) center x * ?L x * ?R x)"
    let ?U = "A * inverse (sqrt tau) * (aim_complex_lp_norm p q)^j"
    let ?V = "B * inverse (sqrt tau) * (aim_complex_lp_norm p qt)^k"
    have left_data: "aim_complex_lp_on_plane ?s ?LR \<and>
        aim_complex_lp_norm ?s ?LR \<le> ?U"
      using A_gain[OF tau_lower q_lp cutoff_q, of center] by blast
    have right_data: "aim_complex_lp_on_plane ?s ?RR \<and>
        aim_complex_lp_norm ?s ?RR \<le> ?V"
      using B_gain[OF tau_lower qt_lp cutoff_qt, of center] by blast
    have left_lp: "aim_complex_lp_on_plane ?s ?LR" by (rule conjunct1[OF left_data])
    have right_lp: "aim_complex_lp_on_plane ?s ?RR" by (rule conjunct1[OF right_data])
    have integral_exists: "integrable lborel ?H"
      by (rule slp_mixed_root_integral_restricted_holder(1)[OF
          p_lower Q_lp Q_support left_lp right_lp])
    have holder_bound: "norm (integral\<^sup>L lborel ?H) \<le>
        aim_complex_lp_norm p Q * aim_complex_lp_norm ?s ?LR * aim_complex_lp_norm ?s ?RR"
      by (rule slp_mixed_root_integral_restricted_holder(2)[OF
          p_lower Q_lp Q_support left_lp right_lp])
    have tau_positive: "0 < tau" using tau_lower by linarith
    have tau_nonnegative: "0 \<le> tau" using tau_positive by simp
    have tau_nonzero: "tau \<noteq> 0" using tau_positive by simp
    have U_nonnegative: "0 \<le> ?U"
      using A_positive tau_nonnegative
      by (intro mult_nonneg_nonneg zero_le_power) (auto simp: aim_complex_lp_norm_def)
    have right_norm_nonnegative: "0 \<le> aim_complex_lp_norm ?s ?RR"
      by (simp add: aim_complex_lp_norm_def)
    have Q_norm_nonnegative: "0 \<le> aim_complex_lp_norm p Q"
      by (simp add: aim_complex_lp_norm_def)
    have product_bound: "aim_complex_lp_norm ?s ?LR * aim_complex_lp_norm ?s ?RR
        \<le> ?U * ?V"
      by (rule mult_mono[OF conjunct2[OF left_data] conjunct2[OF right_data]
          U_nonnegative right_norm_nonnegative])
    have product_with_Q: "aim_complex_lp_norm p Q *
        (aim_complex_lp_norm ?s ?LR * aim_complex_lp_norm ?s ?RR)
        \<le> aim_complex_lp_norm p Q * (?U * ?V)"
      by (rule mult_left_mono[OF product_bound Q_norm_nonnegative])
    have grouped_holder: "norm (integral\<^sup>L lborel ?H) \<le>
        aim_complex_lp_norm p Q *
          (aim_complex_lp_norm ?s ?LR * aim_complex_lp_norm ?s ?RR)"
      using holder_bound by (simp only: mult.assoc)
    have integral_bound: "norm (integral\<^sup>L lborel ?H)
        \<le> aim_complex_lp_norm p Q * (?U * ?V)"
      by (rule order_trans[OF grouped_holder product_with_Q])
    have prefactor_nonnegative: "0 \<le> tau / pi" using tau_nonnegative by simp
    have scaled_bound: "(tau / pi) * norm (integral\<^sup>L lborel ?H)
        \<le> (tau / pi) * (aim_complex_lp_norm p Q * (?U * ?V))"
      by (rule mult_left_mono[OF integral_bound prefactor_nonnegative])
    have inverse_pair: "inverse (sqrt tau) * inverse (sqrt tau) = inverse tau"
      by (simp only: inverse_mult_distrib[symmetric] real_sqrt_mult_self
          abs_of_nonneg[OF tau_nonnegative])
    have cancellation: "tau * (inverse (sqrt tau) * inverse (sqrt tau)) = 1"
      by (simp only: inverse_pair, simp add: tau_nonzero)
    have rearrangement:
        "(tau / pi) * (aim_complex_lp_norm p Q * (?U * ?V)) =
          (?C * aim_complex_lp_norm p Q *
            (aim_complex_lp_norm p q)^j * (aim_complex_lp_norm p qt)^k) *
          (tau * (inverse (sqrt tau) * inverse (sqrt tau)))"
      by (simp add: divide_inverse algebra_simps)
    have scale_identity:
        "(tau / pi) * (aim_complex_lp_norm p Q * (?U * ?V)) =
          ?C * aim_complex_lp_norm p Q *
            (aim_complex_lp_norm p q)^j * (aim_complex_lp_norm p qt)^k"
      by (simp only: rearrangement cancellation mult.right_neutral)
    have normalized_bound: "norm (of_real (tau / pi) * integral\<^sup>L lborel ?H)
        \<le> ?C * aim_complex_lp_norm p Q *
          (aim_complex_lp_norm p q)^j * (aim_complex_lp_norm p qt)^k"
      using scaled_bound
      by (simp only: norm_mult norm_of_real abs_of_nonneg[OF prefactor_nonnegative]
          scale_identity)
    show "integrable lborel (\<lambda>x. Q x * slp_center_kernel (-tau) center x *
      slp_left_recursive_branch j tau center cutoff q (\<lambda>_. 1) x *
      slp_right_recursive_branch k tau center cutoff qt (\<lambda>_. 1) x) \<and>
    norm (of_real (tau / pi) * integral\<^sup>L lborel (\<lambda>x. Q x * slp_center_kernel (-tau) center x *
      slp_left_recursive_branch j tau center cutoff q (\<lambda>_. 1) x *
      slp_right_recursive_branch k tau center cutoff qt (\<lambda>_. 1) x))
      \<le> ?C * aim_complex_lp_norm p Q *
        (aim_complex_lp_norm p q)^j * (aim_complex_lp_norm p qt)^k"
      by (rule conjI[OF integral_exists normalized_bound])
  qed
  show ?thesis by (rule exI[of _ ?C], rule conjI[OF C_positive all])
qed

end

end
