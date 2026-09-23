theory Inverse_Schrodinger_Lp_Finite_Center_Transpose_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Mixed_Root_Uniform_Bound"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Mixed_Finite_Transpose_Identity"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Oscillatory_Kernel"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Bounded-support Lp data are globally integrable\<close>

lemma slp_bounded_supported_lp_integrable:
  fixes p :: real and Y :: "slp_point set" and Q :: slp_scalar_field
  assumes exponent_lower: "1 \<le> p"
    and set_measurable: "Y \<in> sets lborel"
    and set_bounded: "bounded Y"
    and field_lp: "aim_complex_lp_on_plane p Q"
    and field_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> x \<in> Y"
  shows "integrable lborel Q"
proof -
  have local_integrable: "set_integrable lborel Y Q"
    by (rule aim_complex_lp_on_plane_set_integrable_bounded[OF
        exponent_lower set_measurable set_bounded field_lp])
  have restriction_identity: "(\<lambda>x. indicator Y x *\<^sub>R Q x) = Q"
  proof (rule ext)
    fix x
    show "indicator Y x *\<^sub>R Q x = Q x"
    proof (cases "x \<in> Y")
      case True
      show ?thesis by (simp add: True indicator_def)
    next
      case False
      have zero: "Q x = 0" using field_support False by blast
      show ?thesis by (simp add: zero)
    qed
  qed
  show ?thesis using local_integrable
    unfolding set_integrable_def restriction_identity .
qed

section \<open>The exact finite center transpose under the fixed-cutoff hypotheses\<close>

context aim_planar_riesz_hls
begin

theorem slp_test_cutoff_finite_center_transpose:
  fixes p tau :: real and center :: slp_point and Y :: "slp_point set"
    and cutoff q qt Q :: slp_scalar_field
  assumes p_lower: "1 < p" and p_upper: "p < 2"
    and target_bounded: "bounded Y" and target_measurable: "Y \<in> sets lborel"
    and cutoff_test: "slp_test_function_on Y cutoff"
    and q_lp: "aim_complex_lp_on_plane p q"
    and qt_lp: "aim_complex_lp_on_plane p qt"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and cutoff_q: "\<forall>x. cutoff x * q x = q x"
    and cutoff_qt: "\<forall>x. cutoff x * qt x = qt x"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> x \<in> Y"
  shows "slp_center_average tau
      (slp_mixed_center_finite_oscillatory_kernel TYPE('i::finite) TYPE('j::finite)
        tau Q cutoff q cutoff qt) center =
    of_real (tau / pi) * integral\<^sup>L lborel (\<lambda>x. Q x * slp_center_kernel (-tau) center x *
        slp_left_recursive_branch CARD('i) tau center cutoff q (\<lambda>_. 1) x *
        slp_right_recursive_branch CARD('j) tau center cutoff qt (\<lambda>_. 1) x)"
proof -
  obtain B::real where B_positive: "0 < B"
    and Y_bound: "\<And>x. x \<in> Y \<Longrightarrow> norm x \<le> B"
    by (rule bounded_normE[OF target_bounded]) blast
  have B_nonnegative: "0 \<le> B" using B_positive by simp
  have cutoff_plane: "slp_test_function_on UNIV cutoff"
    using cutoff_test unfolding slp_test_function_on_def by auto
  have cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    by (rule borel_measurable_integrable,
        rule slp_test_function_integrable_bounded(1)[OF cutoff_plane])
  have cutoff_range_bounded: "bounded (range cutoff)"
    by (rule slp_test_function_integrable_bounded(2)[OF cutoff_plane])
  obtain M::real where M_positive: "0 < M"
    and M_bound: "\<And>x. norm (cutoff x) \<le> M"
    using cutoff_range_bounded unfolding bounded_pos by blast
  have M_nonnegative: "0 \<le> M" using M_positive by simp
  have cutoff_in: "x \<in> Y" if "cutoff x \<noteq> 0" for x
    using cutoff_test closure_subset[of "{x. cutoff x \<noteq> 0}"] that
    unfolding slp_test_function_on_def by blast
  have cutoff_support: "norm x \<le> B" if "cutoff x \<noteq> 0" for x
    by (rule Y_bound[OF cutoff_in[OF that]])
  have potential_support: "norm x \<le> B"
    if nonzero: "f x \<noteq> 0" and identity: "\<forall>x. cutoff x * f x = f x"
    for f :: slp_scalar_field and x :: slp_point
  proof -
    have cutoff_nonzero: "cutoff x \<noteq> 0"
      using nonzero identity[rule_format, of x] by auto
    show ?thesis by (rule cutoff_support[OF cutoff_nonzero])
  qed
  have q_support: "norm x \<le> B" if "q x \<noteq> 0" for x
    by (rule potential_support[OF that cutoff_q])
  have qt_support: "norm x \<le> B" if "qt x \<noteq> 0" for x
    by (rule potential_support[OF that cutoff_qt])
  have root_support: "norm x \<le> B" if "Q x \<noteq> 0" for x
    by (rule Y_bound[OF Q_support[OF that]])
  have p_at_least_one: "1 \<le> p" using p_lower by simp
  have Q_integrable: "integrable lborel Q"
    by (rule slp_bounded_supported_lp_integrable[OF p_at_least_one
        target_measurable target_bounded Q_lp Q_support])
  have fiber_identity: "slp_center_average tau
      (slp_mixed_center_finite_fiber_integral TYPE('i) TYPE('j)
        tau Q cutoff q cutoff qt) center =
    of_real (tau / pi) * integral\<^sup>L lborel (\<lambda>x. Q x * slp_center_kernel (-tau) center x *
        slp_left_recursive_branch CARD('i) tau center cutoff q (\<lambda>_. 1) x *
        slp_right_recursive_branch CARD('j) tau center cutoff qt (\<lambda>_. 1) x)"
    by (rule slp_mixed_finite_center_average_transpose[OF B_nonnegative p_lower p_upper
        cutoff_measurable q_lp qt_lp M_bound M_nonnegative Q_integrable
        root_support cutoff_support q_support qt_support])
  have kernel_identity:
      "slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j) tau Q cutoff q cutoff qt =
        slp_mixed_center_finite_fiber_integral TYPE('i) TYPE('j) tau Q cutoff q cutoff qt"
    by (rule ext) (simp only: slp_mixed_center_finite_oscillatory_kernel_def)
  show ?thesis unfolding kernel_identity by (rule fiber_identity)
qed

end

section \<open>Uniform transpose bound for the literal finite center kernel\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_finite_center_transpose_uniform_bound:
  fixes p :: real and cutoff :: slp_scalar_field and Y :: "slp_point set"
  assumes p_lower: "1 < p" and p_upper: "p < 2"
    and target_bounded: "bounded Y" and target_measurable: "Y \<in> sets lborel"
    and cutoff_test: "slp_test_function_on Y cutoff"
  shows "\<exists>C::real. 0 < C \<and> (\<forall>tau center q qt Q.
    2 \<le> tau \<and> aim_complex_lp_on_plane p q \<and>
      aim_complex_lp_on_plane p qt \<and> aim_complex_lp_on_plane p Q \<and>
      (\<forall>x. cutoff x * q x = q x) \<and>
      (\<forall>x. cutoff x * qt x = qt x) \<and> (\<forall>x. Q x \<noteq> 0 \<longrightarrow> x \<in> Y) \<longrightarrow>
    norm (slp_center_average tau
      (slp_mixed_center_finite_oscillatory_kernel TYPE('i::finite) TYPE('j::finite)
        tau Q cutoff q cutoff qt) center) \<le>
      C * aim_complex_lp_norm p Q *
        (aim_complex_lp_norm p q)^CARD('i) * (aim_complex_lp_norm p qt)^CARD('j))"
proof -
  obtain C::real where C_positive: "0 < C"
    and root_gain: "\<And>tau center q qt Q. 2 \<le> tau \<and> aim_complex_lp_on_plane p q \<and>
      aim_complex_lp_on_plane p qt \<and> aim_complex_lp_on_plane p Q \<and>
      (\<forall>x. cutoff x * q x = q x) \<and>
      (\<forall>x. cutoff x * qt x = qt x) \<and> (\<forall>x. Q x \<noteq> 0 \<longrightarrow> x \<in> Y) \<Longrightarrow>
      integrable lborel (\<lambda>x. Q x * slp_center_kernel (-tau) center x *
        slp_left_recursive_branch CARD('i) tau center cutoff q (\<lambda>_. 1) x *
        slp_right_recursive_branch CARD('j) tau center cutoff qt (\<lambda>_. 1) x) \<and>
      norm (of_real (tau / pi) * integral\<^sup>L lborel (\<lambda>x. Q x * slp_center_kernel (-tau) center x *
        slp_left_recursive_branch CARD('i) tau center cutoff q (\<lambda>_. 1) x *
        slp_right_recursive_branch CARD('j) tau center cutoff qt (\<lambda>_. 1) x)) \<le>
        C * aim_complex_lp_norm p Q *
          (aim_complex_lp_norm p q)^CARD('i) * (aim_complex_lp_norm p qt)^CARD('j)"
    using slp_mixed_recursive_root_uniform_bound[OF p_lower p_upper
      target_bounded target_measurable cutoff_test,
      where j="CARD('i)" and k="CARD('j)"] by blast
  have all: "\<forall>tau center q qt Q.
    2 \<le> tau \<and> aim_complex_lp_on_plane p q \<and>
      aim_complex_lp_on_plane p qt \<and> aim_complex_lp_on_plane p Q \<and>
      (\<forall>x. cutoff x * q x = q x) \<and>
      (\<forall>x. cutoff x * qt x = qt x) \<and> (\<forall>x. Q x \<noteq> 0 \<longrightarrow> x \<in> Y) \<longrightarrow>
    norm (slp_center_average tau
      (slp_mixed_center_finite_oscillatory_kernel TYPE('i::finite) TYPE('j::finite)
        tau Q cutoff q cutoff qt) center) \<le>
      C * aim_complex_lp_norm p Q *
        (aim_complex_lp_norm p q)^CARD('i) * (aim_complex_lp_norm p qt)^CARD('j)"
  proof (intro allI impI)
    fix tau :: real and center :: slp_point and q qt Q :: slp_scalar_field
    assume hypotheses: "2 \<le> tau \<and> aim_complex_lp_on_plane p q \<and>
      aim_complex_lp_on_plane p qt \<and> aim_complex_lp_on_plane p Q \<and>
      (\<forall>x. cutoff x * q x = q x) \<and>
      (\<forall>x. cutoff x * qt x = qt x) \<and> (\<forall>x. Q x \<noteq> 0 \<longrightarrow> x \<in> Y)"
    have q_lp: "aim_complex_lp_on_plane p q" and qt_lp: "aim_complex_lp_on_plane p qt"
      and Q_lp: "aim_complex_lp_on_plane p Q"
      and cutoff_q: "\<forall>x. cutoff x * q x = q x"
      and cutoff_qt: "\<forall>x. cutoff x * qt x = qt x"
      and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> x \<in> Y"
      using hypotheses by blast+
    have identity: "slp_center_average tau
      (slp_mixed_center_finite_oscillatory_kernel TYPE('i::finite) TYPE('j::finite)
        tau Q cutoff q cutoff qt) center = of_real (tau / pi) * integral\<^sup>L lborel (\<lambda>x. Q x * slp_center_kernel (-tau) center x *
        slp_left_recursive_branch CARD('i) tau center cutoff q (\<lambda>_. 1) x *
        slp_right_recursive_branch CARD('j) tau center cutoff qt (\<lambda>_. 1) x)"
      by (rule slp_test_cutoff_finite_center_transpose[OF p_lower p_upper
          target_bounded target_measurable cutoff_test q_lp qt_lp Q_lp
          cutoff_q cutoff_qt Q_support])
    have root_bound: "norm (of_real (tau / pi) * integral\<^sup>L lborel (\<lambda>x. Q x * slp_center_kernel (-tau) center x *
        slp_left_recursive_branch CARD('i) tau center cutoff q (\<lambda>_. 1) x *
        slp_right_recursive_branch CARD('j) tau center cutoff qt (\<lambda>_. 1) x)) \<le>
        C * aim_complex_lp_norm p Q *
          (aim_complex_lp_norm p q)^CARD('i) * (aim_complex_lp_norm p qt)^CARD('j)"
      by (rule conjunct2[OF root_gain[OF hypotheses]])
    show "norm (slp_center_average tau
      (slp_mixed_center_finite_oscillatory_kernel TYPE('i::finite) TYPE('j::finite)
        tau Q cutoff q cutoff qt) center) \<le>
        C * aim_complex_lp_norm p Q *
          (aim_complex_lp_norm p q)^CARD('i) * (aim_complex_lp_norm p qt)^CARD('j)"
      unfolding identity by (rule root_bound)
  qed
  show ?thesis by (rule exI[of _ C], rule conjI[OF C_positive all])
qed

end

end
