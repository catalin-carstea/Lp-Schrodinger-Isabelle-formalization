theory Inverse_Schrodinger_Lp_Reverse_Later_Block_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_Two_Cauchy_Test_Cutoff"
begin

hide_const (open) Commutative_Ring.norm

section \<open>A fixed test cutoff turns a local bound into a global multiplier\<close>

lemma slp_test_cutoff_bounded_multiplier:
  fixes cutoff :: slp_scalar_field and Y :: "slp_point set"
  assumes cutoff_test: "slp_test_function_on Y cutoff"
  shows "\<exists>M::real. 0 < M \<and>
    (\<forall>g B. g \<in> borel_measurable lborel \<and> 0 \<le> B \<and>
      (\<forall>x\<in>Y. norm (g x) \<le> B) \<longrightarrow>
      (\<lambda>x. cutoff x * g x) \<in> borel_measurable lborel \<and>
      (\<forall>x. norm (cutoff x * g x) \<le> M * B))"
proof -
  have cutoff_plane: "slp_test_function_on UNIV cutoff"
    using cutoff_test unfolding slp_test_function_on_def by auto
  have cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    by (rule borel_measurable_integrable,
        rule slp_test_function_integrable_bounded(1)[OF cutoff_plane])
  have cutoff_range_bounded: "bounded (range cutoff)"
    by (rule slp_test_function_integrable_bounded(2)[OF cutoff_plane])
  obtain M :: real where M_positive: "0 < M"
    and M_bound: "\<And>x. norm (cutoff x) \<le> M"
    using cutoff_range_bounded unfolding bounded_pos by blast
  have M_nonnegative: "0 \<le> M" using M_positive by linarith
  have cutoff_support: "{x. cutoff x \<noteq> 0} \<subseteq> Y"
    using cutoff_test closure_subset[of "{x. cutoff x \<noteq> 0}"]
    unfolding slp_test_function_on_def by blast
  have all: "\<forall>g B. g \<in> borel_measurable lborel \<and> 0 \<le> B \<and>
      (\<forall>x\<in>Y. norm (g x) \<le> B) \<longrightarrow>
      (\<lambda>x. cutoff x * g x) \<in> borel_measurable lborel \<and>
      (\<forall>x. norm (cutoff x * g x) \<le> M * B)"
  proof (intro allI impI)
    fix g :: slp_scalar_field and B :: real
    assume hypotheses: "g \<in> borel_measurable lborel \<and> 0 \<le> B \<and>
      (\<forall>x\<in>Y. norm (g x) \<le> B)"
    have g_measurable: "g \<in> borel_measurable lborel" using hypotheses by blast
    have B_nonnegative: "0 \<le> B" using hypotheses by blast
    have g_bound: "\<And>x. x \<in> Y \<Longrightarrow> norm (g x) \<le> B"
      using hypotheses by blast
    have measurable: "(\<lambda>x. cutoff x * g x) \<in> borel_measurable lborel"
      using cutoff_measurable g_measurable by measurable
    have bound: "norm (cutoff x * g x) \<le> M * B" for x
    proof (cases "x \<in> Y")
      case True
      have "norm (cutoff x * g x) = norm (cutoff x) * norm (g x)"
        by (rule norm_mult)
      also have "... \<le> M * norm (g x)"
        by (rule mult_right_mono[OF M_bound]) simp
      also have "... \<le> M * B"
        by (rule mult_left_mono[OF g_bound[OF True] M_nonnegative])
      finally show ?thesis .
    next
      case False
      have cutoff_zero: "cutoff x = 0" using cutoff_support False by auto
      show ?thesis using mult_nonneg_nonneg[OF M_nonnegative B_nonnegative]
        by (simp add: cutoff_zero)
    qed
    show "(\<lambda>x. cutoff x * g x) \<in> borel_measurable lborel \<and>
        (\<forall>x. norm (cutoff x * g x) \<le> M * B)"
      by (rule conjI[OF measurable], intro allI, rule bound)
  qed
  show ?thesis by (rule exI[of _ M], rule conjI[OF M_positive all])
qed

section \<open>Later reversed blocks preserve the local bound\<close>

context aim_planar_hls_cauchy
begin

theorem slp_reverse_later_block_local_bound:
  fixes cutoff1 cutoff2 :: slp_scalar_field and Y :: "slp_point set"
  assumes p_lower: "1 < p" and p_upper: "p < 2"
    and target_bounded: "bounded Y"
    and cutoff1_test: "slp_test_function_on Y cutoff1"
    and cutoff2_test: "slp_test_function_on Y cutoff2"
  shows "\<exists>C::real. 0 < C \<and>
    (\<forall>tau1 tau2 c1 c2 F g B outer inner.
      aim_complex_lp_on_plane p F \<and> g \<in> borel_measurable lborel \<and>
      0 \<le> B \<and> (\<forall>x\<in>Y. norm (g x) \<le> B) \<longrightarrow>
      slp_cauchy_transform outer (slp_oscillatory_modulation tau1 c1
          (\<lambda>y. cutoff1 y * slp_cauchy_transform inner
            (slp_oscillatory_modulation tau2 c2
              (\<lambda>x. cutoff2 x * (F x * g x))) y)) \<in> borel_measurable lborel \<and>
      (\<forall>z\<in>Y. slp_cauchy_integrable_at outer (slp_oscillatory_modulation tau1 c1
          (\<lambda>y. cutoff1 y * slp_cauchy_transform inner
            (slp_oscillatory_modulation tau2 c2
              (\<lambda>x. cutoff2 x * (F x * g x))) y)) z \<and>
        norm (slp_cauchy_transform outer (slp_oscillatory_modulation tau1 c1
          (\<lambda>y. cutoff1 y * slp_cauchy_transform inner
            (slp_oscillatory_modulation tau2 c2
              (\<lambda>x. cutoff2 x * (F x * g x))) y)) z) \<le> C * aim_complex_lp_norm p F * B))"
proof -
  have p_positive: "0 < p" using p_lower by linarith
  obtain M :: real where M_data:
      "0 < M \<and>
        (\<forall>g B. g \<in> borel_measurable lborel \<and> 0 \<le> B \<and>
          (\<forall>x\<in>Y. norm (g x) \<le> B) \<longrightarrow>
          (\<lambda>x. cutoff2 x * g x) \<in> borel_measurable lborel \<and>
          (\<forall>x. norm (cutoff2 x * g x) \<le> M * B))"
    using slp_test_cutoff_bounded_multiplier[OF cutoff2_test] ..
  have M_positive: "0 < M" by (rule conjunct1[OF M_data])
  have M_nonnegative: "0 \<le> M" using M_positive by linarith
  note M_all = M_data[THEN conjunct2]
  obtain H :: real where H_data:
      "0 < H \<and>
        (\<forall>tau1 tau2 c1 c2 h outer inner.
          aim_complex_lp_on_plane p h \<longrightarrow>
          slp_cauchy_transform outer (slp_oscillatory_modulation tau1 c1
              (\<lambda>y. cutoff1 y * slp_cauchy_transform inner
                (slp_oscillatory_modulation tau2 c2 h) y)) \<in> borel_measurable lborel \<and>
          (\<forall>z\<in>Y. slp_cauchy_integrable_at outer (slp_oscillatory_modulation tau1 c1
              (\<lambda>y. cutoff1 y * slp_cauchy_transform inner
                (slp_oscillatory_modulation tau2 c2 h) y)) z \<and>
            norm (slp_cauchy_transform outer (slp_oscillatory_modulation tau1 c1
              (\<lambda>y. cutoff1 y * slp_cauchy_transform inner
                (slp_oscillatory_modulation tau2 c2 h) y)) z) \<le> H * aim_complex_lp_norm p h))"
    using slp_two_oscillatory_cauchy_test_cutoff_bound[
        OF p_lower p_upper target_bounded cutoff1_test] ..
  have H_positive: "0 < H" by (rule conjunct1[OF H_data])
  have H_nonnegative: "0 \<le> H" using H_positive by linarith
  note H_all = H_data[THEN conjunct2]
  have constant_positive: "0 < H * M" by (rule mult_pos_pos[OF H_positive M_positive])
  have all: "(\<forall>tau1 tau2 c1 c2 F g B outer inner.
      aim_complex_lp_on_plane p F \<and> g \<in> borel_measurable lborel \<and>
      0 \<le> B \<and> (\<forall>x\<in>Y. norm (g x) \<le> B) \<longrightarrow>
      slp_cauchy_transform outer (slp_oscillatory_modulation tau1 c1
          (\<lambda>y. cutoff1 y * slp_cauchy_transform inner
            (slp_oscillatory_modulation tau2 c2
              (\<lambda>x. cutoff2 x * (F x * g x))) y)) \<in> borel_measurable lborel \<and>
      (\<forall>z\<in>Y. slp_cauchy_integrable_at outer (slp_oscillatory_modulation tau1 c1
          (\<lambda>y. cutoff1 y * slp_cauchy_transform inner
            (slp_oscillatory_modulation tau2 c2
              (\<lambda>x. cutoff2 x * (F x * g x))) y)) z \<and>
        norm (slp_cauchy_transform outer (slp_oscillatory_modulation tau1 c1
          (\<lambda>y. cutoff1 y * slp_cauchy_transform inner
            (slp_oscillatory_modulation tau2 c2
              (\<lambda>x. cutoff2 x * (F x * g x))) y)) z) \<le> (H * M) * aim_complex_lp_norm p F * B))"
  proof (intro allI impI)
    fix tau1 tau2 B :: real and c1 c2 :: slp_point
      and F g :: slp_scalar_field and outer inner :: slp_cauchy_orientation
    assume hypotheses:
        "aim_complex_lp_on_plane p F \<and> g \<in> borel_measurable lborel \<and>
          0 \<le> B \<and> (\<forall>x\<in>Y. norm (g x) \<le> B)"
    have F_lp: "aim_complex_lp_on_plane p F" using hypotheses by blast
    have B_nonnegative: "0 \<le> B" using hypotheses by blast
    have multiplier_hypotheses:
        "g \<in> borel_measurable lborel \<and> 0 \<le> B \<and>
          (\<forall>x\<in>Y. norm (g x) \<le> B)"
      using hypotheses by blast
    have multiplier_data:
        "(\<lambda>x. cutoff2 x * g x) \<in> borel_measurable lborel \<and>
          (\<forall>x. norm (cutoff2 x * g x) \<le> M * B)"
      by (rule M_all[rule_format, OF multiplier_hypotheses])
    have multiplier_bound: "norm (cutoff2 x * g x) \<le> M * B" for x
      by (rule multiplier_data[THEN conjunct2, rule_format])
    have multiplier_nonnegative: "0 \<le> M * B"
      by (rule mult_nonneg_nonneg[OF M_nonnegative B_nonnegative])
    note input = slp_complex_lp_bounded_multiplier[
      OF p_positive multiplier_data[THEN conjunct1] multiplier_bound
        multiplier_nonnegative F_lp]
    let ?v = "\<lambda>x. cutoff2 x * (F x * g x)"
    let ?w = "(slp_oscillatory_modulation tau1 c1
          (\<lambda>y. cutoff1 y * slp_cauchy_transform inner
            (slp_oscillatory_modulation tau2 c2
              (\<lambda>x. cutoff2 x * (F x * g x))) y))"
    have v_lp: "aim_complex_lp_on_plane p ?v"
      using input(1) by (simp only: mult.assoc mult.commute mult.left_commute)
    have v_bound: "aim_complex_lp_norm p ?v \<le> (M * B) * aim_complex_lp_norm p F"
      using input(2) by (simp only: mult.assoc mult.commute mult.left_commute)
    have application:
        "slp_cauchy_transform outer ?w \<in> borel_measurable lborel \<and>
          (\<forall>z\<in>Y. slp_cauchy_integrable_at outer ?w z \<and>
            norm (slp_cauchy_transform outer ?w z) \<le> H * aim_complex_lp_norm p ?v)"
      by (rule H_all[rule_format, OF v_lp])
    have points: "\<forall>z\<in>Y. slp_cauchy_integrable_at outer ?w z \<and>
        norm (slp_cauchy_transform outer ?w z) \<le> (H * M) * aim_complex_lp_norm p F * B"
    proof (intro ballI)
      fix z assume z_in: "z \<in> Y"
      note at_z = application[THEN conjunct2, rule_format, OF z_in]
      have bound: "norm (slp_cauchy_transform outer ?w z) \<le>
          (H * M) * aim_complex_lp_norm p F * B"
      proof -
        have "norm (slp_cauchy_transform outer ?w z) \<le> H * aim_complex_lp_norm p ?v"
          by (rule conjunct2[OF at_z])
        also have "... \<le> H * ((M * B) * aim_complex_lp_norm p F)"
          by (rule mult_left_mono[OF v_bound H_nonnegative])
        also have "... = (H * M) * aim_complex_lp_norm p F * B"
          by (simp only: mult.assoc mult.commute mult.left_commute)
        finally show ?thesis .
      qed
      show "slp_cauchy_integrable_at outer ?w z \<and>
          norm (slp_cauchy_transform outer ?w z) \<le>
            (H * M) * aim_complex_lp_norm p F * B"
        by (rule conjI[OF at_z[THEN conjunct1] bound])
    qed
    show "slp_cauchy_transform outer ?w \<in> borel_measurable lborel \<and>
        (\<forall>z\<in>Y. slp_cauchy_integrable_at outer ?w z \<and>
          norm (slp_cauchy_transform outer ?w z) \<le>
            (H * M) * aim_complex_lp_norm p F * B)"
      by (rule conjI[OF application[THEN conjunct1] points])
  qed
  show ?thesis by (rule exI[of _ "H * M"], rule conjI[OF constant_positive all])
qed

end

end
