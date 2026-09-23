theory Inverse_Schrodinger_Lp_Reverse_Finite_Blocks
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_Reverse_First_Block_Gain"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_Reverse_Later_Block_Bound"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Uniform positive-order bounds for the literal reverse recursion\<close>

context aim_planar_hls_cauchy
begin

theorem slp_reverse_finite_blocks_from_lb:
  fixes cutoff1 cutoff2 :: "nat \<Rightarrow> slp_scalar_field"
    and Y :: "slp_point set" and n :: nat
  assumes p_lower: "1 < p" and p_upper: "p < 2"
    and b_lower: "2 * slp_holder_conjugate p < b"
    and target_bounded: "bounded Y"
    and cutoff1_tests: "\<forall>i<Suc n. slp_test_function_on Y (cutoff1 i)"
    and cutoff2_tests: "\<forall>i<Suc n. slp_test_function_on Y (cutoff2 i)"
  shows "\<exists>C::real. 0 < C \<and> (\<forall>tau1 tau2 c1 c2 F g outer inner Pi.
      aim_complex_lp_on_plane b g \<and>
      (\<forall>i<(Suc n). aim_complex_lp_on_plane p (F i)) \<and> Pi 0 = g \<and>
      (\<forall>i<(Suc n). Pi (Suc i) = slp_cauchy_transform (outer i)
            (slp_oscillatory_modulation (tau1 i) (c1 i)
              (\<lambda>y. cutoff1 i y * slp_cauchy_transform (inner i)
                (slp_oscillatory_modulation (tau2 i) (c2 i)
                  (\<lambda>x. cutoff2 i x * (F i x * Pi i x))) y))) \<longrightarrow> Pi (Suc n) \<in> borel_measurable lborel \<and>
      (\<forall>z\<in>Y. norm (Pi (Suc n) z) \<le>
        C * aim_complex_lp_norm b g * (\<Prod>i<(Suc n). aim_complex_lp_norm p (F i))))"
  using cutoff1_tests cutoff2_tests
proof (induction n)
  case 0
  have cut1: "slp_test_function_on Y (cutoff1 0)"
    using "0.prems"(1) by simp
  have cut2: "slp_test_function_on Y (cutoff2 0)"
    using "0.prems"(2) by simp
  obtain C :: real where C_data: "0 < C \<and> (\<forall>tau1 tau2 c1 c2 F g outer inner.
      aim_complex_lp_on_plane p F \<and> aim_complex_lp_on_plane b g \<longrightarrow>
      slp_cauchy_transform outer (slp_oscillatory_modulation tau1 c1
          (\<lambda>y. cutoff1 0 y * slp_cauchy_transform inner
            (slp_oscillatory_modulation tau2 c2
              (\<lambda>x. cutoff2 0 x * (F x * g x))) y)) \<in> borel_measurable lborel \<and>
      (\<forall>z\<in>Y. slp_cauchy_integrable_at outer (slp_oscillatory_modulation tau1 c1
          (\<lambda>y. cutoff1 0 y * slp_cauchy_transform inner
            (slp_oscillatory_modulation tau2 c2
              (\<lambda>x. cutoff2 0 x * (F x * g x))) y)) z \<and>
        norm (slp_cauchy_transform outer (slp_oscillatory_modulation tau1 c1
          (\<lambda>y. cutoff1 0 y * slp_cauchy_transform inner
            (slp_oscillatory_modulation tau2 c2
              (\<lambda>x. cutoff2 0 x * (F x * g x))) y)) z) \<le>
          C * aim_complex_lp_norm p F * aim_complex_lp_norm b g))"
    using slp_two_cauchy_test_cutoff_product_bound[OF p_lower p_upper
        b_lower target_bounded cut1 cut2] ..
  have C_positive: "0 < C" by (rule conjunct1[OF C_data])
  note C_all = C_data[THEN conjunct2]
  have all: "(\<forall>tau1 tau2 c1 c2 F g outer inner Pi.
      aim_complex_lp_on_plane b g \<and>
      (\<forall>i<(Suc 0). aim_complex_lp_on_plane p (F i)) \<and> Pi 0 = g \<and>
      (\<forall>i<(Suc 0). Pi (Suc i) = slp_cauchy_transform (outer i)
            (slp_oscillatory_modulation (tau1 i) (c1 i)
              (\<lambda>y. cutoff1 i y * slp_cauchy_transform (inner i)
                (slp_oscillatory_modulation (tau2 i) (c2 i)
                  (\<lambda>x. cutoff2 i x * (F i x * Pi i x))) y))) \<longrightarrow> Pi (Suc 0) \<in> borel_measurable lborel \<and>
      (\<forall>z\<in>Y. norm (Pi (Suc 0) z) \<le>
        C * aim_complex_lp_norm b g * (\<Prod>i<(Suc 0). aim_complex_lp_norm p (F i))))"
  proof (intro allI impI)
    fix tau1 tau2 :: "nat \<Rightarrow> real"
      and c1 c2 :: "nat \<Rightarrow> slp_point"
      and F Pi :: "nat \<Rightarrow> slp_scalar_field"
      and g :: slp_scalar_field
      and outer inner :: "nat \<Rightarrow> slp_cauchy_orientation"
    assume hypotheses: "aim_complex_lp_on_plane b g \<and>
      (\<forall>i<(Suc 0). aim_complex_lp_on_plane p (F i)) \<and> Pi 0 = g \<and>
      (\<forall>i<(Suc 0). Pi (Suc i) = slp_cauchy_transform (outer i)
            (slp_oscillatory_modulation (tau1 i) (c1 i)
              (\<lambda>y. cutoff1 i y * slp_cauchy_transform (inner i)
                (slp_oscillatory_modulation (tau2 i) (c2 i)
                  (\<lambda>x. cutoff2 i x * (F i x * Pi i x))) y)))"
    have g_lp: "aim_complex_lp_on_plane b g" by (rule conjunct1[OF hypotheses])
    note F_all = hypotheses[THEN conjunct2, THEN conjunct1]
    note Pi_zero = hypotheses[THEN conjunct2, THEN conjunct2, THEN conjunct1]
    note recurrence = hypotheses[THEN conjunct2, THEN conjunct2, THEN conjunct2]
    have F_zero: "aim_complex_lp_on_plane p (F 0)" using F_all by simp
    let ?w = "slp_oscillatory_modulation (tau1 0) (c1 0)
      (\<lambda>y. cutoff1 0 y * slp_cauchy_transform (inner 0)
        (slp_oscillatory_modulation (tau2 0) (c2 0)
          (\<lambda>x. cutoff2 0 x * (F 0 x * g x))) y)"
    have Pi_one: "Pi (Suc 0) = slp_cauchy_transform (outer 0) ?w"
      using recurrence by (simp add: Pi_zero)
    have inputs: "aim_complex_lp_on_plane p (F 0) \<and> aim_complex_lp_on_plane b g"
      by (rule conjI[OF F_zero g_lp])
    have application:
        "slp_cauchy_transform (outer 0) ?w \<in> borel_measurable lborel \<and>
          (\<forall>z\<in>Y. slp_cauchy_integrable_at (outer 0) ?w z \<and>
            norm (slp_cauchy_transform (outer 0) ?w z) \<le>
              C * aim_complex_lp_norm p (F 0) * aim_complex_lp_norm b g)"
      by (rule C_all[rule_format, OF inputs])
    have measurable: "Pi (Suc 0) \<in> borel_measurable lborel"
      using application[THEN conjunct1] by (simp only: Pi_one)
    have points: "\<forall>z\<in>Y. norm (Pi (Suc 0) z) \<le>
        C * aim_complex_lp_norm b g * (\<Prod>i<Suc 0. aim_complex_lp_norm p (F i))"
    proof (intro ballI)
      fix z assume z_in: "z \<in> Y"
      note point = application[THEN conjunct2, rule_format, OF z_in]
      show "norm (Pi (Suc 0) z) \<le>
          C * aim_complex_lp_norm b g * (\<Prod>i<Suc 0. aim_complex_lp_norm p (F i))"
        using point[THEN conjunct2] by (simp add: Pi_one ac_simps)
    qed
    show "Pi (Suc 0) \<in> borel_measurable lborel \<and>
      (\<forall>z\<in>Y. norm (Pi (Suc 0) z) \<le>
        C * aim_complex_lp_norm b g * (\<Prod>i<(Suc 0). aim_complex_lp_norm p (F i)))" by (rule conjI[OF measurable points])
  qed
  show ?case by (rule exI[of _ C], rule conjI[OF C_positive all])
next
  case (Suc n)
  have cut1_old: "\<forall>i<Suc n. slp_test_function_on Y (cutoff1 i)"
    using Suc.prems(1) by auto
  have cut2_old: "\<forall>i<Suc n. slp_test_function_on Y (cutoff2 i)"
    using Suc.prems(2) by auto
  have cut1_new: "slp_test_function_on Y (cutoff1 (Suc n))"
    using Suc.prems(1) by simp
  have cut2_new: "slp_test_function_on Y (cutoff2 (Suc n))"
    using Suc.prems(2) by simp
  obtain C :: real where C_data: "0 < C \<and> (\<forall>tau1 tau2 c1 c2 F g outer inner Pi.
      aim_complex_lp_on_plane b g \<and>
      (\<forall>i<(Suc n). aim_complex_lp_on_plane p (F i)) \<and> Pi 0 = g \<and>
      (\<forall>i<(Suc n). Pi (Suc i) = slp_cauchy_transform (outer i)
            (slp_oscillatory_modulation (tau1 i) (c1 i)
              (\<lambda>y. cutoff1 i y * slp_cauchy_transform (inner i)
                (slp_oscillatory_modulation (tau2 i) (c2 i)
                  (\<lambda>x. cutoff2 i x * (F i x * Pi i x))) y))) \<longrightarrow> Pi (Suc n) \<in> borel_measurable lborel \<and>
      (\<forall>z\<in>Y. norm (Pi (Suc n) z) \<le>
        C * aim_complex_lp_norm b g * (\<Prod>i<(Suc n). aim_complex_lp_norm p (F i))))"
    using Suc.IH[OF cut1_old cut2_old] ..
  have C_positive: "0 < C" by (rule conjunct1[OF C_data])
  have C_nonnegative: "0 \<le> C" using C_positive by linarith
  note C_all = C_data[THEN conjunct2]
  obtain D :: real where D_data: "0 < D \<and> (\<forall>tau1 tau2 c1 c2 F g B outer inner.
      aim_complex_lp_on_plane p F \<and> g \<in> borel_measurable lborel \<and>
      0 \<le> B \<and> (\<forall>x\<in>Y. norm (g x) \<le> B) \<longrightarrow>
      slp_cauchy_transform outer (slp_oscillatory_modulation tau1 c1
          (\<lambda>y. cutoff1 (Suc n) y * slp_cauchy_transform inner
            (slp_oscillatory_modulation tau2 c2
              (\<lambda>x. cutoff2 (Suc n) x * (F x * g x))) y)) \<in> borel_measurable lborel \<and>
      (\<forall>z\<in>Y. slp_cauchy_integrable_at outer (slp_oscillatory_modulation tau1 c1
          (\<lambda>y. cutoff1 (Suc n) y * slp_cauchy_transform inner
            (slp_oscillatory_modulation tau2 c2
              (\<lambda>x. cutoff2 (Suc n) x * (F x * g x))) y)) z \<and>
        norm (slp_cauchy_transform outer (slp_oscillatory_modulation tau1 c1
          (\<lambda>y. cutoff1 (Suc n) y * slp_cauchy_transform inner
            (slp_oscillatory_modulation tau2 c2
              (\<lambda>x. cutoff2 (Suc n) x * (F x * g x))) y)) z) \<le> D * aim_complex_lp_norm p F * B))"
    using slp_reverse_later_block_local_bound[OF p_lower p_upper
        target_bounded cut1_new cut2_new] ..
  have D_positive: "0 < D" by (rule conjunct1[OF D_data])
  note D_all = D_data[THEN conjunct2]
  have constant_positive: "0 < D * C" by (rule mult_pos_pos[OF D_positive C_positive])
  have all: "(\<forall>tau1 tau2 c1 c2 F g outer inner Pi.
      aim_complex_lp_on_plane b g \<and>
      (\<forall>i<(Suc (Suc n)). aim_complex_lp_on_plane p (F i)) \<and> Pi 0 = g \<and>
      (\<forall>i<(Suc (Suc n)). Pi (Suc i) = slp_cauchy_transform (outer i)
            (slp_oscillatory_modulation (tau1 i) (c1 i)
              (\<lambda>y. cutoff1 i y * slp_cauchy_transform (inner i)
                (slp_oscillatory_modulation (tau2 i) (c2 i)
                  (\<lambda>x. cutoff2 i x * (F i x * Pi i x))) y))) \<longrightarrow> Pi (Suc (Suc n)) \<in> borel_measurable lborel \<and>
      (\<forall>z\<in>Y. norm (Pi (Suc (Suc n)) z) \<le>
        (D * C) * aim_complex_lp_norm b g * (\<Prod>i<(Suc (Suc n)). aim_complex_lp_norm p (F i))))"
  proof (intro allI impI)
    fix tau1 tau2 :: "nat \<Rightarrow> real"
      and c1 c2 :: "nat \<Rightarrow> slp_point"
      and F Pi :: "nat \<Rightarrow> slp_scalar_field"
      and g :: slp_scalar_field
      and outer inner :: "nat \<Rightarrow> slp_cauchy_orientation"
    assume hypotheses: "aim_complex_lp_on_plane b g \<and>
      (\<forall>i<(Suc (Suc n)). aim_complex_lp_on_plane p (F i)) \<and> Pi 0 = g \<and>
      (\<forall>i<(Suc (Suc n)). Pi (Suc i) = slp_cauchy_transform (outer i)
            (slp_oscillatory_modulation (tau1 i) (c1 i)
              (\<lambda>y. cutoff1 i y * slp_cauchy_transform (inner i)
                (slp_oscillatory_modulation (tau2 i) (c2 i)
                  (\<lambda>x. cutoff2 i x * (F i x * Pi i x))) y)))"
    have g_lp: "aim_complex_lp_on_plane b g" by (rule conjunct1[OF hypotheses])
    note F_all = hypotheses[THEN conjunct2, THEN conjunct1]
    note Pi_zero = hypotheses[THEN conjunct2, THEN conjunct2, THEN conjunct1]
    note recurrence = hypotheses[THEN conjunct2, THEN conjunct2, THEN conjunct2]
    have F_old: "\<forall>i<Suc n. aim_complex_lp_on_plane p (F i)"
      using F_all by auto
    have recurrence_old: "\<forall>i<Suc n. Pi (Suc i) = slp_cauchy_transform (outer i)
            (slp_oscillatory_modulation (tau1 i) (c1 i)
              (\<lambda>y. cutoff1 i y * slp_cauchy_transform (inner i)
                (slp_oscillatory_modulation (tau2 i) (c2 i)
                  (\<lambda>x. cutoff2 i x * (F i x * Pi i x))) y))"
      using recurrence by auto
    have old_hypotheses: "aim_complex_lp_on_plane b g \<and>
      (\<forall>i<(Suc n). aim_complex_lp_on_plane p (F i)) \<and> Pi 0 = g \<and>
      (\<forall>i<(Suc n). Pi (Suc i) = slp_cauchy_transform (outer i)
            (slp_oscillatory_modulation (tau1 i) (c1 i)
              (\<lambda>y. cutoff1 i y * slp_cauchy_transform (inner i)
                (slp_oscillatory_modulation (tau2 i) (c2 i)
                  (\<lambda>x. cutoff2 i x * (F i x * Pi i x))) y)))"
      by (intro conjI g_lp F_old Pi_zero recurrence_old)
    have prior: "Pi (Suc n) \<in> borel_measurable lborel \<and>
      (\<forall>z\<in>Y. norm (Pi (Suc n) z) \<le>
        C * aim_complex_lp_norm b g * (\<Prod>i<(Suc n). aim_complex_lp_norm p (F i)))"
      by (rule C_all[rule_format, OF old_hypotheses])
    let ?B = "C * aim_complex_lp_norm b g * (\<Prod>i<Suc n. aim_complex_lp_norm p (F i))"
    have g_norm_nonnegative: "0 \<le> aim_complex_lp_norm b g"
      unfolding aim_complex_lp_norm_def by simp
    have product_nonnegative: "0 \<le> (\<Prod>i<Suc n. aim_complex_lp_norm p (F i))"
      by (rule prod_nonneg) (simp add: aim_complex_lp_norm_def)
    have B_nonnegative: "0 \<le> ?B"
      by (intro mult_nonneg_nonneg C_nonnegative g_norm_nonnegative product_nonnegative)
    have F_new: "aim_complex_lp_on_plane p (F (Suc n))"
      using F_all by simp
    let ?w = "slp_oscillatory_modulation (tau1 (Suc n)) (c1 (Suc n))
      (\<lambda>y. cutoff1 (Suc n) y * slp_cauchy_transform (inner (Suc n))
        (slp_oscillatory_modulation (tau2 (Suc n)) (c2 (Suc n))
          (\<lambda>x. cutoff2 (Suc n) x * (F (Suc n) x * Pi (Suc n) x))) y)"
    have Pi_next: "Pi (Suc (Suc n)) = slp_cauchy_transform (outer (Suc n)) ?w"
      using recurrence by simp
    have inputs:
        "aim_complex_lp_on_plane p (F (Suc n)) \<and>
          Pi (Suc n) \<in> borel_measurable lborel \<and> 0 \<le> ?B \<and>
          (\<forall>x\<in>Y. norm (Pi (Suc n) x) \<le> ?B)"
      by (intro conjI F_new prior[THEN conjunct1] B_nonnegative prior[THEN conjunct2])
    have application:
        "slp_cauchy_transform (outer (Suc n)) ?w \<in> borel_measurable lborel \<and>
          (\<forall>z\<in>Y. slp_cauchy_integrable_at (outer (Suc n)) ?w z \<and>
            norm (slp_cauchy_transform (outer (Suc n)) ?w z) \<le>
              D * aim_complex_lp_norm p (F (Suc n)) * ?B)"
      by (rule D_all[rule_format, OF inputs])
    have measurable: "Pi (Suc (Suc n)) \<in> borel_measurable lborel"
      using application[THEN conjunct1] by (simp only: Pi_next)
    have points: "\<forall>z\<in>Y. norm (Pi (Suc (Suc n)) z) \<le>
        (D * C) * aim_complex_lp_norm b g *
          (\<Prod>i<Suc (Suc n). aim_complex_lp_norm p (F i))"
    proof (intro ballI)
      fix z assume z_in: "z \<in> Y"
      note point = application[THEN conjunct2, rule_format, OF z_in]
      show "norm (Pi (Suc (Suc n)) z) \<le>
          (D * C) * aim_complex_lp_norm b g *
            (\<Prod>i<Suc (Suc n). aim_complex_lp_norm p (F i))"
        using point[THEN conjunct2] by (simp add: Pi_next ac_simps)
    qed
    show "Pi (Suc (Suc n)) \<in> borel_measurable lborel \<and>
      (\<forall>z\<in>Y. norm (Pi (Suc (Suc n)) z) \<le>
        (D * C) * aim_complex_lp_norm b g * (\<Prod>i<(Suc (Suc n)). aim_complex_lp_norm p (F i)))"
      by (rule conjI[OF measurable points])
  qed
  show ?case by (rule exI[of _ "D * C"], rule conjI[OF constant_positive all])
qed

end

end
