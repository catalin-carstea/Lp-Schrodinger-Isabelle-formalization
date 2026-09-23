theory Inverse_Schrodinger_Lp_Reverse_Branch_Terminal_Gain
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_Reverse_Finite_Blocks"
begin

hide_const (open) Commutative_Ring.norm

section \<open>All positive reverse orders inherit the uniform terminal Sobolev gain\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_uniform_reverse_branch_terminal_gain:
  fixes cutoff1 cutoff2 :: "nat \<Rightarrow> slp_scalar_field"
    and Y :: "slp_point set" and m :: nat
  assumes p_lower: "1 < p" and p_upper: "p < 2"
    and b_lower: "2 * slp_holder_conjugate p < b"
    and target_bounded: "bounded Y" and order_positive: "0 < m"
    and cutoff1_tests: "\<forall>i<m. slp_test_function_on Y (cutoff1 i)"
    and cutoff2_tests: "\<forall>i<m. slp_test_function_on Y (cutoff2 i)"
  shows "\<exists>C::real. 0 < C \<and> (\<forall>tau c f F epsilon0 epsilon1 epsilon2 terminal outer inner Pi.
      2 \<le> tau \<and> slp_test_function_on Y f \<and>
      (\<forall>i<m. aim_complex_lp_on_plane p (F i)) \<and>
      epsilon0 \<in> {-1, 1} \<and>
      (\<forall>i<m. epsilon1 i \<in> {-1, 1} \<and> epsilon2 i \<in> {-1, 1}) \<and>
      Pi 0 = slp_cauchy_transform terminal
        (slp_oscillatory_modulation (epsilon0 * tau) c f) \<and> (\<forall>i<m. Pi (Suc i) =
        slp_cauchy_transform (outer i)
          (slp_oscillatory_modulation (epsilon1 i * tau) c
            (\<lambda>y. cutoff1 i y * slp_cauchy_transform (inner i)
              (slp_oscillatory_modulation (epsilon2 i * tau) c
                (\<lambda>x. cutoff2 i x * (F i x * Pi i x))) y))) \<longrightarrow> Pi m \<in> borel_measurable lborel \<and>
      (\<forall>z\<in>Y. norm (Pi m z) \<le> C * inverse (sqrt tau) *
        slp_w1p_norm_on (slp_hls_source_exponent b) UNIV f (slp_classical_gradient f) *
        (\<Prod>i<m. aim_complex_lp_norm p (F i))))"
proof -
  obtain n :: nat where m_suc: "m = Suc n" using order_positive by (cases m) auto
  have cutoff1_suc: "\<forall>i<Suc n. slp_test_function_on Y (cutoff1 i)"
    using cutoff1_tests by (simp only: m_suc)
  have cutoff2_suc: "\<forall>i<Suc n. slp_test_function_on Y (cutoff2 i)"
    using cutoff2_tests by (simp only: m_suc)
  have H_exists: "\<exists>H::real. 0 < H \<and> (\<forall>tau1 tau2 c1 c2 F g outer inner Pi.
      aim_complex_lp_on_plane b g \<and>
      (\<forall>i<m. aim_complex_lp_on_plane p (F i)) \<and> Pi 0 = g \<and>
      (\<forall>i<m. Pi (Suc i) = slp_cauchy_transform (outer i)
            (slp_oscillatory_modulation (tau1 i) (c1 i)
              (\<lambda>y. cutoff1 i y * slp_cauchy_transform (inner i)
                (slp_oscillatory_modulation (tau2 i) (c2 i)
                  (\<lambda>x. cutoff2 i x * (F i x * Pi i x))) y))) \<longrightarrow> Pi m \<in> borel_measurable lborel \<and>
      (\<forall>z\<in>Y. norm (Pi m z) \<le>
        H * aim_complex_lp_norm b g * (\<Prod>i<m. aim_complex_lp_norm p (F i))))"
    using slp_reverse_finite_blocks_from_lb[OF p_lower p_upper b_lower
        target_bounded cutoff1_suc cutoff2_suc]
    by (simp only: m_suc)
  obtain H :: real where H_data: "0 < H \<and> (\<forall>tau1 tau2 c1 c2 F g outer inner Pi.
      aim_complex_lp_on_plane b g \<and>
      (\<forall>i<m. aim_complex_lp_on_plane p (F i)) \<and> Pi 0 = g \<and>
      (\<forall>i<m. Pi (Suc i) = slp_cauchy_transform (outer i)
            (slp_oscillatory_modulation (tau1 i) (c1 i)
              (\<lambda>y. cutoff1 i y * slp_cauchy_transform (inner i)
                (slp_oscillatory_modulation (tau2 i) (c2 i)
                  (\<lambda>x. cutoff2 i x * (F i x * Pi i x))) y))) \<longrightarrow> Pi m \<in> borel_measurable lborel \<and>
      (\<forall>z\<in>Y. norm (Pi m z) \<le>
        H * aim_complex_lp_norm b g * (\<Prod>i<m. aim_complex_lp_norm p (F i))))" using H_exists ..
  have H_positive: "0 < H" by (rule conjunct1[OF H_data])
  have H_nonnegative: "0 \<le> H" using H_positive by linarith
  note H_all = H_data[THEN conjunct2]
  have b_above_two: "2 < b"
    by (rule slp_reverse_first_block_exponents(1)[OF p_lower p_upper b_lower])
  obtain T :: real where T_data:
      "0 < T \<and>
        (\<forall>tau c f epsilon orientation.
          2 \<le> tau \<and> slp_test_function_on Y f \<and> epsilon \<in> {-1, 1} \<longrightarrow>
          aim_complex_lp_on_plane b
            (slp_cauchy_transform orientation
              (slp_oscillatory_modulation (epsilon * tau) c f)) \<and>
          aim_complex_lp_norm b
            (slp_cauchy_transform orientation
              (slp_oscillatory_modulation (epsilon * tau) c f))
            \<le> T * inverse (sqrt tau) *
              slp_w1p_norm_on (slp_hls_source_exponent b) UNIV f (slp_classical_gradient f))"
    using slp_uniform_terminal_w1p_gain_plane[OF b_above_two target_bounded] ..
  have T_positive: "0 < T" by (rule conjunct1[OF T_data])
  note T_all = T_data[THEN conjunct2]
  have constant_positive: "0 < H * T" by (rule mult_pos_pos[OF H_positive T_positive])
  have all: "(\<forall>tau c f F epsilon0 epsilon1 epsilon2 terminal outer inner Pi.
      2 \<le> tau \<and> slp_test_function_on Y f \<and>
      (\<forall>i<m. aim_complex_lp_on_plane p (F i)) \<and>
      epsilon0 \<in> {-1, 1} \<and>
      (\<forall>i<m. epsilon1 i \<in> {-1, 1} \<and> epsilon2 i \<in> {-1, 1}) \<and>
      Pi 0 = slp_cauchy_transform terminal
        (slp_oscillatory_modulation (epsilon0 * tau) c f) \<and> (\<forall>i<m. Pi (Suc i) =
        slp_cauchy_transform (outer i)
          (slp_oscillatory_modulation (epsilon1 i * tau) c
            (\<lambda>y. cutoff1 i y * slp_cauchy_transform (inner i)
              (slp_oscillatory_modulation (epsilon2 i * tau) c
                (\<lambda>x. cutoff2 i x * (F i x * Pi i x))) y))) \<longrightarrow> Pi m \<in> borel_measurable lborel \<and>
      (\<forall>z\<in>Y. norm (Pi m z) \<le> (H * T) * inverse (sqrt tau) *
        slp_w1p_norm_on (slp_hls_source_exponent b) UNIV f (slp_classical_gradient f) *
        (\<Prod>i<m. aim_complex_lp_norm p (F i))))"
  proof (intro allI impI)
    fix tau epsilon0 :: real and c :: slp_point and f :: slp_scalar_field
      and F Pi :: "nat \<Rightarrow> slp_scalar_field"
      and epsilon1 epsilon2 :: "nat \<Rightarrow> real"
      and terminal :: slp_cauchy_orientation
      and outer inner :: "nat \<Rightarrow> slp_cauchy_orientation"
    assume hypotheses: "2 \<le> tau \<and> slp_test_function_on Y f \<and>
      (\<forall>i<m. aim_complex_lp_on_plane p (F i)) \<and>
      epsilon0 \<in> {-1, 1} \<and>
      (\<forall>i<m. epsilon1 i \<in> {-1, 1} \<and> epsilon2 i \<in> {-1, 1}) \<and>
      Pi 0 = slp_cauchy_transform terminal
        (slp_oscillatory_modulation (epsilon0 * tau) c f) \<and> (\<forall>i<m. Pi (Suc i) =
        slp_cauchy_transform (outer i)
          (slp_oscillatory_modulation (epsilon1 i * tau) c
            (\<lambda>y. cutoff1 i y * slp_cauchy_transform (inner i)
              (slp_oscillatory_modulation (epsilon2 i * tau) c
                (\<lambda>x. cutoff2 i x * (F i x * Pi i x))) y)))"
    have tau_lower: "2 \<le> tau" by (rule conjunct1[OF hypotheses])
    note tail1 = hypotheses[THEN conjunct2]
    have f_test: "slp_test_function_on Y f" by (rule conjunct1[OF tail1])
    note tail2 = tail1[THEN conjunct2]
    note F_all = tail2[THEN conjunct1]
    note tail3 = tail2[THEN conjunct2]
    have epsilon0_sign: "epsilon0 \<in> {-1, 1}" by (rule conjunct1[OF tail3])
    note tail4 = tail3[THEN conjunct2]
    note tail5 = tail4[THEN conjunct2]
    note Pi_zero = tail5[THEN conjunct1]
    note recurrence = tail5[THEN conjunct2]
    let ?g = "slp_cauchy_transform terminal
        (slp_oscillatory_modulation (epsilon0 * tau) c f)"
    let ?W = "slp_w1p_norm_on (slp_hls_source_exponent b) UNIV f (slp_classical_gradient f)"
    let ?P = "(\<Prod>i<m. aim_complex_lp_norm p (F i))"
    have terminal_hypotheses:
        "2 \<le> tau \<and> slp_test_function_on Y f \<and> epsilon0 \<in> {-1, 1}"
      by (intro conjI tau_lower f_test epsilon0_sign)
    have terminal_data:
        "aim_complex_lp_on_plane b ?g \<and>
          aim_complex_lp_norm b ?g \<le> T * inverse (sqrt tau) * ?W"
      by (rule T_all[rule_format, OF terminal_hypotheses])
    have H_hypotheses: "aim_complex_lp_on_plane b ?g \<and>
      (\<forall>i<m. aim_complex_lp_on_plane p (F i)) \<and> Pi 0 = ?g \<and>
      (\<forall>i<m. Pi (Suc i) = slp_cauchy_transform (outer i)
            (slp_oscillatory_modulation (epsilon1 i * tau) c
              (\<lambda>y. cutoff1 i y * slp_cauchy_transform (inner i)
                (slp_oscillatory_modulation (epsilon2 i * tau) c
                  (\<lambda>x. cutoff2 i x * (F i x * Pi i x))) y)))"
      by (intro conjI terminal_data[THEN conjunct1] F_all Pi_zero recurrence)
    have application:
        "Pi m \<in> borel_measurable lborel \<and>
          (\<forall>z\<in>Y. norm (Pi m z) \<le> H * aim_complex_lp_norm b ?g * ?P)"
      by (rule H_all[rule_format, OF H_hypotheses])
    have product_nonnegative: "0 \<le> ?P"
      by (rule prod_nonneg) (simp add: aim_complex_lp_norm_def)
    have factor_nonnegative: "0 \<le> H * ?P"
      by (rule mult_nonneg_nonneg[OF H_nonnegative product_nonnegative])
    have points: "\<forall>z\<in>Y. norm (Pi m z) \<le>
        (H * T) * inverse (sqrt tau) * ?W * ?P"
    proof (intro ballI)
      fix z assume z_in: "z \<in> Y"
      have "norm (Pi m z) \<le> H * aim_complex_lp_norm b ?g * ?P"
        by (rule application[THEN conjunct2, rule_format, OF z_in])
      also have "... = (H * ?P) * aim_complex_lp_norm b ?g" by (simp only: ac_simps)
      also have "... \<le> (H * ?P) * (T * inverse (sqrt tau) * ?W)"
        by (rule mult_left_mono[OF terminal_data[THEN conjunct2] factor_nonnegative])
      also have "... = (H * T) * inverse (sqrt tau) * ?W * ?P" by (simp only: ac_simps)
      finally show "norm (Pi m z) \<le> (H * T) * inverse (sqrt tau) * ?W * ?P" .
    qed
    show "Pi m \<in> borel_measurable lborel \<and>
      (\<forall>z\<in>Y. norm (Pi m z) \<le> (H * T) * inverse (sqrt tau) *
        slp_w1p_norm_on (slp_hls_source_exponent b) UNIV f (slp_classical_gradient f) *
        (\<Prod>i<m. aim_complex_lp_norm p (F i)))"
      by (rule conjI[OF application[THEN conjunct1] points])
  qed
  show ?thesis by (rule exI[of _ "H * T"], rule conjI[OF constant_positive all])
qed

section \<open>Repeated coefficients give the exact potential norm power\<close>

theorem slp_uniform_reverse_branch_constant_coefficient_gain:
  fixes cutoff1 cutoff2 :: "nat \<Rightarrow> slp_scalar_field"
    and Y :: "slp_point set" and m :: nat
  assumes p_lower: "1 < p" and p_upper: "p < 2"
    and b_lower: "2 * slp_holder_conjugate p < b"
    and target_bounded: "bounded Y" and order_positive: "0 < m"
    and cutoff1_tests: "\<forall>i<m. slp_test_function_on Y (cutoff1 i)"
    and cutoff2_tests: "\<forall>i<m. slp_test_function_on Y (cutoff2 i)"
  shows "\<exists>C::real. 0 < C \<and> (\<forall>tau c f q epsilon0 epsilon1 epsilon2 terminal outer inner Pi.
      2 \<le> tau \<and> slp_test_function_on Y f \<and>
      aim_complex_lp_on_plane p q \<and>
      epsilon0 \<in> {-1, 1} \<and>
      (\<forall>i<m. epsilon1 i \<in> {-1, 1} \<and> epsilon2 i \<in> {-1, 1}) \<and>
      Pi 0 = slp_cauchy_transform terminal
        (slp_oscillatory_modulation (epsilon0 * tau) c f) \<and> (\<forall>i<m. Pi (Suc i) =
        slp_cauchy_transform (outer i)
          (slp_oscillatory_modulation (epsilon1 i * tau) c
            (\<lambda>y. cutoff1 i y * slp_cauchy_transform (inner i)
              (slp_oscillatory_modulation (epsilon2 i * tau) c
                (\<lambda>x. cutoff2 i x * (q x * Pi i x))) y))) \<longrightarrow> Pi m \<in> borel_measurable lborel \<and>
      (\<forall>z\<in>Y. norm (Pi m z) \<le> C * inverse (sqrt tau) *
        slp_w1p_norm_on (slp_hls_source_exponent b) UNIV f (slp_classical_gradient f) *
        (aim_complex_lp_norm p q) ^ m))"
proof -
  obtain C :: real where C_data: "0 < C \<and> (\<forall>tau c f F epsilon0 epsilon1 epsilon2 terminal outer inner Pi.
      2 \<le> tau \<and> slp_test_function_on Y f \<and>
      (\<forall>i<m. aim_complex_lp_on_plane p (F i)) \<and>
      epsilon0 \<in> {-1, 1} \<and>
      (\<forall>i<m. epsilon1 i \<in> {-1, 1} \<and> epsilon2 i \<in> {-1, 1}) \<and>
      Pi 0 = slp_cauchy_transform terminal
        (slp_oscillatory_modulation (epsilon0 * tau) c f) \<and> (\<forall>i<m. Pi (Suc i) =
        slp_cauchy_transform (outer i)
          (slp_oscillatory_modulation (epsilon1 i * tau) c
            (\<lambda>y. cutoff1 i y * slp_cauchy_transform (inner i)
              (slp_oscillatory_modulation (epsilon2 i * tau) c
                (\<lambda>x. cutoff2 i x * (F i x * Pi i x))) y))) \<longrightarrow> Pi m \<in> borel_measurable lborel \<and>
      (\<forall>z\<in>Y. norm (Pi m z) \<le> C * inverse (sqrt tau) *
        slp_w1p_norm_on (slp_hls_source_exponent b) UNIV f (slp_classical_gradient f) *
        (\<Prod>i<m. aim_complex_lp_norm p (F i))))"
    using slp_uniform_reverse_branch_terminal_gain[OF p_lower p_upper
        b_lower target_bounded order_positive cutoff1_tests cutoff2_tests] ..
  have C_positive: "0 < C" by (rule conjunct1[OF C_data])
  note C_all = C_data[THEN conjunct2]
  have all: "(\<forall>tau c f q epsilon0 epsilon1 epsilon2 terminal outer inner Pi.
      2 \<le> tau \<and> slp_test_function_on Y f \<and>
      aim_complex_lp_on_plane p q \<and>
      epsilon0 \<in> {-1, 1} \<and>
      (\<forall>i<m. epsilon1 i \<in> {-1, 1} \<and> epsilon2 i \<in> {-1, 1}) \<and>
      Pi 0 = slp_cauchy_transform terminal
        (slp_oscillatory_modulation (epsilon0 * tau) c f) \<and> (\<forall>i<m. Pi (Suc i) =
        slp_cauchy_transform (outer i)
          (slp_oscillatory_modulation (epsilon1 i * tau) c
            (\<lambda>y. cutoff1 i y * slp_cauchy_transform (inner i)
              (slp_oscillatory_modulation (epsilon2 i * tau) c
                (\<lambda>x. cutoff2 i x * (q x * Pi i x))) y))) \<longrightarrow> Pi m \<in> borel_measurable lborel \<and>
      (\<forall>z\<in>Y. norm (Pi m z) \<le> C * inverse (sqrt tau) *
        slp_w1p_norm_on (slp_hls_source_exponent b) UNIV f (slp_classical_gradient f) *
        (aim_complex_lp_norm p q) ^ m))"
  proof (intro allI impI)
    fix tau epsilon0 :: real and c :: slp_point and f q :: slp_scalar_field
      and Pi :: "nat \<Rightarrow> slp_scalar_field"
      and epsilon1 epsilon2 :: "nat \<Rightarrow> real"
      and terminal :: slp_cauchy_orientation
      and outer inner :: "nat \<Rightarrow> slp_cauchy_orientation"
    assume hypotheses: "2 \<le> tau \<and> slp_test_function_on Y f \<and>
      aim_complex_lp_on_plane p q \<and>
      epsilon0 \<in> {-1, 1} \<and>
      (\<forall>i<m. epsilon1 i \<in> {-1, 1} \<and> epsilon2 i \<in> {-1, 1}) \<and>
      Pi 0 = slp_cauchy_transform terminal
        (slp_oscillatory_modulation (epsilon0 * tau) c f) \<and> (\<forall>i<m. Pi (Suc i) =
        slp_cauchy_transform (outer i)
          (slp_oscillatory_modulation (epsilon1 i * tau) c
            (\<lambda>y. cutoff1 i y * slp_cauchy_transform (inner i)
              (slp_oscillatory_modulation (epsilon2 i * tau) c
                (\<lambda>x. cutoff2 i x * (q x * Pi i x))) y)))"
    have tau_lower: "2 \<le> tau" by (rule conjunct1[OF hypotheses])
    note tail1 = hypotheses[THEN conjunct2]
    have f_test: "slp_test_function_on Y f" by (rule conjunct1[OF tail1])
    note tail2 = tail1[THEN conjunct2]
    have q_lp: "aim_complex_lp_on_plane p q" by (rule conjunct1[OF tail2])
    note rest = tail2[THEN conjunct2]
    have all_coefficients: "\<forall>i<m. aim_complex_lp_on_plane p q"
      by (intro allI impI, rule q_lp)
    have generic_hypotheses: "2 \<le> tau \<and> slp_test_function_on Y f \<and>
      (\<forall>i<m. aim_complex_lp_on_plane p q) \<and>
      epsilon0 \<in> {-1, 1} \<and>
      (\<forall>i<m. epsilon1 i \<in> {-1, 1} \<and> epsilon2 i \<in> {-1, 1}) \<and>
      Pi 0 = slp_cauchy_transform terminal
        (slp_oscillatory_modulation (epsilon0 * tau) c f) \<and> (\<forall>i<m. Pi (Suc i) =
        slp_cauchy_transform (outer i)
          (slp_oscillatory_modulation (epsilon1 i * tau) c
            (\<lambda>y. cutoff1 i y * slp_cauchy_transform (inner i)
              (slp_oscillatory_modulation (epsilon2 i * tau) c
                (\<lambda>x. cutoff2 i x * (q x * Pi i x))) y)))"
      by (rule conjI[OF tau_lower], rule conjI[OF f_test],
          rule conjI[OF all_coefficients rest])
    have application:
        "Pi m \<in> borel_measurable lborel \<and>
          (\<forall>z\<in>Y. norm (Pi m z) \<le> C * inverse (sqrt tau) *
            slp_w1p_norm_on (slp_hls_source_exponent b) UNIV f (slp_classical_gradient f) *
            (\<Prod>i<m. aim_complex_lp_norm p q))"
      by (rule C_all[rule_format, OF generic_hypotheses])
    show "Pi m \<in> borel_measurable lborel \<and>
        (\<forall>z\<in>Y. norm (Pi m z) \<le> C * inverse (sqrt tau) *
          slp_w1p_norm_on (slp_hls_source_exponent b) UNIV f (slp_classical_gradient f) *
          (aim_complex_lp_norm p q) ^ m)"
      using application by simp
  qed
  show ?thesis by (rule exI[of _ C], rule conjI[OF C_positive all])
qed

end

end
