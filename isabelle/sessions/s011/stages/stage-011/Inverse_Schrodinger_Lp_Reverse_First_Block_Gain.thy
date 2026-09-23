theory Inverse_Schrodinger_Lp_Reverse_First_Block_Gain
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_Two_Cauchy_Test_Cutoff"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Quantitative_Complex_Lp_Product"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_Uniform_Terminal_W1p_Gain"
begin

hide_const (open) Commutative_Ring.norm

section \<open>The first reversed-block exponents\<close>

lemma slp_reverse_first_block_exponents:
  fixes p b :: real
  assumes p_lower: "1 < p" and p_upper: "p < 2"
    and b_lower: "2 * slp_holder_conjugate p < b"
  defines "a \<equiv> p * b / (p + b)"
  shows "2 < b" and "1 < a" and "a < 2" and "a < p" and "a < b"
    and "1 < p / a" and "1 < b / a"
    and "1 / (p / a) + 1 / (b / a) = 1"
    and "1 / a = 1 / p + 1 / b"
proof -
  have p_positive: "0 < p" using p_lower by linarith
  have p_nonzero: "p \<noteq> 0" using p_positive by simp
  have denominator_positive: "0 < p - 1" using p_lower by linarith
  have conjugate_lower: "1 < slp_holder_conjugate p"
    unfolding slp_holder_conjugate_def
    using denominator_positive by (simp add: less_divide_eq)
  show b_above_two: "2 < b" using conjugate_lower b_lower by linarith
  have b_positive: "0 < b" using b_above_two by linarith
  have b_nonzero: "b \<noteq> 0" using b_positive by simp
  have sum_positive: "0 < p + b" using p_positive b_positive by simp
  have sum_nonzero: "p + b \<noteq> 0" using sum_positive by simp
  have b_above_conjugate: "p / (p - 1) < b"
    using conjugate_lower b_lower unfolding slp_holder_conjugate_def by linarith
  have product_lower: "p < b * (p - 1)"
    using b_above_conjugate denominator_positive by (simp add: divide_less_eq)
  have numerator_lower: "p + b < p * b"
    using product_lower by (simp add: algebra_simps)
  show a_lower: "1 < a"
    unfolding a_def using numerator_lower sum_positive by (simp add: less_divide_eq)
  have a_positive: "0 < a" using a_lower by linarith
  have p_square_positive: "0 < p * p" by (rule mult_pos_pos[OF p_positive p_positive])
  have b_square_positive: "0 < b * b" by (rule mult_pos_pos[OF b_positive b_positive])
  have p_numerator: "p * b < p * (p + b)"
    using p_square_positive by (simp add: algebra_simps)
  have b_numerator: "p * b < b * (p + b)"
    using b_square_positive by (simp add: algebra_simps)
  show a_below_p: "a < p"
    unfolding a_def using p_numerator sum_positive by (simp add: divide_less_eq)
  show "a < 2" using a_below_p p_upper by linarith
  show a_below_b: "a < b"
    unfolding a_def using b_numerator sum_positive by (simp add: divide_less_eq)
  show "1 < p / a" using a_positive a_below_p by (simp add: less_divide_eq)
  show "1 < b / a" using a_positive a_below_b by (simp add: less_divide_eq)
  have first_reciprocal: "1 / (p / a) = b / (p + b)"
    unfolding a_def using p_nonzero by (simp add: divide_inverse ac_simps)
  have second_reciprocal: "1 / (b / a) = p / (p + b)"
    unfolding a_def using b_nonzero by (simp add: divide_inverse ac_simps)
  show "1 / (p / a) + 1 / (b / a) = 1"
    by (simp only: first_reciprocal second_reciprocal add_divide_distrib[symmetric])
      (use sum_nonzero in simp)
  have inverse_a: "1 / a = (p + b) / (p * b)"
    unfolding a_def by simp
  have inverse_p: "1 / p = b / (p * b)"
    using b_nonzero by (simp add: divide_inverse ac_simps)
  have inverse_b: "1 / b = p / (p * b)"
    using p_nonzero by (simp add: divide_inverse ac_simps)
  show "1 / a = 1 / p + 1 / b"
    by (simp only: inverse_a inverse_p inverse_b add_divide_distrib[symmetric])
      (simp add: add.commute)
qed

section \<open>Coefficient times a finite-exponent terminal input\<close>

context aim_planar_hls_cauchy
begin

theorem slp_two_cauchy_test_cutoff_product_bound:
  fixes cutoff1 cutoff2 :: slp_scalar_field and Y :: "slp_point set"
  assumes p_lower: "1 < p" and p_upper: "p < 2"
    and b_lower: "2 * slp_holder_conjugate p < b"
    and target_bounded: "bounded Y"
    and cutoff1_test: "slp_test_function_on Y cutoff1"
    and cutoff2_test: "slp_test_function_on Y cutoff2"
  shows "\<exists>C::real. 0 < C \<and>
    (\<forall>tau1 tau2 c1 c2 F g outer inner.
      aim_complex_lp_on_plane p F \<and> aim_complex_lp_on_plane b g \<longrightarrow>
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
              (\<lambda>x. cutoff2 x * (F x * g x))) y)) z) \<le>
          C * aim_complex_lp_norm p F * aim_complex_lp_norm b g))"
proof -
  let ?a = "p * b / (p + b)"
  note exponents = slp_reverse_first_block_exponents[OF p_lower p_upper b_lower]
  have a_lower: "1 < ?a" by (rule exponents(2))
  have a_upper: "?a < 2" by (rule exponents(3))
  have a_positive: "0 < ?a" using a_lower by linarith
  have p_scale: "1 < p / ?a" by (rule exponents(6))
  have b_scale: "1 < b / ?a" by (rule exponents(7))
  have conjugate: "1 / (p / ?a) + 1 / (b / ?a) = 1"
    by (rule exponents(8))
  have cutoff2_plane: "slp_test_function_on UNIV cutoff2"
    using cutoff2_test unfolding slp_test_function_on_def by auto
  have cutoff2_measurable: "cutoff2 \<in> borel_measurable lborel"
    by (rule borel_measurable_integrable,
        rule slp_test_function_integrable_bounded(1)[OF cutoff2_plane])
  have cutoff2_bounded: "bounded (range cutoff2)"
    by (rule slp_test_function_integrable_bounded(2)[OF cutoff2_plane])
  obtain M :: real where M_positive: "0 < M"
    and M_bound: "\<And>x. norm (cutoff2 x) \<le> M"
    using cutoff2_bounded unfolding bounded_pos by blast
  have M_nonnegative: "0 \<le> M" using M_positive by linarith
  obtain H :: real where H_data:
      "0 < H \<and>
        (\<forall>tau1 tau2 c1 c2 h outer inner.
          aim_complex_lp_on_plane ?a h \<longrightarrow>
          slp_cauchy_transform outer (slp_oscillatory_modulation tau1 c1
              (\<lambda>y. cutoff1 y * slp_cauchy_transform inner
                (slp_oscillatory_modulation tau2 c2 h) y)) \<in> borel_measurable lborel \<and>
          (\<forall>z\<in>Y. slp_cauchy_integrable_at outer (slp_oscillatory_modulation tau1 c1
              (\<lambda>y. cutoff1 y * slp_cauchy_transform inner
                (slp_oscillatory_modulation tau2 c2 h) y)) z \<and>
            norm (slp_cauchy_transform outer (slp_oscillatory_modulation tau1 c1
              (\<lambda>y. cutoff1 y * slp_cauchy_transform inner
                (slp_oscillatory_modulation tau2 c2 h) y)) z) \<le> H * aim_complex_lp_norm ?a h))"
    using slp_two_oscillatory_cauchy_test_cutoff_bound[OF a_lower a_upper
        target_bounded cutoff1_test] ..
  have H_positive: "0 < H" by (rule conjunct1[OF H_data])
  have H_nonnegative: "0 \<le> H" using H_positive by linarith
  note H_all = H_data[THEN conjunct2]
  have constant_positive: "0 < H * M" by (rule mult_pos_pos[OF H_positive M_positive])
  have all: "(\<forall>tau1 tau2 c1 c2 F g outer inner.
      aim_complex_lp_on_plane p F \<and> aim_complex_lp_on_plane b g \<longrightarrow>
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
              (\<lambda>x. cutoff2 x * (F x * g x))) y)) z) \<le>
          (H * M) * aim_complex_lp_norm p F * aim_complex_lp_norm b g))"
  proof (intro allI impI)
    fix tau1 tau2 c1 c2 F g outer inner
    assume inputs: "aim_complex_lp_on_plane p F \<and> aim_complex_lp_on_plane b g"
    have F_lp: "aim_complex_lp_on_plane p F" by (rule conjunct1[OF inputs])
    have g_lp: "aim_complex_lp_on_plane b g" by (rule conjunct2[OF inputs])
    let ?v = "\<lambda>x. cutoff2 x * (F x * g x)"
    let ?w = "(slp_oscillatory_modulation tau1 c1
          (\<lambda>y. cutoff1 y * slp_cauchy_transform inner
            (slp_oscillatory_modulation tau2 c2
              (\<lambda>x. cutoff2 x * (F x * g x))) y))"
    note product = slp_aim_complex_lp_on_plane_product_norm_bound[
      OF a_positive p_scale b_scale conjugate F_lp g_lp]
    note input = slp_complex_lp_bounded_multiplier[
      OF a_positive cutoff2_measurable M_bound M_nonnegative product(1)]
    have v_bound: "aim_complex_lp_norm ?a ?v \<le>
        M * (aim_complex_lp_norm p F * aim_complex_lp_norm b g)"
      by (rule order_trans[OF input(2)], rule mult_left_mono[OF product(2) M_nonnegative])
    have application:
        "slp_cauchy_transform outer ?w \<in> borel_measurable lborel \<and>
          (\<forall>z\<in>Y. slp_cauchy_integrable_at outer ?w z \<and>
            norm (slp_cauchy_transform outer ?w z) \<le> H * aim_complex_lp_norm ?a ?v)"
      by (rule H_all[rule_format, OF input(1)])
    have points: "\<forall>z\<in>Y. slp_cauchy_integrable_at outer ?w z \<and>
        norm (slp_cauchy_transform outer ?w z) \<le>
          (H * M) * aim_complex_lp_norm p F * aim_complex_lp_norm b g"
    proof (intro ballI)
      fix z assume z_in: "z \<in> Y"
      note at_z = application[THEN conjunct2, rule_format, OF z_in]
      have bound: "norm (slp_cauchy_transform outer ?w z) \<le>
          (H * M) * aim_complex_lp_norm p F * aim_complex_lp_norm b g"
      proof -
        have "norm (slp_cauchy_transform outer ?w z) \<le> H * aim_complex_lp_norm ?a ?v"
          by (rule conjunct2[OF at_z])
        also have "... \<le> H * (M * (aim_complex_lp_norm p F * aim_complex_lp_norm b g))"
          by (rule mult_left_mono[OF v_bound H_nonnegative])
        also have "... = (H * M) * aim_complex_lp_norm p F * aim_complex_lp_norm b g"
          by (simp only: mult.assoc)
        finally show ?thesis .
      qed
      show "slp_cauchy_integrable_at outer ?w z \<and>
        norm (slp_cauchy_transform outer ?w z) \<le>
          (H * M) * aim_complex_lp_norm p F * aim_complex_lp_norm b g"
        by (rule conjI[OF at_z[THEN conjunct1] bound])
    qed
    show "slp_cauchy_transform outer ?w \<in> borel_measurable lborel \<and>
        (\<forall>z\<in>Y. slp_cauchy_integrable_at outer ?w z \<and>
          norm (slp_cauchy_transform outer ?w z) \<le>
            (H * M) * aim_complex_lp_norm p F * aim_complex_lp_norm b g)"
      by (rule conjI[OF application[THEN conjunct1] points])
  qed
  show ?thesis by (rule exI[of _ "H * M"], rule conjI[OF constant_positive all])
qed

end

section \<open>The first reversed branch inherits the terminal decay\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_reverse_first_block_terminal_gain:
  fixes cutoff1 cutoff2 :: slp_scalar_field and Y :: "slp_point set"
  assumes p_lower: "1 < p" and p_upper: "p < 2"
    and b_lower: "2 * slp_holder_conjugate p < b"
    and target_bounded: "bounded Y"
    and cutoff1_test: "slp_test_function_on Y cutoff1"
    and cutoff2_test: "slp_test_function_on Y cutoff2"
  shows "\<exists>C::real. 0 < C \<and>
    (\<forall>tau c f F epsilon0 epsilon1 epsilon2 terminal outer inner.
      2 \<le> tau \<and> slp_test_function_on Y f \<and> aim_complex_lp_on_plane p F \<and>
      epsilon0 \<in> {-1, 1} \<and> epsilon1 \<in> {-1, 1} \<and> epsilon2 \<in> {-1, 1}
      \<longrightarrow>
      slp_cauchy_transform outer (slp_oscillatory_modulation (epsilon1 * tau) c
          (\<lambda>y. cutoff1 y * slp_cauchy_transform inner
            (slp_oscillatory_modulation (epsilon2 * tau) c
              (\<lambda>x. cutoff2 x * (F x * slp_cauchy_transform terminal
                (slp_oscillatory_modulation (epsilon0 * tau) c f) x))) y)) \<in> borel_measurable lborel \<and>
      (\<forall>z\<in>Y. slp_cauchy_integrable_at outer (slp_oscillatory_modulation (epsilon1 * tau) c
          (\<lambda>y. cutoff1 y * slp_cauchy_transform inner
            (slp_oscillatory_modulation (epsilon2 * tau) c
              (\<lambda>x. cutoff2 x * (F x * slp_cauchy_transform terminal
                (slp_oscillatory_modulation (epsilon0 * tau) c f) x))) y)) z \<and>
        norm (slp_cauchy_transform outer (slp_oscillatory_modulation (epsilon1 * tau) c
          (\<lambda>y. cutoff1 y * slp_cauchy_transform inner
            (slp_oscillatory_modulation (epsilon2 * tau) c
              (\<lambda>x. cutoff2 x * (F x * slp_cauchy_transform terminal
                (slp_oscillatory_modulation (epsilon0 * tau) c f) x))) y)) z) \<le>
          C * inverse (sqrt tau) *
            slp_w1p_norm_on (slp_hls_source_exponent b) UNIV f (slp_classical_gradient f) *
            aim_complex_lp_norm p F))"
proof -
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
  obtain H :: real where H_data:
      "0 < H \<and> (\<forall>tau1 tau2 c1 c2 F g outer inner.
      aim_complex_lp_on_plane p F \<and> aim_complex_lp_on_plane b g \<longrightarrow>
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
              (\<lambda>x. cutoff2 x * (F x * g x))) y)) z) \<le>
          H * aim_complex_lp_norm p F * aim_complex_lp_norm b g))"
    using slp_two_cauchy_test_cutoff_product_bound[OF p_lower p_upper b_lower
        target_bounded cutoff1_test cutoff2_test] ..
  have H_positive: "0 < H" by (rule conjunct1[OF H_data])
  have H_nonnegative: "0 \<le> H" using H_positive by linarith
  note H_all = H_data[THEN conjunct2]
  have constant_positive: "0 < H * T" by (rule mult_pos_pos[OF H_positive T_positive])
  have all: "(\<forall>tau c f F epsilon0 epsilon1 epsilon2 terminal outer inner.
      2 \<le> tau \<and> slp_test_function_on Y f \<and> aim_complex_lp_on_plane p F \<and>
      epsilon0 \<in> {-1, 1} \<and> epsilon1 \<in> {-1, 1} \<and> epsilon2 \<in> {-1, 1}
      \<longrightarrow>
      slp_cauchy_transform outer (slp_oscillatory_modulation (epsilon1 * tau) c
          (\<lambda>y. cutoff1 y * slp_cauchy_transform inner
            (slp_oscillatory_modulation (epsilon2 * tau) c
              (\<lambda>x. cutoff2 x * (F x * slp_cauchy_transform terminal
                (slp_oscillatory_modulation (epsilon0 * tau) c f) x))) y)) \<in> borel_measurable lborel \<and>
      (\<forall>z\<in>Y. slp_cauchy_integrable_at outer (slp_oscillatory_modulation (epsilon1 * tau) c
          (\<lambda>y. cutoff1 y * slp_cauchy_transform inner
            (slp_oscillatory_modulation (epsilon2 * tau) c
              (\<lambda>x. cutoff2 x * (F x * slp_cauchy_transform terminal
                (slp_oscillatory_modulation (epsilon0 * tau) c f) x))) y)) z \<and>
        norm (slp_cauchy_transform outer (slp_oscillatory_modulation (epsilon1 * tau) c
          (\<lambda>y. cutoff1 y * slp_cauchy_transform inner
            (slp_oscillatory_modulation (epsilon2 * tau) c
              (\<lambda>x. cutoff2 x * (F x * slp_cauchy_transform terminal
                (slp_oscillatory_modulation (epsilon0 * tau) c f) x))) y)) z) \<le>
          (H * T) * inverse (sqrt tau) *
            slp_w1p_norm_on (slp_hls_source_exponent b) UNIV f (slp_classical_gradient f) *
            aim_complex_lp_norm p F))"
  proof (intro allI impI)
    fix tau epsilon0 epsilon1 epsilon2 :: real
      and c :: slp_point and f F :: slp_scalar_field
      and terminal outer inner :: slp_cauchy_orientation
    assume hypotheses:
        "2 \<le> tau \<and> slp_test_function_on Y f \<and> aim_complex_lp_on_plane p F \<and>
          epsilon0 \<in> {-1, 1} \<and> epsilon1 \<in> {-1, 1} \<and> epsilon2 \<in> {-1, 1}"
    have terminal_hypotheses:
        "2 \<le> tau \<and> slp_test_function_on Y f \<and> epsilon0 \<in> {-1, 1}"
      using hypotheses by blast
    have F_lp: "aim_complex_lp_on_plane p F" using hypotheses by blast
    let ?g = "slp_cauchy_transform terminal
                (slp_oscillatory_modulation (epsilon0 * tau) c f)"
    let ?w = "(slp_oscillatory_modulation (epsilon1 * tau) c
          (\<lambda>y. cutoff1 y * slp_cauchy_transform inner
            (slp_oscillatory_modulation (epsilon2 * tau) c
              (\<lambda>x. cutoff2 x * (F x * slp_cauchy_transform terminal
                (slp_oscillatory_modulation (epsilon0 * tau) c f) x))) y))"
    let ?W = "slp_w1p_norm_on (slp_hls_source_exponent b) UNIV f (slp_classical_gradient f)"
    have terminal_data:
        "aim_complex_lp_on_plane b ?g \<and>
          aim_complex_lp_norm b ?g \<le> T * inverse (sqrt tau) * ?W"
      by (rule T_all[rule_format, OF terminal_hypotheses])
    have product_hypotheses:
        "aim_complex_lp_on_plane p F \<and> aim_complex_lp_on_plane b ?g"
      by (rule conjI[OF F_lp terminal_data[THEN conjunct1]])
    have application:
        "slp_cauchy_transform outer ?w \<in> borel_measurable lborel \<and>
          (\<forall>z\<in>Y. slp_cauchy_integrable_at outer ?w z \<and>
            norm (slp_cauchy_transform outer ?w z) \<le>
              H * aim_complex_lp_norm p F * aim_complex_lp_norm b ?g)"
      by (rule H_all[rule_format, OF product_hypotheses])
    have F_norm_nonnegative: "0 \<le> aim_complex_lp_norm p F"
      unfolding aim_complex_lp_norm_def by simp
    have factor_nonnegative: "0 \<le> H * aim_complex_lp_norm p F"
      by (rule mult_nonneg_nonneg[OF H_nonnegative F_norm_nonnegative])
    have points: "\<forall>z\<in>Y. slp_cauchy_integrable_at outer ?w z \<and>
        norm (slp_cauchy_transform outer ?w z) \<le>
          (H * T) * inverse (sqrt tau) * ?W * aim_complex_lp_norm p F"
    proof (intro ballI)
      fix z assume z_in: "z \<in> Y"
      note at_z = application[THEN conjunct2, rule_format, OF z_in]
      have bound: "norm (slp_cauchy_transform outer ?w z) \<le>
          (H * T) * inverse (sqrt tau) * ?W * aim_complex_lp_norm p F"
      proof -
        have "norm (slp_cauchy_transform outer ?w z) \<le>
            H * aim_complex_lp_norm p F * aim_complex_lp_norm b ?g"
          by (rule conjunct2[OF at_z])
        also have "... \<le>
            (H * aim_complex_lp_norm p F) * (T * inverse (sqrt tau) * ?W)"
          by (rule mult_left_mono[OF terminal_data[THEN conjunct2] factor_nonnegative])
        also have "... =
            (H * T) * inverse (sqrt tau) * ?W * aim_complex_lp_norm p F"
          by (simp only: mult.assoc mult.commute mult.left_commute)
        finally show ?thesis .
      qed
      show "slp_cauchy_integrable_at outer ?w z \<and>
        norm (slp_cauchy_transform outer ?w z) \<le>
          (H * T) * inverse (sqrt tau) * ?W * aim_complex_lp_norm p F"
        by (rule conjI[OF at_z[THEN conjunct1] bound])
    qed
    show "slp_cauchy_transform outer ?w \<in> borel_measurable lborel \<and>
        (\<forall>z\<in>Y. slp_cauchy_integrable_at outer ?w z \<and>
          norm (slp_cauchy_transform outer ?w z) \<le>
            (H * T) * inverse (sqrt tau) * ?W * aim_complex_lp_norm p F)"
      by (rule conjI[OF application[THEN conjunct1] points])
  qed
  show ?thesis by (rule exI[of _ "H * T"], rule conjI[OF constant_positive all])
qed

end

end
