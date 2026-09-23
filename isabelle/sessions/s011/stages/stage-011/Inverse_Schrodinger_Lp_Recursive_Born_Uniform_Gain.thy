theory Inverse_Schrodinger_Lp_Recursive_Born_Uniform_Gain
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_Reverse_Branch_Terminal_Gain"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Right_Recursive_Branch"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Exact insertion of the fixed cutoff in both Born recursions\<close>

lemma slp_born_recursive_branches_cutoff_recurrence:
  fixes cutoff q :: slp_scalar_field
  assumes cutoff_identity: "\<And>x. cutoff x * q x = q x"
  shows
    "slp_left_recursive_branch 0 tau c cutoff q (\<lambda>_. 1) =
      slp_cauchy_transform SLP_Partial_Inverse
        (slp_oscillatory_modulation tau c cutoff)"
    "slp_right_recursive_branch 0 tau c cutoff q (\<lambda>_. 1) =
      slp_cauchy_transform SLP_Dbar_Inverse
        (slp_oscillatory_modulation tau c cutoff)"
    "slp_left_recursive_branch (Suc n) tau c cutoff q (\<lambda>_. 1) =
      slp_cauchy_transform SLP_Partial_Inverse
        (slp_oscillatory_modulation tau c
          (\<lambda>y. cutoff y * slp_cauchy_transform SLP_Dbar_Inverse
            (slp_oscillatory_modulation (-tau) c
              (\<lambda>x. cutoff x * (q x *
                slp_left_recursive_branch n tau c cutoff q (\<lambda>_. 1) x))) y))"
    "slp_right_recursive_branch (Suc n) tau c cutoff q (\<lambda>_. 1) =
      slp_cauchy_transform SLP_Dbar_Inverse
        (slp_oscillatory_modulation tau c
          (\<lambda>y. cutoff y * slp_cauchy_transform SLP_Partial_Inverse
            (slp_oscillatory_modulation (-tau) c
              (\<lambda>x. cutoff x * (q x *
                slp_right_recursive_branch n tau c cutoff q (\<lambda>_. 1) x))) y))"
proof -
  have cutoff_product: "(\<lambda>x. cutoff x * (q x * g x)) = (\<lambda>x. q x * g x)"
    for g :: slp_scalar_field
    by (rule ext) (simp only: mult.assoc[symmetric] cutoff_identity)
  show "slp_left_recursive_branch 0 tau c cutoff q (\<lambda>_. 1) =
      slp_cauchy_transform SLP_Partial_Inverse
        (slp_oscillatory_modulation tau c cutoff)"
    by (simp add: slp_partial_psi_inverse_def)
  show "slp_right_recursive_branch 0 tau c cutoff q (\<lambda>_. 1) =
      slp_cauchy_transform SLP_Dbar_Inverse
        (slp_oscillatory_modulation tau c cutoff)"
    by (simp add: slp_dbar_psi_inverse_def)
  show "slp_left_recursive_branch (Suc n) tau c cutoff q (\<lambda>_. 1) =
      slp_cauchy_transform SLP_Partial_Inverse
        (slp_oscillatory_modulation tau c
          (\<lambda>y. cutoff y * slp_cauchy_transform SLP_Dbar_Inverse
            (slp_oscillatory_modulation (-tau) c
              (\<lambda>x. cutoff x * (q x *
                slp_left_recursive_branch n tau c cutoff q (\<lambda>_. 1) x))) y))"
    by (simp add: slp_partial_psi_inverse_def slp_dbar_psi_inverse_def cutoff_product)
  show "slp_right_recursive_branch (Suc n) tau c cutoff q (\<lambda>_. 1) =
      slp_cauchy_transform SLP_Dbar_Inverse
        (slp_oscillatory_modulation tau c
          (\<lambda>y. cutoff y * slp_cauchy_transform SLP_Partial_Inverse
            (slp_oscillatory_modulation (-tau) c
              (\<lambda>x. cutoff x * (q x *
                slp_right_recursive_branch n tau c cutoff q (\<lambda>_. 1) x))) y))"
    by (simp add: slp_partial_psi_inverse_def slp_dbar_psi_inverse_def cutoff_product)
qed

section \<open>A common positive-order gain for the actual left and right branches\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_positive_born_branches_uniform_gain:
  fixes cutoff :: slp_scalar_field and Y :: "slp_point set" and m :: nat
  assumes p_lower: "1 < p" and p_upper: "p < 2"
    and b_lower: "2 * slp_holder_conjugate p < b"
    and target_bounded: "bounded Y" and order_positive: "0 < m"
    and cutoff_test: "slp_test_function_on Y cutoff"
  shows "\<exists>C::real. 0 < C \<and> (\<forall>tau c q. 2 \<le> tau \<and> aim_complex_lp_on_plane p q \<and>
      (\<forall>x. cutoff x * q x = q x) \<longrightarrow> slp_left_recursive_branch m tau c cutoff q (\<lambda>_. 1) \<in> borel_measurable lborel \<and>
      slp_right_recursive_branch m tau c cutoff q (\<lambda>_. 1) \<in> borel_measurable lborel \<and>
      (\<forall>z\<in>Y. norm (slp_left_recursive_branch m tau c cutoff q (\<lambda>_. 1) z) \<le> C * inverse (sqrt tau) * (aim_complex_lp_norm p q)^m \<and>
        norm (slp_right_recursive_branch m tau c cutoff q (\<lambda>_. 1) z) \<le> C * inverse (sqrt tau) * (aim_complex_lp_norm p q)^m))"
proof -
  have cutoff_tests: "\<forall>i<m. slp_test_function_on Y cutoff"
    by (intro allI impI, rule cutoff_test)
  obtain H :: real where H_data: "0 < H \<and> (\<forall>tau c f q epsilon0 epsilon1 epsilon2 terminal outer inner Pi.
      2 \<le> tau \<and> slp_test_function_on Y f \<and>
      aim_complex_lp_on_plane p q \<and>
      epsilon0 \<in> {-1, 1} \<and>
      (\<forall>i<m. epsilon1 i \<in> {-1, 1} \<and> epsilon2 i \<in> {-1, 1}) \<and>
      Pi 0 = slp_cauchy_transform terminal
        (slp_oscillatory_modulation (epsilon0 * tau) c f) \<and> (\<forall>i<m. Pi (Suc i) =
        slp_cauchy_transform (outer i)
          (slp_oscillatory_modulation (epsilon1 i * tau) c
            (\<lambda>y. cutoff y * slp_cauchy_transform (inner i)
              (slp_oscillatory_modulation (epsilon2 i * tau) c
                (\<lambda>x. cutoff x * (q x * Pi i x))) y))) \<longrightarrow> Pi m \<in> borel_measurable lborel \<and>
      (\<forall>z\<in>Y. norm (Pi m z) \<le> H * inverse (sqrt tau) *
        slp_w1p_norm_on (slp_hls_source_exponent b) UNIV f (slp_classical_gradient f) *
        (aim_complex_lp_norm p q) ^ m))"
    using slp_uniform_reverse_branch_constant_coefficient_gain[OF p_lower
      p_upper b_lower target_bounded order_positive cutoff_tests cutoff_tests] ..
  have H_positive: "0 < H" by (rule conjunct1[OF H_data])
  note H_all = H_data[THEN conjunct2]
  let ?W = "slp_w1p_norm_on (slp_hls_source_exponent b) UNIV cutoff (slp_classical_gradient cutoff)"
  let ?K = "H * (abs ?W + 1)"
  have abs_nonnegative: "0 \<le> abs ?W" by simp
  have factor_positive: "0 < abs ?W + 1"
    using abs_nonnegative by linarith
  have K_positive: "0 < ?K"
    by (rule mult_pos_pos[OF H_positive factor_positive])
  have W_bound: "?W \<le> abs ?W + 1"
    using abs_ge_self[of ?W] by linarith
  have branch_gain:
      "Pi m \<in> borel_measurable lborel \<and>
        (\<forall>z\<in>Y. norm (Pi m z) \<le>
          ?K * inverse (sqrt tau) * (aim_complex_lp_norm p q)^m)"
    if tau_lower: "2 \<le> tau"
      and q_lp: "aim_complex_lp_on_plane p q"
      and zero: "Pi 0 = slp_cauchy_transform terminal
        (slp_oscillatory_modulation tau c cutoff)"
      and recursion: "\<forall>i<m. Pi (Suc i) =
        slp_cauchy_transform outer
          (slp_oscillatory_modulation tau c
            (\<lambda>y. cutoff y * slp_cauchy_transform inner
              (slp_oscillatory_modulation (-tau) c
                (\<lambda>x. cutoff x * (q x * Pi i x))) y))"
    for tau :: real and c :: slp_point and q :: slp_scalar_field
      and terminal outer inner :: slp_cauchy_orientation
      and Pi :: "nat \<Rightarrow> slp_scalar_field"
  proof -
    have hypotheses: "2 \<le> tau \<and> slp_test_function_on Y cutoff \<and>
      aim_complex_lp_on_plane p q \<and> (1::real) \<in> {-1,1} \<and>
      (\<forall>i<m. (1::real) \<in> {-1,1} \<and> (-1::real) \<in> {-1,1}) \<and>
      Pi 0 = slp_cauchy_transform terminal
        (slp_oscillatory_modulation (1 * tau) c cutoff) \<and>
      (\<forall>i<m. Pi (Suc i) =
        slp_cauchy_transform outer
          (slp_oscillatory_modulation (1 * tau) c
            (\<lambda>y. cutoff y * slp_cauchy_transform inner
              (slp_oscillatory_modulation ((-1) * tau) c
                (\<lambda>x. cutoff x * (q x * Pi i x))) y)))"
      using tau_lower cutoff_test q_lp zero recursion by simp
    have application: "Pi m \<in> borel_measurable lborel \<and>
        (\<forall>z\<in>Y. norm (Pi m z) \<le>
          H * inverse (sqrt tau) * ?W * (aim_complex_lp_norm p q)^m)"
      by (rule H_all[rule_format, OF hypotheses])
    have scale_nonnegative: "0 \<le> H * inverse (sqrt tau)"
      using H_positive tau_lower by (intro mult_nonneg_nonneg) auto
    have power_nonnegative: "0 \<le> (aim_complex_lp_norm p q)^m"
      by (rule zero_le_power) (simp add: aim_complex_lp_norm_def)
    have constant_bound:
        "H * inverse (sqrt tau) * ?W * (aim_complex_lp_norm p q)^m \<le>
          ?K * inverse (sqrt tau) * (aim_complex_lp_norm p q)^m"
    proof -
      have first: "H * inverse (sqrt tau) * ?W \<le>
          H * inverse (sqrt tau) * (abs ?W + 1)"
        by (rule mult_left_mono[OF W_bound scale_nonnegative])
      have second:
          "H * inverse (sqrt tau) * ?W * (aim_complex_lp_norm p q)^m \<le>
            H * inverse (sqrt tau) * (abs ?W + 1) * (aim_complex_lp_norm p q)^m"
        by (rule mult_right_mono[OF first power_nonnegative])
      show ?thesis using second by (simp only: mult.assoc mult.left_commute mult.commute)
    qed
    show ?thesis
    proof (rule conjI[OF application[THEN conjunct1]], intro ballI)
      fix z assume z_in: "z \<in> Y"
      have bound: "norm (Pi m z) \<le>
          H * inverse (sqrt tau) * ?W * (aim_complex_lp_norm p q)^m"
        by (rule application[THEN conjunct2, rule_format, OF z_in])
      show "norm (Pi m z) \<le>
          ?K * inverse (sqrt tau) * (aim_complex_lp_norm p q)^m"
        by (rule order_trans[OF bound constant_bound])
    qed
  qed
  have all: "(\<forall>tau c q. 2 \<le> tau \<and> aim_complex_lp_on_plane p q \<and>
      (\<forall>x. cutoff x * q x = q x) \<longrightarrow> slp_left_recursive_branch m tau c cutoff q (\<lambda>_. 1) \<in> borel_measurable lborel \<and>
      slp_right_recursive_branch m tau c cutoff q (\<lambda>_. 1) \<in> borel_measurable lborel \<and>
      (\<forall>z\<in>Y. norm (slp_left_recursive_branch m tau c cutoff q (\<lambda>_. 1) z) \<le> ?K * inverse (sqrt tau) * (aim_complex_lp_norm p q)^m \<and>
        norm (slp_right_recursive_branch m tau c cutoff q (\<lambda>_. 1) z) \<le> ?K * inverse (sqrt tau) * (aim_complex_lp_norm p q)^m))"
  proof (intro allI impI)
    fix tau :: real and c :: slp_point and q :: slp_scalar_field
    assume hypotheses: "2 \<le> tau \<and> aim_complex_lp_on_plane p q \<and>
      (\<forall>x. cutoff x * q x = q x)"
    have tau_lower: "2 \<le> tau" by (rule conjunct1[OF hypotheses])
    note rest = hypotheses[THEN conjunct2]
    have q_lp: "aim_complex_lp_on_plane p q" by (rule conjunct1[OF rest])
    have cutoff_identity: "cutoff x * q x = q x" for x
      by (rule rest[THEN conjunct2, rule_format])
    have left_zero: "slp_left_recursive_branch 0 tau c cutoff q (\<lambda>_. 1) =
        slp_cauchy_transform SLP_Partial_Inverse
          (slp_oscillatory_modulation tau c cutoff)"
      by (rule slp_born_recursive_branches_cutoff_recurrence(1)[OF cutoff_identity])
    have right_zero: "slp_right_recursive_branch 0 tau c cutoff q (\<lambda>_. 1) =
        slp_cauchy_transform SLP_Dbar_Inverse
          (slp_oscillatory_modulation tau c cutoff)"
      by (rule slp_born_recursive_branches_cutoff_recurrence(2)[OF cutoff_identity])
    have left_recursion: "\<forall>i<m.
        slp_left_recursive_branch (Suc i) tau c cutoff q (\<lambda>_. 1) =
          slp_cauchy_transform SLP_Partial_Inverse
            (slp_oscillatory_modulation tau c
              (\<lambda>y. cutoff y * slp_cauchy_transform SLP_Dbar_Inverse
                (slp_oscillatory_modulation (-tau) c
                  (\<lambda>x. cutoff x * (q x *
                    slp_left_recursive_branch i tau c cutoff q (\<lambda>_. 1) x))) y))"
      by (intro allI impI, rule slp_born_recursive_branches_cutoff_recurrence(3)[OF cutoff_identity])
    have right_recursion: "\<forall>i<m.
        slp_right_recursive_branch (Suc i) tau c cutoff q (\<lambda>_. 1) =
          slp_cauchy_transform SLP_Dbar_Inverse
            (slp_oscillatory_modulation tau c
              (\<lambda>y. cutoff y * slp_cauchy_transform SLP_Partial_Inverse
                (slp_oscillatory_modulation (-tau) c
                  (\<lambda>x. cutoff x * (q x *
                    slp_right_recursive_branch i tau c cutoff q (\<lambda>_. 1) x))) y))"
      by (intro allI impI, rule slp_born_recursive_branches_cutoff_recurrence(4)[OF cutoff_identity])
    have left_gain: "slp_left_recursive_branch m tau c cutoff q (\<lambda>_. 1) \<in> borel_measurable lborel \<and>
        (\<forall>z\<in>Y. norm (slp_left_recursive_branch m tau c cutoff q (\<lambda>_. 1) z) \<le>
          ?K * inverse (sqrt tau) * (aim_complex_lp_norm p q)^m)"
      by (rule branch_gain[OF tau_lower q_lp left_zero left_recursion])
    have right_gain: "slp_right_recursive_branch m tau c cutoff q (\<lambda>_. 1) \<in> borel_measurable lborel \<and>
        (\<forall>z\<in>Y. norm (slp_right_recursive_branch m tau c cutoff q (\<lambda>_. 1) z) \<le>
          ?K * inverse (sqrt tau) * (aim_complex_lp_norm p q)^m)"
      by (rule branch_gain[OF tau_lower q_lp right_zero right_recursion])
    show "slp_left_recursive_branch m tau c cutoff q (\<lambda>_. 1) \<in> borel_measurable lborel \<and>
      slp_right_recursive_branch m tau c cutoff q (\<lambda>_. 1) \<in> borel_measurable lborel \<and>
      (\<forall>z\<in>Y. norm (slp_left_recursive_branch m tau c cutoff q (\<lambda>_. 1) z) \<le> ?K * inverse (sqrt tau) * (aim_complex_lp_norm p q)^m \<and>
        norm (slp_right_recursive_branch m tau c cutoff q (\<lambda>_. 1) z) \<le> ?K * inverse (sqrt tau) * (aim_complex_lp_norm p q)^m)"
    proof (rule conjI[OF left_gain[THEN conjunct1]],
        rule conjI[OF right_gain[THEN conjunct1]], intro ballI)
      fix z assume z_in: "z \<in> Y"
      show "norm (slp_left_recursive_branch m tau c cutoff q (\<lambda>_. 1) z) \<le>
          ?K * inverse (sqrt tau) * (aim_complex_lp_norm p q)^m \<and>
        norm (slp_right_recursive_branch m tau c cutoff q (\<lambda>_. 1) z) \<le>
          ?K * inverse (sqrt tau) * (aim_complex_lp_norm p q)^m"
        by (rule conjI[OF left_gain[THEN conjunct2, rule_format, OF z_in]
              right_gain[THEN conjunct2, rule_format, OF z_in]])
    qed
  qed
  show ?thesis by (rule exI[of _ ?K], rule conjI[OF K_positive all])
qed

end

end

