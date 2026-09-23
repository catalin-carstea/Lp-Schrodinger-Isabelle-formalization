theory Inverse_Schrodinger_Lp_Right_Initial_Correction_Lpstar
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Right_Initial_Correction_Power_Loss"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Nested_Coefficient_Product_High_Endpoint"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Literal right initial-correction secondary norm\<close>

context slp_cauchy_local_w1s
begin

theorem slp_right_neumann_base_lpstar_inverse_sqrt_bound:
  fixes p A0 B0 B1 :: real
    and X Y :: "slp_point set"
    and cutoff :: slp_scalar_field
  assumes riesz_hls: "aim_planar_riesz_hls_claim"
    and cauchy_test_left_inverse:
      "aim_planar_cauchy_test_left_inverse_claim"
    and evans_density: "evans_compact_support_w1p_zero_density_claim"
    and exponent_lower: "1 < p"
    and exponent_upper: "p < 2"
    and X_open: "open X"
    and X_bounded: "bounded X"
    and Y_bounded: "bounded Y"
    and cutoff_test: "slp_test_function_on X cutoff"
    and cutoff_bound:
      "\<And>x. x \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm (cutoff x) \<le> A0"
    and cutoff_derivative_zero_bound:
      "\<And>x. x \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm
          (slp_complex_partial_derivative cutoff 0 x) \<le> B0"
    and cutoff_derivative_one_bound:
      "\<And>x. x \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm
          (slp_complex_partial_derivative cutoff 1 x) \<le> B1"
    and A0_nonnegative: "0 \<le> A0"
    and B0_nonnegative: "0 \<le> B0"
    and B1_nonnegative: "0 \<le> B1"
  shows
    "\<exists>C::real. 0 < C \<and>
      (\<forall>tau c coefficient.
        2 \<le> tau \<and>
        aim_complex_lp_on_plane p coefficient \<and>
        {x. coefficient x \<noteq> 0} \<subseteq> Y
        \<longrightarrow>
        slp_complex_lp_on (aim_hls_target_exponent p) X
          (slp_right_neumann_base tau c cutoff coefficient
            SLP_Partial_Inverse)
        \<and>
        slp_complex_lp_norm_on (aim_hls_target_exponent p) X
          (slp_right_neumann_base tau c cutoff coefficient
            SLP_Partial_Inverse)
          \<le> C * inverse (sqrt tau) *
            (aim_complex_lp_norm p coefficient +
              Real_Vector_Spaces.norm
                (slp_partial_inverse coefficient c)))"
proof -
  have exponent_one_le: "1 \<le> p"
    using exponent_lower by linarith
  have target_positive: "0 < aim_hls_target_exponent p"
    using slp_qstar_exponent_relations(1)[OF exponent_lower exponent_upper]
    by linarith
  have X_measurable: "X \<in> sets lborel"
    using X_open by simp
  have cutoff_zero:
      "slp_w1p_zero_pair_on p X cutoff (slp_classical_gradient cutoff)"
    by (rule slp_test_function_w1p_zero_pair[OF _ cutoff_test])
       (use exponent_lower in linarith)
  have cutoff_pair:
      "slp_w1p_pair_on p X cutoff (slp_classical_gradient cutoff)"
    using cutoff_zero unfolding slp_w1p_zero_pair_on_def by blast
  have cutoff_support: "closure {x. cutoff x \<noteq> 0} \<subseteq> X"
    using cutoff_test unfolding slp_test_function_on_def by blast
  have cutoff_compact: "compact (closure {x. cutoff x \<noteq> 0})"
    using cutoff_test unfolding slp_test_function_on_def by blast
  have cutoff_smooth: "smooth_on UNIV cutoff"
    using cutoff_test unfolding slp_test_function_on_def by blast
  let ?W0 =
    "slp_w1p_norm_on p X cutoff (slp_classical_gradient cutoff)"
  let ?S = "36 * ?W0"
  have W0_nonnegative: "0 \<le> ?W0"
    unfolding slp_w1p_norm_on_def by simp
  have S_nonnegative: "0 \<le> ?S"
    using W0_nonnegative by simp

  obtain K :: real where K_positive: "0 < K"
    and inner_bound:
      "\<forall>tau c coefficient multiplier M.
        aim_complex_lp_on_plane p coefficient \<and>
        {x. coefficient x \<noteq> 0} \<subseteq> Y \<and>
        multiplier \<in> borel_measurable lborel \<and>
        (AE x in lborel. norm (multiplier x) \<le> M) \<and>
        0 \<le> M
        \<longrightarrow>
        slp_w1p_norm_on p X
            (\<lambda>x. cutoff x *
              slp_dbar_psi_inverse tau c
                (\<lambda>y. coefficient y * multiplier y) x)
            (\<lambda>x. \<chi> i.
              cutoff x *
                slp_dbar_inverse_gradient
                  (slp_oscillatory_modulation (- tau) c
                    (\<lambda>y. coefficient y * multiplier y)) x $ i +
              slp_dbar_psi_inverse tau c
                  (\<lambda>y. coefficient y * multiplier y) x *
                slp_complex_partial_derivative cutoff i x)
          \<le> K * M * aim_complex_lp_norm p coefficient
        \<and>
        slp_w1p_norm_on p X
            (\<lambda>x. cutoff x *
              slp_partial_psi_inverse (- tau) c
                (\<lambda>y. coefficient y * multiplier y) x)
            (\<lambda>x. \<chi> i.
              cutoff x *
                slp_partial_inverse_gradient
                  (slp_oscillatory_modulation (- tau) c
                    (\<lambda>y. coefficient y * multiplier y)) x $ i +
              slp_partial_psi_inverse (- tau) c
                  (\<lambda>y. coefficient y * multiplier y) x *
                slp_complex_partial_derivative cutoff i x)
          \<le> K * M * aim_complex_lp_norm p coefficient"
    using slp_both_inner_cauchy_coefficient_product_cutoff_w1p_norm_bounds[
      OF exponent_lower X_open X_bounded Y_bounded cutoff_test cutoff_bound
        cutoff_derivative_zero_bound cutoff_derivative_one_bound
        A0_nonnegative B0_nonnegative B1_nonnegative]
    by blast
  have outer_context: "slp_qstar_centered_smooth_far_hls_context"
    using aim_planar_hls_cauchy riesz_hls cauchy_test_left_inverse
    by unfold_locales
  obtain H :: real where H_positive: "0 < H"
    and outer_gain:
      "\<And>tau c f Df epsilon orientation.
        2 \<le> tau \<Longrightarrow>
        slp_w1p_zero_pair_on p X f Df \<Longrightarrow>
        epsilon \<in> {-1, 1} \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent p)
          (slp_cauchy_transform orientation
            (slp_oscillatory_modulation (epsilon * tau) c
              (slp_restrict_field X f)))
        \<and>
        aim_complex_lp_norm (aim_hls_target_exponent p)
          (slp_cauchy_transform orientation
            (slp_oscillatory_modulation (epsilon * tau) c
              (slp_restrict_field X f)))
          \<le> H * inverse (sqrt tau) * slp_w1p_norm_on p X f Df"
    using slp_qstar_centered_smooth_far_hls_context.slp_w1p_zero_pair_all_orientation_gain[
      OF outer_context exponent_lower exponent_upper X_bounded]
    by blast
  let ?C = "48 * H * (K + ?S)"
  have KS_positive: "0 < K + ?S"
    using K_positive S_nonnegative by linarith
  have C_positive: "0 < ?C"
    by (rule mult_pos_pos[OF mult_pos_pos[OF _ H_positive] KS_positive])
       simp

  show ?thesis
  proof (rule exI[of _ ?C], rule conjI[OF C_positive])
    show "\<forall>tau c coefficient.
        2 \<le> tau \<and>
        aim_complex_lp_on_plane p coefficient \<and>
        {x. coefficient x \<noteq> 0} \<subseteq> Y
        \<longrightarrow>
        slp_complex_lp_on (aim_hls_target_exponent p) X
          (slp_right_neumann_base tau c cutoff coefficient
            SLP_Partial_Inverse)
        \<and>
        slp_complex_lp_norm_on (aim_hls_target_exponent p) X
          (slp_right_neumann_base tau c cutoff coefficient
            SLP_Partial_Inverse)
          \<le> ?C * inverse (sqrt tau) *
            (aim_complex_lp_norm p coefficient +
              Real_Vector_Spaces.norm
                (slp_partial_inverse coefficient c))"
    proof (intro allI impI)
      fix tau :: real and c :: slp_point
        and coefficient :: slp_scalar_field
      assume data:
        "2 \<le> tau \<and>
          aim_complex_lp_on_plane p coefficient \<and>
          {x. coefficient x \<noteq> 0} \<subseteq> Y"
      have tau_lower: "2 \<le> tau" using data by blast
      have coefficient_lp: "aim_complex_lp_on_plane p coefficient"
        using data by blast
      have coefficient_carrier: "{x. coefficient x \<noteq> 0} \<subseteq> Y"
        using data by blast
      have coefficient_support: "bounded {x. coefficient x \<noteq> 0}"
        by (rule bounded_subset[OF Y_bounded coefficient_carrier])
      let ?one = "\<lambda>_ :: slp_point. (1 :: complex)"
      let ?a = "\<lambda>_ :: slp_point. slp_partial_inverse coefficient c"
      let ?A = "slp_partial_inverse coefficient"
      let ?DA = "slp_partial_inverse_gradient coefficient"
      let ?uQ = "\<lambda>x. cutoff x * ?A x"
      let ?DuQ = "\<lambda>x. \<chi> i.
        cutoff x * ?DA x $ i +
          ?A x * slp_complex_partial_derivative cutoff i x"
      let ?uC = "\<lambda>x. ?a x * cutoff x"
      let ?DuC = "\<lambda>x. \<chi> i.
        ?a x * slp_classical_gradient cutoff x $ i +
          cutoff x * slp_complex_partial_derivative ?a i x"
      let ?u = "\<lambda>x. ?uQ x - ?uC x"
      let ?Du = "\<lambda>x. ?DuQ x - ?DuC x"
      let ?WQ = "slp_w1p_norm_on p X ?uQ ?DuQ"
      let ?WC = "slp_w1p_norm_on p X ?uC ?DuC"
      let ?W = "slp_w1p_norm_on p X ?u ?Du"
      let ?qnorm = "aim_complex_lp_norm p coefficient"
      let ?anorm = "Real_Vector_Spaces.norm (?A c)"
      let ?T =
        "slp_right_neumann_base tau c cutoff coefficient SLP_Partial_Inverse"

      have zero_modulation:
          "slp_oscillatory_modulation 0 c coefficient = coefficient"
        by (rule ext)
           (simp add: slp_oscillatory_modulation_def slp_center_kernel_def)
      have zero_partial:
          "slp_partial_psi_inverse 0 c coefficient = ?A"
        unfolding slp_partial_psi_inverse_def
        by (simp add: zero_modulation)
      note inner_zero_pairs = slp_both_inner_cauchy_mult_test_w1p_zero_pairs[
        where s=p and tau=0 and X=X and c=c and source=coefficient
          and cutoff=cutoff,
        OF evans_density exponent_lower X_open X_bounded coefficient_lp
          coefficient_support cutoff_test]
      have q_zero: "slp_w1p_zero_pair_on p X ?uQ ?DuQ"
        using conjunct2[OF inner_zero_pairs]
        by (simp add: zero_partial zero_modulation)
      have q_pair: "slp_w1p_pair_on p X ?uQ ?DuQ"
        using q_zero unfolding slp_w1p_zero_pair_on_def by blast

      have a_smooth: "smooth_on UNIV ?a"
        by (rule smooth_on_const)
      have a_value_bound:
          "\<And>x. x \<in> X \<Longrightarrow>
            Real_Vector_Spaces.norm (?a x) \<le> ?anorm"
        by simp
      have a_derivative_zero:
          "\<And>x. x \<in> X \<Longrightarrow>
            Real_Vector_Spaces.norm
              (slp_complex_partial_derivative ?a 0 x) \<le> 0"
        by (simp add: slp_complex_partial_derivative_def)
      have a_derivative_one:
          "\<And>x. x \<in> X \<Longrightarrow>
            Real_Vector_Spaces.norm
              (slp_complex_partial_derivative ?a 1 x) \<le> 0"
        by (simp add: slp_complex_partial_derivative_def)
      have anorm_nonnegative: "0 \<le> ?anorm" by simp
      have zero_nonnegative: "0 \<le> (0::real)" by simp
      have c_zero: "slp_w1p_zero_pair_on p X ?uC ?DuC"
        by (rule slp_w1p_zero_pair_on_mult_smooth_bounded[
              OF exponent_one_le X_measurable X_bounded cutoff_zero a_smooth
                a_value_bound a_derivative_zero a_derivative_one
                anorm_nonnegative zero_nonnegative zero_nonnegative])
      have c_pair: "slp_w1p_pair_on p X ?uC ?DuC"
        using c_zero unfolding slp_w1p_zero_pair_on_def by blast
      have diff_pair: "slp_w1p_pair_on p X ?u ?Du"
        by (rule slp_w1p_pair_on_diff[OF exponent_one_le q_pair c_pair])

      have compact_zero:
          "\<forall>x \<in> X - closure {x. cutoff x \<noteq> 0}.
            ?u x = 0 \<and> (\<forall>i. ?Du x $ i = 0)"
      proof (intro ballI conjI allI)
        fix x :: slp_point and i :: 2
        assume outside: "x \<in> X - closure {x. cutoff x \<noteq> 0}"
        have x_not_support: "x \<notin> closure {x. cutoff x \<noteq> 0}"
          using outside by blast
        have cutoff_zero_at: "cutoff x = 0"
          using x_not_support closure_subset by blast
        have derivative_support:
            "closure {y. slp_complex_partial_derivative cutoff i y \<noteq> 0}
              \<subseteq> closure {x. cutoff x \<noteq> 0}"
          by (rule slp_complex_partial_derivative_support_subset[
                OF cutoff_smooth])
        have derivative_zero_at:
            "slp_complex_partial_derivative cutoff i x = 0"
          using x_not_support derivative_support closure_subset by blast
        show "?u x = 0"
          using cutoff_zero_at by simp
        show "?Du x $ i = 0"
          using cutoff_zero_at derivative_zero_at
          by (simp add: slp_classical_gradient_def)
      qed
      have combined_zero: "slp_w1p_zero_pair_on p X ?u ?Du"
        using evans_density exponent_one_le X_open cutoff_compact
          cutoff_support diff_pair compact_zero
        unfolding evans_compact_support_w1p_zero_density_claim_def
        by blast

      have q_graph: "?WQ \<le> K * ?qnorm"
      proof -
        note raw = inner_bound[rule_format,
          where tau=0 and c=c and coefficient=coefficient
            and multiplier="?one" and M=1]
        have inner_premises:
            "aim_complex_lp_on_plane p coefficient \<and>
              {x. coefficient x \<noteq> 0} \<subseteq> Y \<and>
              ?one \<in> borel_measurable lborel \<and>
              (AE x in lborel. norm (?one x) \<le> 1) \<and>
              0 \<le> (1::real)"
          using coefficient_lp coefficient_carrier by simp
        note first = conjunct2[OF raw[OF inner_premises]]
        show ?thesis
          using first by (simp add: zero_partial zero_modulation)
      qed
      have c_graph: "?WC \<le> ?S * ?anorm"
      proof -
        note raw = slp_w1p_norm_on_mult_smooth_bounded[
          OF exponent_one_le X_measurable X_bounded cutoff_pair a_smooth
            a_value_bound a_derivative_zero a_derivative_one
            anorm_nonnegative zero_nonnegative zero_nonnegative]
        show ?thesis
          using raw by (simp add: algebra_simps)
      qed
      have coarse:
          "?W \<le> 48 * (?WQ + ?WC)"
        by (rule slp_w1p_norm_on_diff_coarse_triangle[
              OF exponent_one_le q_pair c_pair])
      have graph_sum:
          "?WQ + ?WC \<le> K * ?qnorm + ?S * ?anorm"
        by (rule add_mono[OF q_graph c_graph])
      have W_bound:
          "?W \<le> 48 * (K * ?qnorm + ?S * ?anorm)"
        by (rule order_trans[OF coarse mult_left_mono[OF graph_sum]]) simp

      have restrict_u: "slp_restrict_field X ?u = ?u"
      proof (rule ext)
        fix x
        show "slp_restrict_field X ?u x = ?u x"
        proof (cases "x \<in> X")
          case True
          then show ?thesis by (simp add: slp_restrict_field_def)
        next
          case False
          have cutoff_zero_at: "cutoff x = 0"
          proof (rule ccontr)
            assume "cutoff x \<noteq> 0"
            then have "x \<in> closure {x. cutoff x \<noteq> 0}"
              unfolding closure_def by simp
            with cutoff_support False show False by blast
          qed
          show ?thesis using False cutoff_zero_at
            by (simp add: slp_restrict_field_def)
        qed
      qed
      have source_presentation:
          "?u = (\<lambda>x. cutoff x * (?A x - ?A c))"
        by (rule ext) (simp add: algebra_simps)
      have restricted_source_presentation:
          "slp_restrict_field X ?u =
            (\<lambda>x. cutoff x * (?A x - ?A c))"
        by (rule trans[OF restrict_u source_presentation])
      have output_presentation:
          "slp_dbar_psi_inverse (- tau) c (slp_restrict_field X ?u) = ?T"
        by (simp only: restricted_source_presentation
              slp_right_neumann_base_def)

      have global:
          "aim_complex_lp_on_plane (aim_hls_target_exponent p) ?T \<and>
            aim_complex_lp_norm (aim_hls_target_exponent p) ?T
              \<le> H * inverse (sqrt tau) * ?W"
        using outer_gain[
          where tau=tau and c=c and f="?u" and Df="?Du" and epsilon=1
            and orientation=SLP_Dbar_Inverse,
          OF tau_lower combined_zero]
        by (simp add: slp_dbar_psi_inverse_def
              restricted_source_presentation slp_right_neumann_base_def)
      have local_lp:
          "slp_complex_lp_on (aim_hls_target_exponent p) X ?T"
        by (rule aim_complex_lp_on_plane_restrict[
              OF target_positive X_measurable conjunct1[OF global]])
      have local_le:
          "slp_complex_lp_norm_on (aim_hls_target_exponent p) X ?T \<le>
            aim_complex_lp_norm (aim_hls_target_exponent p) ?T"
        by (rule slp_complex_lp_norm_on_le[
              OF target_positive X_measurable conjunct1[OF global]])
      have qnorm_nonnegative: "0 \<le> ?qnorm"
        unfolding aim_complex_lp_norm_def by (rule powr_ge_zero)
      have rate_nonnegative: "0 \<le> inverse (sqrt tau)"
        using tau_lower by simp
      have Hrate_nonnegative: "0 \<le> H * inverse (sqrt tau)"
        by (rule mult_nonneg_nonneg[OF less_imp_le[OF H_positive]
              rate_nonnegative])
      have scaled_W:
          "H * inverse (sqrt tau) * ?W \<le>
            H * inverse (sqrt tau) *
              (48 * (K * ?qnorm + ?S * ?anorm))"
        by (rule mult_left_mono[OF W_bound Hrate_nonnegative])
      have coefficient_enlarged:
          "K * ?qnorm + ?S * ?anorm \<le>
            (K + ?S) * (?qnorm + ?anorm)"
      proof -
        have cross_nonnegative:
            "0 \<le> K * ?anorm + ?S * ?qnorm"
          by (intro add_nonneg_nonneg mult_nonneg_nonneg)
             (use K_positive S_nonnegative qnorm_nonnegative
                anorm_nonnegative in auto)
        have expansion:
            "(K + ?S) * (?qnorm + ?anorm) =
              (K * ?qnorm + ?S * ?anorm) +
                (K * ?anorm + ?S * ?qnorm)"
          by (simp add: algebra_simps)
        show ?thesis
          unfolding expansion using cross_nonnegative by simp
      qed
      have scaled_coefficient:
          "H * inverse (sqrt tau) *
              (48 * (K * ?qnorm + ?S * ?anorm))
            \<le>
            H * inverse (sqrt tau) *
              (48 * ((K + ?S) * (?qnorm + ?anorm)))"
      proof (rule mult_left_mono[OF _ Hrate_nonnegative])
        show "48 * (K * ?qnorm + ?S * ?anorm) \<le>
            48 * ((K + ?S) * (?qnorm + ?anorm))"
          by (rule mult_left_mono[OF coefficient_enlarged]) simp
      qed
      have final_identity:
          "H * inverse (sqrt tau) *
              (48 * ((K + ?S) * (?qnorm + ?anorm))) =
            ?C * inverse (sqrt tau) * (?qnorm + ?anorm)"
        by (simp add: algebra_simps)
      have after_global:
          "slp_complex_lp_norm_on (aim_hls_target_exponent p) X ?T
            \<le> H * inverse (sqrt tau) * ?W"
        by (rule order_trans[OF local_le conjunct2[OF global]])
      have after_W:
          "slp_complex_lp_norm_on (aim_hls_target_exponent p) X ?T
            \<le> H * inverse (sqrt tau) *
              (48 * (K * ?qnorm + ?S * ?anorm))"
        by (rule order_trans[OF after_global scaled_W])
      have pre_final:
          "slp_complex_lp_norm_on (aim_hls_target_exponent p) X ?T
            \<le> H * inverse (sqrt tau) *
              (48 * ((K + ?S) * (?qnorm + ?anorm)))"
        by (rule order_trans[OF after_W scaled_coefficient])
      have final_bound:
          "slp_complex_lp_norm_on (aim_hls_target_exponent p) X ?T
            \<le> ?C * inverse (sqrt tau) * (?qnorm + ?anorm)"
        using pre_final by (simp only: final_identity)
      show
          "slp_complex_lp_on (aim_hls_target_exponent p) X ?T \<and>
            slp_complex_lp_norm_on (aim_hls_target_exponent p) X ?T
              \<le> ?C * inverse (sqrt tau) * (?qnorm + ?anorm)"
        by (rule conjI[OF local_lp final_bound])
    qed
  qed
qed

end

end
