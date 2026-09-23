theory Inverse_Schrodinger_Lp_Nested_Coefficient_Product_High_Endpoint
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Inner_Cauchy_Coefficient_Product_Cutoff_Norm"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_All_Orientation_Gain"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Actual nested coefficient-product high endpoint\<close>

context slp_cauchy_local_w1s
begin

theorem slp_both_nested_coefficient_product_lpstar_inverse_sqrt_bounds:
  fixes p A B0 B1 :: real
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
        Real_Vector_Spaces.norm (cutoff x) \<le> A"
    and cutoff_derivative_zero_bound:
      "\<And>x. x \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm
          (slp_complex_partial_derivative cutoff 0 x) \<le> B0"
    and cutoff_derivative_one_bound:
      "\<And>x. x \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm
          (slp_complex_partial_derivative cutoff 1 x) \<le> B1"
    and A_nonnegative: "0 \<le> A"
    and B0_nonnegative: "0 \<le> B0"
    and B1_nonnegative: "0 \<le> B1"
  shows
    "\<exists>C::real. 0 < C \<and>
      (\<forall>tau c coefficient multiplier M.
        2 \<le> tau \<and>
        aim_complex_lp_on_plane p coefficient \<and>
        {x. coefficient x \<noteq> 0} \<subseteq> Y \<and>
        multiplier \<in> borel_measurable lborel \<and>
        (AE x in lborel. norm (multiplier x) \<le> M) \<and>
        0 \<le> M
        \<longrightarrow>
        slp_complex_lp_on (aim_hls_target_exponent p) X
          (slp_partial_psi_inverse tau c
            (\<lambda>x. cutoff x *
              slp_dbar_psi_inverse tau c
                (\<lambda>y. coefficient y * multiplier y) x))
        \<and>
        slp_complex_lp_norm_on (aim_hls_target_exponent p) X
          (slp_partial_psi_inverse tau c
            (\<lambda>x. cutoff x *
              slp_dbar_psi_inverse tau c
                (\<lambda>y. coefficient y * multiplier y) x))
          \<le> C * inverse (sqrt tau) * M *
            aim_complex_lp_norm p coefficient
        \<and>
        slp_complex_lp_on (aim_hls_target_exponent p) X
          (slp_dbar_psi_inverse (- tau) c
            (\<lambda>x. cutoff x *
              slp_partial_psi_inverse (- tau) c
                (\<lambda>y. coefficient y * multiplier y) x))
        \<and>
        slp_complex_lp_norm_on (aim_hls_target_exponent p) X
          (slp_dbar_psi_inverse (- tau) c
            (\<lambda>x. cutoff x *
              slp_partial_psi_inverse (- tau) c
                (\<lambda>y. coefficient y * multiplier y) x))
          \<le> C * inverse (sqrt tau) * M *
            aim_complex_lp_norm p coefficient)"
proof -
  have exponent_positive: "0 < p"
    using exponent_lower by linarith
  have target_positive: "0 < aim_hls_target_exponent p"
    using slp_qstar_exponent_relations(1)[OF exponent_lower exponent_upper]
    by linarith
  have X_measurable: "X \<in> sets lborel"
    using X_open by simp
  obtain K :: real where K_positive: "0 < K"
    and inner_gain:
      "\<And>tau c coefficient multiplier M.
        aim_complex_lp_on_plane p coefficient \<Longrightarrow>
        {x. coefficient x \<noteq> 0} \<subseteq> Y \<Longrightarrow>
        multiplier \<in> borel_measurable lborel \<Longrightarrow>
        (AE x in lborel. norm (multiplier x) \<le> M) \<Longrightarrow>
        0 \<le> M \<Longrightarrow>
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
        A_nonnegative B0_nonnegative B1_nonnegative]
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
      OF outer_context
        exponent_lower exponent_upper X_bounded]
    by blast
  let ?C = "H * K"
  have C_positive: "0 < ?C"
    by (rule mult_pos_pos[OF H_positive K_positive])
  have cutoff_support: "closure {x. cutoff x \<noteq> 0} \<subseteq> X"
    using cutoff_test unfolding slp_test_function_on_def by blast
  have restrict_cutoff_product:
      "slp_restrict_field X (\<lambda>x. cutoff x * h x) =
        (\<lambda>x. cutoff x * h x)" for h :: slp_scalar_field
  proof (rule ext)
    fix x
    show "slp_restrict_field X (\<lambda>x. cutoff x * h x) x =
        cutoff x * h x"
    proof (cases "x \<in> X")
      case True
      then show ?thesis by (simp add: slp_restrict_field_def)
    next
      case False
      have cutoff_zero: "cutoff x = 0"
      proof (rule ccontr)
        assume "cutoff x \<noteq> 0"
        then have "x \<in> closure {x. cutoff x \<noteq> 0}"
          unfolding closure_def by simp
        with cutoff_support False show False by blast
      qed
      show ?thesis using False cutoff_zero
        by (simp add: slp_restrict_field_def)
    qed
  qed
  show ?thesis
  proof (rule exI[of _ ?C], rule conjI[OF C_positive])
    show "\<forall>tau c coefficient multiplier M.
        2 \<le> tau \<and>
        aim_complex_lp_on_plane p coefficient \<and>
        {x. coefficient x \<noteq> 0} \<subseteq> Y \<and>
        multiplier \<in> borel_measurable lborel \<and>
        (AE x in lborel. norm (multiplier x) \<le> M) \<and>
        0 \<le> M
        \<longrightarrow>
        slp_complex_lp_on (aim_hls_target_exponent p) X
          (slp_partial_psi_inverse tau c
            (\<lambda>x. cutoff x *
              slp_dbar_psi_inverse tau c
                (\<lambda>y. coefficient y * multiplier y) x))
        \<and>
        slp_complex_lp_norm_on (aim_hls_target_exponent p) X
          (slp_partial_psi_inverse tau c
            (\<lambda>x. cutoff x *
              slp_dbar_psi_inverse tau c
                (\<lambda>y. coefficient y * multiplier y) x))
          \<le> ?C * inverse (sqrt tau) * M *
            aim_complex_lp_norm p coefficient
        \<and>
        slp_complex_lp_on (aim_hls_target_exponent p) X
          (slp_dbar_psi_inverse (- tau) c
            (\<lambda>x. cutoff x *
              slp_partial_psi_inverse (- tau) c
                (\<lambda>y. coefficient y * multiplier y) x))
        \<and>
        slp_complex_lp_norm_on (aim_hls_target_exponent p) X
          (slp_dbar_psi_inverse (- tau) c
            (\<lambda>x. cutoff x *
              slp_partial_psi_inverse (- tau) c
                (\<lambda>y. coefficient y * multiplier y) x))
          \<le> ?C * inverse (sqrt tau) * M *
            aim_complex_lp_norm p coefficient"
    proof (intro allI impI)
      fix tau :: real and c :: slp_point
        and coefficient multiplier :: slp_scalar_field and M :: real
      assume data:
        "2 \<le> tau \<and>
          aim_complex_lp_on_plane p coefficient \<and>
          {x. coefficient x \<noteq> 0} \<subseteq> Y \<and>
          multiplier \<in> borel_measurable lborel \<and>
          (AE x in lborel. norm (multiplier x) \<le> M) \<and>
          0 \<le> M"
      have tau_lower: "2 \<le> tau" using data by blast
      have coefficient_lp: "aim_complex_lp_on_plane p coefficient"
        using data by blast
      have coefficient_carrier: "{x. coefficient x \<noteq> 0} \<subseteq> Y"
        using data by blast
      have multiplier_measurable: "multiplier \<in> borel_measurable lborel"
        using data by blast
      have multiplier_bound: "AE x in lborel. norm (multiplier x) \<le> M"
        using data by blast
      have M_nonnegative: "0 \<le> M" using data by blast
      let ?source = "\<lambda>x. coefficient x * multiplier x"
      let ?uL = "\<lambda>x. cutoff x * slp_dbar_psi_inverse tau c ?source x"
      let ?DuL = "\<lambda>x. \<chi> i.
        cutoff x *
          slp_dbar_inverse_gradient
            (slp_oscillatory_modulation (- tau) c ?source) x $ i +
        slp_dbar_psi_inverse tau c ?source x *
          slp_complex_partial_derivative cutoff i x"
      let ?uR = "\<lambda>x. cutoff x *
        slp_partial_psi_inverse (- tau) c ?source x"
      let ?DuR = "\<lambda>x. \<chi> i.
        cutoff x *
          slp_partial_inverse_gradient
            (slp_oscillatory_modulation (- tau) c ?source) x $ i +
        slp_partial_psi_inverse (- tau) c ?source x *
          slp_complex_partial_derivative cutoff i x"
      let ?TL = "slp_partial_psi_inverse tau c ?uL"
      let ?TR = "slp_dbar_psi_inverse (- tau) c ?uR"
      note product = slp_complex_lp_AE_bounded_multiplier[
        where p=p and multiplier=multiplier and f=coefficient and C=M,
        OF exponent_positive multiplier_measurable multiplier_bound
          M_nonnegative coefficient_lp]
      have source_lp: "aim_complex_lp_on_plane p ?source"
        using product(1) by (simp only: mult.commute)
      have source_carrier: "{x. ?source x \<noteq> 0} \<subseteq> Y"
        using coefficient_carrier by auto
      have source_support: "bounded {x. ?source x \<noteq> 0}"
        by (rule bounded_subset[OF Y_bounded source_carrier])
      note zero_pairs = slp_both_inner_cauchy_mult_test_w1p_zero_pairs[
        OF evans_density exponent_lower X_open X_bounded source_lp
          source_support cutoff_test]
      have zero_left: "slp_w1p_zero_pair_on p X ?uL ?DuL"
        by (rule conjunct1[OF zero_pairs])
      have zero_right: "slp_w1p_zero_pair_on p X ?uR ?DuR"
        by (rule conjunct2[OF zero_pairs])
      note inner = inner_gain[OF coefficient_lp coefficient_carrier
        multiplier_measurable multiplier_bound M_nonnegative]
      have inner_left:
          "slp_w1p_norm_on p X ?uL ?DuL \<le>
            K * M * aim_complex_lp_norm p coefficient"
        by (rule conjunct1[OF inner])
      have inner_right:
          "slp_w1p_norm_on p X ?uR ?DuR \<le>
            K * M * aim_complex_lp_norm p coefficient"
        by (rule conjunct2[OF inner])
      have restrict_left: "slp_restrict_field X ?uL = ?uL"
        by (rule restrict_cutoff_product)
      have restrict_right: "slp_restrict_field X ?uR = ?uR"
        by (rule restrict_cutoff_product)
      have left_global:
          "aim_complex_lp_on_plane (aim_hls_target_exponent p) ?TL \<and>
            aim_complex_lp_norm (aim_hls_target_exponent p) ?TL
              \<le> H * inverse (sqrt tau) * slp_w1p_norm_on p X ?uL ?DuL"
        using outer_gain[
          where tau=tau and c=c and f="?uL" and Df="?DuL"
            and epsilon=1 and orientation=SLP_Partial_Inverse,
          OF tau_lower zero_left]
        by (simp add: slp_partial_psi_inverse_def restrict_left)
      have right_global:
          "aim_complex_lp_on_plane (aim_hls_target_exponent p) ?TR \<and>
            aim_complex_lp_norm (aim_hls_target_exponent p) ?TR
              \<le> H * inverse (sqrt tau) * slp_w1p_norm_on p X ?uR ?DuR"
        using outer_gain[
          where tau=tau and c=c and f="?uR" and Df="?DuR"
            and epsilon=1 and orientation=SLP_Dbar_Inverse,
          OF tau_lower zero_right]
        by (simp add: slp_dbar_psi_inverse_def restrict_right)
      have left_local_lp:
          "slp_complex_lp_on (aim_hls_target_exponent p) X ?TL"
        by (rule aim_complex_lp_on_plane_restrict[
              OF target_positive X_measurable conjunct1[OF left_global]])
      have right_local_lp:
          "slp_complex_lp_on (aim_hls_target_exponent p) X ?TR"
        by (rule aim_complex_lp_on_plane_restrict[
              OF target_positive X_measurable conjunct1[OF right_global]])
      have left_local_le:
          "slp_complex_lp_norm_on (aim_hls_target_exponent p) X ?TL \<le>
            aim_complex_lp_norm (aim_hls_target_exponent p) ?TL"
        by (rule slp_complex_lp_norm_on_le[
              OF target_positive X_measurable conjunct1[OF left_global]])
      have right_local_le:
          "slp_complex_lp_norm_on (aim_hls_target_exponent p) X ?TR \<le>
            aim_complex_lp_norm (aim_hls_target_exponent p) ?TR"
        by (rule slp_complex_lp_norm_on_le[
              OF target_positive X_measurable conjunct1[OF right_global]])
      have scale_nonnegative: "0 \<le> H * inverse (sqrt tau)"
        using H_positive tau_lower by simp
      have left_scaled:
          "H * inverse (sqrt tau) * slp_w1p_norm_on p X ?uL ?DuL \<le>
            H * inverse (sqrt tau) *
              (K * M * aim_complex_lp_norm p coefficient)"
        by (rule mult_left_mono[OF inner_left scale_nonnegative])
      have right_scaled:
          "H * inverse (sqrt tau) * slp_w1p_norm_on p X ?uR ?DuR \<le>
            H * inverse (sqrt tau) *
              (K * M * aim_complex_lp_norm p coefficient)"
        by (rule mult_left_mono[OF inner_right scale_nonnegative])
      have left_bound:
          "slp_complex_lp_norm_on (aim_hls_target_exponent p) X ?TL \<le>
            ?C * inverse (sqrt tau) * M *
              aim_complex_lp_norm p coefficient"
        using order_trans[OF left_local_le
              order_trans[OF conjunct2[OF left_global] left_scaled]]
        by (simp only: mult.assoc mult.left_commute mult.commute)
      have right_bound:
          "slp_complex_lp_norm_on (aim_hls_target_exponent p) X ?TR \<le>
            ?C * inverse (sqrt tau) * M *
              aim_complex_lp_norm p coefficient"
        using order_trans[OF right_local_le
              order_trans[OF conjunct2[OF right_global] right_scaled]]
        by (simp only: mult.assoc mult.left_commute mult.commute)
      show
          "slp_complex_lp_on (aim_hls_target_exponent p) X ?TL \<and>
            slp_complex_lp_norm_on (aim_hls_target_exponent p) X ?TL
              \<le> ?C * inverse (sqrt tau) * M *
                aim_complex_lp_norm p coefficient
          \<and>
          slp_complex_lp_on (aim_hls_target_exponent p) X ?TR \<and>
            slp_complex_lp_norm_on (aim_hls_target_exponent p) X ?TR
              \<le> ?C * inverse (sqrt tau) * M *
                aim_complex_lp_norm p coefficient"
        by (rule conjI[OF left_local_lp], rule conjI[OF left_bound],
            rule conjI[OF right_local_lp right_bound])
    qed
  qed
qed

end

end
