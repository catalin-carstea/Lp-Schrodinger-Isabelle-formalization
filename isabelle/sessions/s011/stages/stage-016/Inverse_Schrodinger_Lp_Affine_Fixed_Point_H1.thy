theory Inverse_Schrodinger_Lp_Affine_Fixed_Point_H1
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Outer_Conjugated_Field_H1"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Outer_Affine_Fixed_Point_AE"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Pair_AE_Transport"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Restricted almost-everywhere transport of local Lp membership\<close>

lemma slp_complex_lp_on_cong_restrict_AE:
  fixes u v :: slp_scalar_field
  assumes X_measurable: "X \<in> sets lborel"
    and source_lp: "slp_complex_lp_on p X u"
    and target_measurable: "v \<in> borel_measurable lborel"
    and equality_AE: "AE x in restrict_space lborel X. u x = v x"
  shows "slp_complex_lp_on p X v"
proof -
  let ?uX = "slp_restrict_field X u"
  let ?vX = "slp_restrict_field X v"
  have source_power_integrable:
      "integrable lborel
        (\<lambda>x. Real_Vector_Spaces.norm (?uX x) powr p)"
    using source_lp
    unfolding slp_complex_lp_on_def aim_complex_lp_on_plane_def by blast
  have target_restricted_measurable: "?vX \<in> borel_measurable lborel"
    by (rule slp_restrict_field_measurable[OF
          X_measurable target_measurable])
  have target_power_measurable:
      "(\<lambda>x. Real_Vector_Spaces.norm (?vX x) powr p)
        \<in> borel_measurable lborel"
    using target_restricted_measurable by measurable
  have equality_inside: "AE x in lborel. x \<in> X \<longrightarrow> u x = v x"
    using equality_AE X_measurable by (simp add: AE_restrict_space_iff)
  have restricted_AE: "AE x in lborel. ?uX x = ?vX x"
    using equality_inside
    by eventually_elim (auto simp: slp_restrict_field_def)
  have power_AE:
      "AE x in lborel.
        Real_Vector_Spaces.norm (?uX x) powr p =
          Real_Vector_Spaces.norm (?vX x) powr p"
    using restricted_AE by eventually_elim simp
  have target_power_integrable:
      "integrable lborel
        (\<lambda>x. Real_Vector_Spaces.norm (?vX x) powr p)"
    by (rule integrable_cong_AE_imp[OF source_power_integrable
          target_power_measurable power_AE])
  show ?thesis
    unfolding slp_complex_lp_on_def aim_complex_lp_on_plane_def
    using target_restricted_measurable target_power_integrable by blast
qed

section \<open>Above-two Sobolev pairs descend to the project H1 carrier\<close>

lemma slp_w1p_pair_on_above_two_h1_pair_on:
  assumes exponent_above_two: "2 < s"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and pair: "slp_w1p_pair_on s X u Du"
  shows "slp_h1_pair_on X u Du"
proof -
  have weak: "slp_weak_gradient_on X u Du"
    and u_ls: "slp_complex_lp_on s X u"
    and D0_ls: "slp_complex_lp_on s X (\<lambda>x. Du x $ 0)"
    and D1_ls: "slp_complex_lp_on s X (\<lambda>x. Du x $ 1)"
    using pair unfolding slp_w1p_pair_on_def by blast+
  have exponent_order: "2 \<le> s"
    using exponent_above_two by linarith
  have u_l2: "slp_complex_lp_on 2 X u"
    by (rule slp_complex_lp_on_mono_exponent_bounded[OF
          _ exponent_order X_measurable X_bounded u_ls]) simp
  have D0_l2: "slp_complex_lp_on 2 X (\<lambda>x. Du x $ 0)"
    by (rule slp_complex_lp_on_mono_exponent_bounded[OF
          _ exponent_order X_measurable X_bounded D0_ls]) simp
  have D1_l2: "slp_complex_lp_on 2 X (\<lambda>x. Du x $ 1)"
    by (rule slp_complex_lp_on_mono_exponent_bounded[OF
          _ exponent_order X_measurable X_bounded D1_ls]) simp
  have pair_two: "slp_w1p_pair_on 2 X u Du"
    unfolding slp_w1p_pair_on_def
    using weak u_l2 D0_l2 D1_l2 by blast
  show ?thesis
    by (rule slp_w1p_pair_on_two_h1_pair_on[OF X_measurable pair_two])
qed

section \<open>Exact affine fixed-point representatives in project H1\<close>

context slp_cauchy_outer_fixed_point
begin

theorem slp_both_affine_fixed_points_h1:
  fixes p M_left M_right tau :: real
    and c :: slp_point
    and X :: "slp_point set"
    and cutoff coefficient W_left W_right :: slp_scalar_field
  assumes exponent_lower: "1 < p"
    and exponent_upper: "p < 2"
    and X_open: "open X"
    and X_bounded: "bounded X"
    and cutoff_test: "slp_test_function_on X cutoff"
    and coefficient_lp: "aim_complex_lp_on_plane p coefficient"
    and coefficient_support: "{x. coefficient x \<noteq> 0} \<subseteq> X"
    and left_admissible:
      "slp_ae_bounded_measurable lborel M_left W_left"
    and right_admissible:
      "slp_ae_bounded_measurable lborel M_right W_right"
    and left_fixed:
      "AE z in lborel.
        W_left z =
          slp_restrict_field X
            (slp_left_neumann_base tau c cutoff coefficient
              SLP_Dbar_Inverse) z +
          slp_restrict_field X
            (slp_left_neumann_step tau c cutoff coefficient W_left) z"
    and right_fixed:
      "AE z in lborel.
        W_right z =
          slp_restrict_field X
            (slp_right_neumann_base tau c cutoff coefficient
              SLP_Partial_Inverse) z +
          slp_restrict_field X
            (slp_right_neumann_step tau c cutoff coefficient W_right) z"
  shows
    "slp_h1_pair_on X W_left
        (slp_left_outer_conjugated_gradient
          tau c cutoff coefficient W_left)
      \<and>
      slp_h1_pair_on X W_right
        (slp_right_outer_conjugated_gradient
          tau c cutoff coefficient W_right)"
proof -
  let ?qstar = "aim_hls_target_exponent p"
  let ?left_outer =
    "slp_left_outer_conjugated_field tau c cutoff coefficient W_left"
  let ?left_gradient =
    "slp_left_outer_conjugated_gradient tau c cutoff coefficient W_left"
  let ?right_outer =
    "slp_right_outer_conjugated_field tau c cutoff coefficient W_right"
  let ?right_gradient =
    "slp_right_outer_conjugated_gradient tau c cutoff coefficient W_right"

  have X_measurable: "X \<in> sets (lborel :: slp_point measure)"
    using X_open by simp
  have qstar_above_two: "2 < ?qstar"
    by (rule slp_qstar_exponent_relations(1)[OF
          exponent_lower exponent_upper])

  note left_certificates = slp_both_outer_conjugated_fields_local_w1pstar[OF
    exponent_lower exponent_upper X_open X_bounded cutoff_test coefficient_lp
    coefficient_support left_admissible X_measurable X_bounded]
  have left_outer_pair:
      "slp_w1p_pair_on ?qstar X ?left_outer ?left_gradient"
    by (rule slp_local_w1s_certificate_w1p_pair_on)
       (rule conjunct1[OF left_certificates])

  note right_certificates = slp_both_outer_conjugated_fields_local_w1pstar[OF
    exponent_lower exponent_upper X_open X_bounded cutoff_test coefficient_lp
    coefficient_support right_admissible X_measurable X_bounded]
  have right_outer_pair:
      "slp_w1p_pair_on ?qstar X ?right_outer ?right_gradient"
    by (rule slp_local_w1s_certificate_w1p_pair_on)
       (rule conjunct2[OF right_certificates])

  note fixed_points = slp_both_affine_fixed_points_eq_restricted_outer_fields_AE[OF
    exponent_lower exponent_upper X_open X_bounded cutoff_test coefficient_lp
    coefficient_support left_admissible right_admissible left_fixed right_fixed]
  have left_inside:
      "AE x in lborel. x \<in> X \<longrightarrow> ?left_outer x = W_left x"
    using conjunct1[OF fixed_points]
    by eventually_elim (simp add: slp_restrict_field_def)
  have left_AE:
      "AE x in restrict_space lborel X. ?left_outer x = W_left x"
    using left_inside X_measurable by (simp add: AE_restrict_space_iff)
  have right_inside:
      "AE x in lborel. x \<in> X \<longrightarrow> ?right_outer x = W_right x"
    using conjunct2[OF fixed_points]
    by eventually_elim (simp add: slp_restrict_field_def)
  have right_AE:
      "AE x in restrict_space lborel X. ?right_outer x = W_right x"
    using right_inside X_measurable by (simp add: AE_restrict_space_iff)

  have left_measurable: "W_left \<in> borel_measurable lborel"
    using left_admissible unfolding slp_ae_bounded_measurable_def by blast
  have right_measurable: "W_right \<in> borel_measurable lborel"
    using right_admissible unfolding slp_ae_bounded_measurable_def by blast
  have left_function_lp: "slp_complex_lp_on ?qstar X W_left"
    by (rule slp_complex_lp_on_cong_restrict_AE[OF X_measurable
          slp_w1p_pair_onD(2)[OF left_outer_pair] left_measurable left_AE])
  have right_function_lp: "slp_complex_lp_on ?qstar X W_right"
    by (rule slp_complex_lp_on_cong_restrict_AE[OF X_measurable
          slp_w1p_pair_onD(2)[OF right_outer_pair] right_measurable right_AE])

  have left_pair:
      "slp_w1p_pair_on ?qstar X W_left ?left_gradient"
    by (rule slp_w1p_pair_on_cong_restrict_AE[OF X_measurable
          left_outer_pair left_function_lp
          slp_w1p_pair_onD(3)[OF left_outer_pair]
          slp_w1p_pair_onD(4)[OF left_outer_pair] left_AE]) simp
  have right_pair:
      "slp_w1p_pair_on ?qstar X W_right ?right_gradient"
    by (rule slp_w1p_pair_on_cong_restrict_AE[OF X_measurable
          right_outer_pair right_function_lp
          slp_w1p_pair_onD(3)[OF right_outer_pair]
          slp_w1p_pair_onD(4)[OF right_outer_pair] right_AE]) simp

  have left_h1: "slp_h1_pair_on X W_left ?left_gradient"
    by (rule slp_w1p_pair_on_above_two_h1_pair_on[OF
          qstar_above_two X_measurable X_bounded left_pair])
  have right_h1: "slp_h1_pair_on X W_right ?right_gradient"
    by (rule slp_w1p_pair_on_above_two_h1_pair_on[OF
          qstar_above_two X_measurable X_bounded right_pair])
  show ?thesis
    using left_h1 right_h1 by blast
qed

end

end
