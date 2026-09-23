theory Inverse_Schrodinger_Lp_Nested_Coefficient_Difference_Pointwise
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Oscillatory_Cauchy_Difference_AE"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cauchy_Packed_Positive_Amplitude"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Pointwise additivity of the cutoff-nested operators\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_both_nested_oscillatory_cauchy_difference_pointwise:
  fixes p :: real
    and X :: "slp_point set"
    and cutoff f g :: slp_scalar_field
  assumes exponent_lower: "1 < p"
    and exponent_upper: "p < 2"
    and X_bounded: "bounded X"
    and cutoff_test: "slp_test_function_on X cutoff"
    and first_lp: "aim_complex_lp_on_plane p f"
    and second_lp: "aim_complex_lp_on_plane p g"
  shows
    "\<forall>z\<in>X.
      slp_partial_psi_inverse tau c
          (\<lambda>x. cutoff x *
            slp_dbar_psi_inverse tau c (\<lambda>y. f y - g y) x) z =
        slp_partial_psi_inverse tau c
            (\<lambda>x. cutoff x * slp_dbar_psi_inverse tau c f x) z -
          slp_partial_psi_inverse tau c
            (\<lambda>x. cutoff x * slp_dbar_psi_inverse tau c g x) z
      \<and>
      slp_dbar_psi_inverse (- tau) c
          (\<lambda>x. cutoff x *
            slp_partial_psi_inverse (- tau) c
              (\<lambda>y. f y - g y) x) z =
        slp_dbar_psi_inverse (- tau) c
            (\<lambda>x. cutoff x *
              slp_partial_psi_inverse (- tau) c f x) z -
          slp_dbar_psi_inverse (- tau) c
            (\<lambda>x. cutoff x *
              slp_partial_psi_inverse (- tau) c g x) z"
proof -
  have exponent_positive: "0 < p"
    using exponent_lower by linarith
  have difference_lp:
      "aim_complex_lp_on_plane p (\<lambda>y. f y - g y)"
    by (rule aim_complex_lp_on_plane_diff[
          OF exponent_positive first_lp second_lp])
  have nested_integrable:
      "\<And>tau1 tau2 c1 c2 h outer inner z.
        aim_complex_lp_on_plane p h \<Longrightarrow>
        z \<in> X \<Longrightarrow>
        slp_cauchy_integrable_at outer
          (slp_oscillatory_modulation tau1 c1
            (\<lambda>x. cutoff x *
              slp_cauchy_transform inner
                (slp_oscillatory_modulation tau2 c2 h) x)) z"
    using slp_two_oscillatory_cauchy_test_cutoff_bound[
      OF exponent_lower exponent_upper X_bounded cutoff_test]
    by blast
  have guarded_difference:
      "\<And>orientation h u v z.
        slp_cauchy_integrable_at orientation h z \<Longrightarrow>
        slp_cauchy_integrable_at orientation u z \<Longrightarrow>
        slp_cauchy_integrable_at orientation v z \<Longrightarrow>
        (AE y in lborel. h y = u y - v y) \<Longrightarrow>
        slp_cauchy_transform orientation h z =
          slp_cauchy_transform orientation u z -
            slp_cauchy_transform orientation v z"
  proof -
    fix orientation h u v z
    assume h_integrable: "slp_cauchy_integrable_at orientation h z"
      and u_integrable: "slp_cauchy_integrable_at orientation u z"
      and v_integrable: "slp_cauchy_integrable_at orientation v z"
      and h_ae: "AE y in lborel. h y = u y - v y"
    let ?negative_v = "\<lambda>y. (- 1) * v y"
    let ?difference = "\<lambda>y. u y + ?negative_v y"
    have negative_integrable:
        "slp_cauchy_integrable_at orientation ?negative_v z"
      by (rule slp_cauchy_integrable_at_mult_left[OF v_integrable])
    have difference_integrable:
        "slp_cauchy_integrable_at orientation ?difference z"
      by (rule slp_cauchy_integrable_at_add[
            OF u_integrable negative_integrable])
    have h_difference_ae: "AE y in lborel. h y = ?difference y"
      using h_ae by eventually_elim simp
    have congruent:
        "slp_cauchy_transform orientation h z =
          slp_cauchy_transform orientation ?difference z"
      by (rule slp_cauchy_transform_cong_ae[
            OF h_integrable difference_integrable h_difference_ae])
    have additive:
        "slp_cauchy_transform orientation ?difference z =
          slp_cauchy_transform orientation u z +
            slp_cauchy_transform orientation ?negative_v z"
      by (rule slp_cauchy_transform_add[
            OF u_integrable negative_integrable])
    have negative:
        "slp_cauchy_transform orientation ?negative_v z =
          (- 1) * slp_cauchy_transform orientation v z"
      by (rule slp_cauchy_transform_mult_left[OF v_integrable])
    show "slp_cauchy_transform orientation h z =
        slp_cauchy_transform orientation u z -
          slp_cauchy_transform orientation v z"
      using congruent additive negative by simp
  qed
  have inner_differences:
      "(AE x in (lborel :: slp_point measure).
        slp_dbar_psi_inverse tau c (\<lambda>y. f y - g y) x =
          slp_dbar_psi_inverse tau c f x -
            slp_dbar_psi_inverse tau c g x)
      \<and>
      (AE x in (lborel :: slp_point measure).
        slp_partial_psi_inverse (- tau) c (\<lambda>y. f y - g y) x =
          slp_partial_psi_inverse (- tau) c f x -
            slp_partial_psi_inverse (- tau) c g x)"
    by (rule slp_both_oscillatory_cauchy_difference_AE[
          OF exponent_lower exponent_upper first_lp second_lp])
  let ?left_difference =
    "slp_oscillatory_modulation tau c
      (\<lambda>x. cutoff x *
        slp_dbar_psi_inverse tau c (\<lambda>y. f y - g y) x)"
  let ?left_first =
    "slp_oscillatory_modulation tau c
      (\<lambda>x. cutoff x * slp_dbar_psi_inverse tau c f x)"
  let ?left_second =
    "slp_oscillatory_modulation tau c
      (\<lambda>x. cutoff x * slp_dbar_psi_inverse tau c g x)"
  let ?right_difference =
    "slp_oscillatory_modulation tau c
      (\<lambda>x. cutoff x *
        slp_partial_psi_inverse (- tau) c
          (\<lambda>y. f y - g y) x)"
  let ?right_first =
    "slp_oscillatory_modulation tau c
      (\<lambda>x. cutoff x * slp_partial_psi_inverse (- tau) c f x)"
  let ?right_second =
    "slp_oscillatory_modulation tau c
      (\<lambda>x. cutoff x * slp_partial_psi_inverse (- tau) c g x)"
  have left_source_ae:
      "AE x in lborel.
        ?left_difference x = ?left_first x - ?left_second x"
    using conjunct1[OF inner_differences]
  proof eventually_elim
    fix x :: slp_point
    assume inner:
      "slp_dbar_psi_inverse tau c (\<lambda>y. f y - g y) x =
        slp_dbar_psi_inverse tau c f x -
          slp_dbar_psi_inverse tau c g x"
    show "?left_difference x = ?left_first x - ?left_second x"
      unfolding slp_oscillatory_modulation_def
      by (subst inner) (simp add: algebra_simps)
  qed
  have right_source_ae:
      "AE x in lborel.
        ?right_difference x = ?right_first x - ?right_second x"
    using conjunct2[OF inner_differences]
  proof eventually_elim
    fix x :: slp_point
    assume inner:
      "slp_partial_psi_inverse (- tau) c (\<lambda>y. f y - g y) x =
        slp_partial_psi_inverse (- tau) c f x -
          slp_partial_psi_inverse (- tau) c g x"
    show "?right_difference x = ?right_first x - ?right_second x"
      unfolding slp_oscillatory_modulation_def
      by (subst inner) (simp add: algebra_simps)
  qed
  show ?thesis
  proof (intro ballI conjI)
    fix z :: slp_point
    assume z_in: "z \<in> X"
    have left_difference_integrable:
        "slp_cauchy_integrable_at SLP_Partial_Inverse
          ?left_difference z"
      unfolding slp_dbar_psi_inverse_def
      by (rule nested_integrable[
            OF difference_lp z_in])
    have left_first_integrable:
        "slp_cauchy_integrable_at SLP_Partial_Inverse
          ?left_first z"
      unfolding slp_dbar_psi_inverse_def
      by (rule nested_integrable[OF first_lp z_in])
    have left_second_integrable:
        "slp_cauchy_integrable_at SLP_Partial_Inverse
          ?left_second z"
      unfolding slp_dbar_psi_inverse_def
      by (rule nested_integrable[OF second_lp z_in])
    have left:
        "slp_cauchy_transform SLP_Partial_Inverse ?left_difference z =
          slp_cauchy_transform SLP_Partial_Inverse ?left_first z -
            slp_cauchy_transform SLP_Partial_Inverse ?left_second z"
      by (rule guarded_difference[
            OF left_difference_integrable left_first_integrable
              left_second_integrable left_source_ae])
    show
      "slp_partial_psi_inverse tau c
          (\<lambda>x. cutoff x *
            slp_dbar_psi_inverse tau c (\<lambda>y. f y - g y) x) z =
        slp_partial_psi_inverse tau c
            (\<lambda>x. cutoff x * slp_dbar_psi_inverse tau c f x) z -
          slp_partial_psi_inverse tau c
            (\<lambda>x. cutoff x * slp_dbar_psi_inverse tau c g x) z"
      using left unfolding slp_partial_psi_inverse_def .
  next
    fix z :: slp_point
    assume z_in: "z \<in> X"
    have right_difference_integrable:
        "slp_cauchy_integrable_at SLP_Dbar_Inverse
          ?right_difference z"
      unfolding slp_partial_psi_inverse_def
      by (rule nested_integrable[
            OF difference_lp z_in])
    have right_first_integrable:
        "slp_cauchy_integrable_at SLP_Dbar_Inverse
          ?right_first z"
      unfolding slp_partial_psi_inverse_def
      by (rule nested_integrable[OF first_lp z_in])
    have right_second_integrable:
        "slp_cauchy_integrable_at SLP_Dbar_Inverse
          ?right_second z"
      unfolding slp_partial_psi_inverse_def
      by (rule nested_integrable[OF second_lp z_in])
    have right:
        "slp_cauchy_transform SLP_Dbar_Inverse ?right_difference z =
          slp_cauchy_transform SLP_Dbar_Inverse ?right_first z -
            slp_cauchy_transform SLP_Dbar_Inverse ?right_second z"
      by (rule guarded_difference[
            OF right_difference_integrable right_first_integrable
              right_second_integrable right_source_ae])
    show
      "slp_dbar_psi_inverse (- tau) c
          (\<lambda>x. cutoff x *
            slp_partial_psi_inverse (- tau) c
              (\<lambda>y. f y - g y) x) z =
        slp_dbar_psi_inverse (- tau) c
            (\<lambda>x. cutoff x *
              slp_partial_psi_inverse (- tau) c f x) z -
          slp_dbar_psi_inverse (- tau) c
            (\<lambda>x. cutoff x *
              slp_partial_psi_inverse (- tau) c g x) z"
      using right
      unfolding slp_dbar_psi_inverse_def
      by (simp only: minus_minus)
  qed
qed

theorem slp_both_nested_coefficient_difference_pointwise:
  fixes p M :: real
    and X :: "slp_point set"
    and cutoff q1 q2 multiplier :: slp_scalar_field
  assumes exponent_lower: "1 < p"
    and exponent_upper: "p < 2"
    and X_bounded: "bounded X"
    and cutoff_test: "slp_test_function_on X cutoff"
    and first_lp: "aim_complex_lp_on_plane p q1"
    and second_lp: "aim_complex_lp_on_plane p q2"
    and multiplier_measurable:
      "multiplier \<in> borel_measurable lborel"
    and multiplier_bound:
      "AE x in lborel. norm (multiplier x) \<le> M"
    and bound_nonnegative: "0 \<le> M"
  shows
    "\<forall>z\<in>X.
      slp_partial_psi_inverse tau c
          (\<lambda>x. cutoff x *
            slp_dbar_psi_inverse tau c
              (\<lambda>y. (q1 y - q2 y) * multiplier y) x) z =
        slp_partial_psi_inverse tau c
            (\<lambda>x. cutoff x *
              slp_dbar_psi_inverse tau c
                (\<lambda>y. q1 y * multiplier y) x) z -
          slp_partial_psi_inverse tau c
            (\<lambda>x. cutoff x *
              slp_dbar_psi_inverse tau c
                (\<lambda>y. q2 y * multiplier y) x) z
      \<and>
      slp_dbar_psi_inverse (- tau) c
          (\<lambda>x. cutoff x *
            slp_partial_psi_inverse (- tau) c
              (\<lambda>y. (q1 y - q2 y) * multiplier y) x) z =
        slp_dbar_psi_inverse (- tau) c
            (\<lambda>x. cutoff x *
              slp_partial_psi_inverse (- tau) c
                (\<lambda>y. q1 y * multiplier y) x) z -
          slp_dbar_psi_inverse (- tau) c
            (\<lambda>x. cutoff x *
              slp_partial_psi_inverse (- tau) c
                (\<lambda>y. q2 y * multiplier y) x) z"
proof -
  have exponent_positive: "0 < p"
    using exponent_lower by linarith
  note first_product = slp_complex_lp_AE_bounded_multiplier[
    where p=p and multiplier=multiplier and f=q1 and C=M,
    OF exponent_positive multiplier_measurable multiplier_bound
      bound_nonnegative first_lp]
  note second_product = slp_complex_lp_AE_bounded_multiplier[
    where p=p and multiplier=multiplier and f=q2 and C=M,
    OF exponent_positive multiplier_measurable multiplier_bound
      bound_nonnegative second_lp]
  have first_product_lp:
      "aim_complex_lp_on_plane p (\<lambda>y. q1 y * multiplier y)"
    using first_product(1) by (simp only: mult.commute)
  have second_product_lp:
      "aim_complex_lp_on_plane p (\<lambda>y. q2 y * multiplier y)"
    using second_product(1) by (simp only: mult.commute)
  have generic:
      "\<forall>z\<in>X.
        slp_partial_psi_inverse tau c
            (\<lambda>x. cutoff x *
              slp_dbar_psi_inverse tau c
                (\<lambda>y. q1 y * multiplier y -
                  q2 y * multiplier y) x) z =
          slp_partial_psi_inverse tau c
              (\<lambda>x. cutoff x *
                slp_dbar_psi_inverse tau c
                  (\<lambda>y. q1 y * multiplier y) x) z -
            slp_partial_psi_inverse tau c
              (\<lambda>x. cutoff x *
                slp_dbar_psi_inverse tau c
                  (\<lambda>y. q2 y * multiplier y) x) z
        \<and>
        slp_dbar_psi_inverse (- tau) c
            (\<lambda>x. cutoff x *
              slp_partial_psi_inverse (- tau) c
                (\<lambda>y. q1 y * multiplier y -
                  q2 y * multiplier y) x) z =
          slp_dbar_psi_inverse (- tau) c
              (\<lambda>x. cutoff x *
                slp_partial_psi_inverse (- tau) c
                  (\<lambda>y. q1 y * multiplier y) x) z -
            slp_dbar_psi_inverse (- tau) c
              (\<lambda>x. cutoff x *
                slp_partial_psi_inverse (- tau) c
                  (\<lambda>y. q2 y * multiplier y) x) z"
    by (rule slp_both_nested_oscillatory_cauchy_difference_pointwise[
          OF exponent_lower exponent_upper X_bounded cutoff_test
            first_product_lp second_product_lp])
  show ?thesis
    using generic by (simp add: algebra_simps)
qed

end

end
