theory Inverse_Schrodinger_Lp_Quadratic_Phase_H1_Algebra
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_Quadratic_Phase_H1_Multiplier"
begin

section \<open>Bounded-carrier project-H1 algebra\<close>

lemma slp_h1_pair_on_const_bounded:
  fixes k :: complex
  assumes X_measurable: "X \<in> sets (lborel :: slp_point measure)"
    and X_bounded: "bounded X"
  shows "slp_h1_pair_on X (\<lambda>_. k) (\<lambda>_. 0)"
proof -
  have weak_UNIV:
      "slp_weak_gradient_on UNIV (\<lambda>_. k) (\<lambda>_. 0)"
    by (rule slp_weak_gradient_on_UNIV_const)
  have weak: "slp_weak_gradient_on X (\<lambda>_. k) (\<lambda>_. 0)"
    by (rule slp_weak_gradient_on_UNIV_imp_on[OF weak_UNIV])
  have value_restricted_lp:
      "aim_complex_lp_on_plane 2
        (slp_restrict_field X (\<lambda>_. k))"
    by (rule slp_bounded_restriction_lp_norm(1)[
          where A = "Real_Vector_Spaces.norm k"])
       (use X_measurable X_bounded in simp_all)
  have value_lp: "slp_complex_lp_on 2 X (\<lambda>_. k)"
    using value_restricted_lp unfolding slp_complex_lp_on_def .
  have zero_restricted_lp:
      "aim_complex_lp_on_plane 2
        (slp_restrict_field X (\<lambda>_. 0))"
    by (rule slp_bounded_restriction_lp_norm(1)[where A = 0])
       (use X_measurable X_bounded in simp_all)
  have zero_lp: "slp_complex_lp_on 2 X (\<lambda>_. 0)"
    using zero_restricted_lp unfolding slp_complex_lp_on_def .
  have pair_two:
      "slp_w1p_pair_on 2 X (\<lambda>_. k) (\<lambda>_. 0)"
    unfolding slp_w1p_pair_on_def
    using weak value_lp zero_lp by simp
  show ?thesis
    by (rule slp_w1p_pair_on_two_h1_pair_on[OF
          X_measurable pair_two])
qed

theorem slp_h1_pair_on_add:
  assumes X_measurable: "X \<in> sets (lborel :: slp_point measure)"
    and X_bounded: "bounded X"
    and first_pair: "slp_h1_pair_on X u Du"
    and second_pair: "slp_h1_pair_on X v Dv"
  shows "slp_h1_pair_on X
    (\<lambda>x. u x + v x) (\<lambda>x. Du x + Dv x)"
proof -
  have first_two: "slp_w1p_pair_on 2 X u Du"
    by (rule slp_h1_pair_on_w1p_pair_on_two[OF
          X_measurable first_pair])
  have second_two: "slp_w1p_pair_on 2 X v Dv"
    by (rule slp_h1_pair_on_w1p_pair_on_two[OF
          X_measurable second_pair])
  have zero_h1:
      "slp_h1_pair_on X
        (\<lambda>_. (0::complex)) (\<lambda>_. (0::complex ^ 2))"
    by (rule slp_h1_pair_on_const_bounded[OF
          X_measurable X_bounded])
  have zero_two:
      "slp_w1p_pair_on 2 X
        (\<lambda>_. (0::complex)) (\<lambda>_. (0::complex ^ 2))"
    by (rule slp_h1_pair_on_w1p_pair_on_two[OF
          X_measurable zero_h1])
  have negative_two:
      "slp_w1p_pair_on 2 X
        (\<lambda>x. - v x) (\<lambda>x. - Dv x)"
  proof -
    have raw:
        "slp_w1p_pair_on 2 X
          (\<lambda>x. (0::complex) - v x)
          (\<lambda>x. (0::complex ^ 2) - Dv x)"
      by (rule slp_w1p_pair_on_diff[OF _ zero_two second_two]) simp
    show ?thesis using raw by simp
  qed
  have sum_two:
      "slp_w1p_pair_on 2 X
        (\<lambda>x. u x + v x) (\<lambda>x. Du x + Dv x)"
  proof -
    have raw:
        "slp_w1p_pair_on 2 X
          (\<lambda>x. u x - (- v x))
          (\<lambda>x. Du x - (- Dv x))"
      by (rule slp_w1p_pair_on_diff[OF _ first_two negative_two]) simp
    show ?thesis using raw by simp
  qed
  show ?thesis
    by (rule slp_w1p_pair_on_two_h1_pair_on[OF
          X_measurable sum_two])
qed

section \<open>Pure quadratic phases in project H1\<close>

theorem slp_h1_pair_on_holomorphic_quadratic_phase:
  assumes X_measurable: "X \<in> sets (lborel :: slp_point measure)"
    and X_bounded: "bounded X"
  shows "slp_h1_pair_on X
    (slp_holomorphic_quadratic_phase_multiplier tau c)
    (\<lambda>x. \<chi> i.
      slp_holomorphic_quadratic_phase_multiplier tau c x *
        (\<i> * of_real tau * slp_point_as_complex (x - c) *
          slp_point_as_complex (axis i 1)))"
proof -
  have one_pair:
      "slp_h1_pair_on X
        (\<lambda>_. (1::complex)) (\<lambda>_. (0::complex ^ 2))"
    by (rule slp_h1_pair_on_const_bounded[OF
          X_measurable X_bounded])
  have raw:
      "slp_h1_pair_on X
        (\<lambda>x.
          slp_holomorphic_quadratic_phase_multiplier tau c x * 1)
        (\<lambda>x. \<chi> i.
          slp_holomorphic_quadratic_phase_multiplier tau c x *
            (0::complex ^ 2) $ i +
          1 * (slp_holomorphic_quadratic_phase_multiplier tau c x *
            (\<i> * of_real tau * slp_point_as_complex (x - c) *
              slp_point_as_complex (axis i 1))))"
    by (rule
          slp_h1_pair_on_holomorphic_quadratic_phase_multiplier[OF
            X_measurable X_bounded one_pair])
  show ?thesis
    using raw
    by (simp only: zero_index mult_zero_right add_0
          mult.left_neutral mult.right_neutral)
qed

theorem slp_h1_pair_on_antiholomorphic_quadratic_phase:
  assumes X_measurable: "X \<in> sets (lborel :: slp_point measure)"
    and X_bounded: "bounded X"
  shows "slp_h1_pair_on X
    (slp_antiholomorphic_quadratic_phase_multiplier tau c)
    (\<lambda>x. \<chi> i.
      slp_antiholomorphic_quadratic_phase_multiplier tau c x *
        (\<i> * of_real tau * cnj (slp_point_as_complex (x - c)) *
          cnj (slp_point_as_complex (axis i 1))))"
proof -
  have one_pair:
      "slp_h1_pair_on X
        (\<lambda>_. (1::complex)) (\<lambda>_. (0::complex ^ 2))"
    by (rule slp_h1_pair_on_const_bounded[OF
          X_measurable X_bounded])
  have raw:
      "slp_h1_pair_on X
        (\<lambda>x.
          slp_antiholomorphic_quadratic_phase_multiplier tau c x * 1)
        (\<lambda>x. \<chi> i.
          slp_antiholomorphic_quadratic_phase_multiplier tau c x *
            (0::complex ^ 2) $ i +
          1 * (slp_antiholomorphic_quadratic_phase_multiplier tau c x *
            (\<i> * of_real tau *
              cnj (slp_point_as_complex (x - c)) *
              cnj (slp_point_as_complex (axis i 1)))))"
    by (rule
          slp_h1_pair_on_antiholomorphic_quadratic_phase_multiplier[OF
            X_measurable X_bounded one_pair])
  show ?thesis
    using raw
    by (simp only: zero_index mult_zero_right add_0
          mult.left_neutral mult.right_neutral)
qed

end
