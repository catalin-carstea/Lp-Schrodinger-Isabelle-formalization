theory Inverse_Schrodinger_Lp_Quadratic_Phase_H1_Multiplier
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_Quadratic_Phase_Derivatives"
begin

section \<open>Project-H1 closure under smooth bounded-carrier multiplication\<close>

theorem slp_h1_pair_on_mult_smooth_bounded:
  assumes X_measurable: "X \<in> sets (lborel :: slp_point measure)"
    and X_bounded: "bounded X"
    and pair: "slp_h1_pair_on X u Du"
    and multiplier_smooth: "smooth_on UNIV a"
  shows "slp_h1_pair_on X
    (\<lambda>x. a x * u x)
    (\<lambda>x. \<chi> i. a x * Du x $ i +
      u x * slp_complex_partial_derivative a i x)"
proof -
  have pair_two: "slp_w1p_pair_on 2 X u Du"
    by (rule slp_h1_pair_on_w1p_pair_on_two[OF X_measurable pair])
  have product_two:
      "slp_w1p_pair_on 2 X
        (\<lambda>x. a x * u x)
        (\<lambda>x. \<chi> i. a x * Du x $ i +
          u x * slp_complex_partial_derivative a i x)"
    by (rule slp_w1p_pair_on_mult_smooth_bounded[OF
          _ X_measurable X_bounded pair_two multiplier_smooth])
       simp
  show ?thesis
    by (rule slp_w1p_pair_on_two_h1_pair_on[OF
          X_measurable product_two])
qed

section \<open>Exact quadratic-phase Cartesian partials\<close>

lemma slp_holomorphic_quadratic_phase_multiplier_partial_derivative:
  "slp_complex_partial_derivative
      (slp_holomorphic_quadratic_phase_multiplier tau c) i z =
    slp_holomorphic_quadratic_phase_multiplier tau c z *
      (\<i> * of_real tau * slp_point_as_complex (z - c) *
        slp_point_as_complex (axis i 1))"
proof -
  have derivative:
      "((slp_holomorphic_quadratic_phase_multiplier tau c) has_derivative
        (\<lambda>h. slp_holomorphic_quadratic_phase_multiplier tau c z *
          (\<i> * of_real tau * slp_point_as_complex (z - c) *
            slp_point_as_complex h))) (at z)"
    by (rule
          slp_holomorphic_quadratic_phase_multiplier_has_derivative(1))
  have frechet:
      "frechet_derivative
          (slp_holomorphic_quadratic_phase_multiplier tau c) (at z) =
        (\<lambda>h. slp_holomorphic_quadratic_phase_multiplier tau c z *
          (\<i> * of_real tau * slp_point_as_complex (z - c) *
            slp_point_as_complex h))"
    by (rule sym, rule frechet_derivative_at[OF derivative])
  show ?thesis
    unfolding slp_complex_partial_derivative_def frechet ..
qed

lemma slp_antiholomorphic_quadratic_phase_multiplier_partial_derivative:
  "slp_complex_partial_derivative
      (slp_antiholomorphic_quadratic_phase_multiplier tau c) i z =
    slp_antiholomorphic_quadratic_phase_multiplier tau c z *
      (\<i> * of_real tau * cnj (slp_point_as_complex (z - c)) *
        cnj (slp_point_as_complex (axis i 1)))"
proof -
  have derivative:
      "((slp_antiholomorphic_quadratic_phase_multiplier tau c) has_derivative
        (\<lambda>h. slp_antiholomorphic_quadratic_phase_multiplier tau c z *
          (\<i> * of_real tau * cnj (slp_point_as_complex (z - c)) *
            cnj (slp_point_as_complex h)))) (at z)"
    by (rule
          slp_antiholomorphic_quadratic_phase_multiplier_has_derivative(1))
  have frechet:
      "frechet_derivative
          (slp_antiholomorphic_quadratic_phase_multiplier tau c) (at z) =
        (\<lambda>h. slp_antiholomorphic_quadratic_phase_multiplier tau c z *
          (\<i> * of_real tau * cnj (slp_point_as_complex (z - c)) *
            cnj (slp_point_as_complex h)))"
    by (rule sym, rule frechet_derivative_at[OF derivative])
  show ?thesis
    unfolding slp_complex_partial_derivative_def frechet ..
qed

section \<open>Exact quadratic-phase project-H1 products\<close>

theorem slp_h1_pair_on_holomorphic_quadratic_phase_multiplier:
  assumes X_measurable: "X \<in> sets (lborel :: slp_point measure)"
    and X_bounded: "bounded X"
    and pair: "slp_h1_pair_on X u Du"
  shows "slp_h1_pair_on X
    (\<lambda>x. slp_holomorphic_quadratic_phase_multiplier tau c x * u x)
    (\<lambda>x. \<chi> i.
      slp_holomorphic_quadratic_phase_multiplier tau c x * Du x $ i +
      u x * (slp_holomorphic_quadratic_phase_multiplier tau c x *
        (\<i> * of_real tau * slp_point_as_complex (x - c) *
          slp_point_as_complex (axis i 1))))"
proof -
  have multiplier_smooth:
      "smooth_on UNIV
        (slp_holomorphic_quadratic_phase_multiplier tau c)"
    by (rule
          slp_holomorphic_quadratic_phase_multiplier_has_derivative(2))
  have raw:
      "slp_h1_pair_on X
        (\<lambda>x. slp_holomorphic_quadratic_phase_multiplier tau c x * u x)
        (\<lambda>x. \<chi> i.
          slp_holomorphic_quadratic_phase_multiplier tau c x * Du x $ i +
          u x * slp_complex_partial_derivative
            (slp_holomorphic_quadratic_phase_multiplier tau c) i x)"
    by (rule slp_h1_pair_on_mult_smooth_bounded[OF
          X_measurable X_bounded pair multiplier_smooth])
  show ?thesis
    using raw
    by (simp only:
          slp_holomorphic_quadratic_phase_multiplier_partial_derivative)
qed

theorem slp_h1_pair_on_antiholomorphic_quadratic_phase_multiplier:
  assumes X_measurable: "X \<in> sets (lborel :: slp_point measure)"
    and X_bounded: "bounded X"
    and pair: "slp_h1_pair_on X u Du"
  shows "slp_h1_pair_on X
    (\<lambda>x. slp_antiholomorphic_quadratic_phase_multiplier tau c x * u x)
    (\<lambda>x. \<chi> i.
      slp_antiholomorphic_quadratic_phase_multiplier tau c x * Du x $ i +
      u x * (slp_antiholomorphic_quadratic_phase_multiplier tau c x *
        (\<i> * of_real tau * cnj (slp_point_as_complex (x - c)) *
          cnj (slp_point_as_complex (axis i 1)))))"
proof -
  have multiplier_smooth:
      "smooth_on UNIV
        (slp_antiholomorphic_quadratic_phase_multiplier tau c)"
    by (rule
          slp_antiholomorphic_quadratic_phase_multiplier_has_derivative(2))
  have raw:
      "slp_h1_pair_on X
        (\<lambda>x.
          slp_antiholomorphic_quadratic_phase_multiplier tau c x * u x)
        (\<lambda>x. \<chi> i.
          slp_antiholomorphic_quadratic_phase_multiplier tau c x * Du x $ i +
          u x * slp_complex_partial_derivative
            (slp_antiholomorphic_quadratic_phase_multiplier tau c) i x)"
    by (rule slp_h1_pair_on_mult_smooth_bounded[OF
          X_measurable X_bounded pair multiplier_smooth])
  show ?thesis
    using raw
    by (simp only:
          slp_antiholomorphic_quadratic_phase_multiplier_partial_derivative)
qed

end
