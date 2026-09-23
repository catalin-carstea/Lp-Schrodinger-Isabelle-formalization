theory Inverse_Schrodinger_Lp_W1p_Rough_Center_Quantitative_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Rough_Global_Far_IBP_Center"
begin

section \<open>Explicit quantitative rough bound at the phase center\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_w1p_zero_pair_partial_psi_inverse_rough_center_bound:
  fixes b A R tau delta :: real
    and c :: slp_point
    and X :: "slp_point set"
    and u :: slp_scalar_field
    and Du :: slp_gradient_field
  assumes tau_positive: "0 < tau"
    and exponent_above_two: "2 < b"
    and radius_nonnegative: "0 \<le> A"
    and relative_radius_nonnegative: "0 \<le> R"
    and set_radius:
      "\<And>y. y \<in> X \<Longrightarrow> Real_Vector_Spaces.norm y \<le> A"
    and relative_radius:
      "\<And>y. y \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm (c - y) \<le> R"
    and center_in: "c \<in> X"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and delta_positive: "0 < delta"
    and normalized_lower: "1 \<le> R / delta"
    and zero_pair: "slp_w1p_zero_pair_on b X u Du"
  defines "q \<equiv> slp_holder_conjugate b"
  shows total_integrable:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (slp_oscillatory_modulation tau c
          (slp_restrict_field X u)) c"
    and quantitative_bound:
      "(let
          P = Real_Vector_Spaces.norm (inverse (of_real pi :: complex));
          K = P *
            (integral\<^sup>L lborel
              (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x) powr q))
                powr (1 / q);
          K1 = P *
            (integral\<^sup>L lborel
              (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr q))
                powr (1 / q);
          W = slp_w1p_norm_on b X u Du;
          M = K * (192 * W);
          N = P * M * delta *
            (6 * integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
              2 * unit_ball_vol 2);
          DB = K * ((2 / delta) * (4 * W));
          CB = (2 * slp_global_cutoff_L / delta) *
            (K1 * pi powr (1 / b) * M);
          SB = P * M *
            ((1 / delta) *
                integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
              (1 / delta) * (1 + log 2 (R / delta)) *
                integral\<^sup>L lborel
                  (slp_squared_radial_annulus 1 2))
        in
          Real_Vector_Spaces.norm (slp_partial_psi_inverse tau c
            (slp_restrict_field X u) c) \<le>
            N + (1 / tau) * (DB + (CB + SB)))"
proof -
  let ?near =
    "slp_partial_psi_inverse tau c
      (slp_global_cutoff.slp_near_cutoff_amplitude delta c
        (slp_restrict_field X u)) c"
  let ?far =
    "slp_partial_psi_inverse tau c
      (slp_global_far_cutoff_amplitude delta c
        (slp_restrict_field X u)) c"
  let ?derivative =
    "slp_partial_psi_inverse tau c
      (slp_restrict_field X
        (slp_gradient_wirtinger_partial
          (\<lambda>x. \<chi> i.
            slp_global_far_coefficient delta c x * Du x $ i +
            u x * slp_complex_partial_derivative
              (slp_global_far_coefficient delta c) i x))) c"
  let ?P =
    "Real_Vector_Spaces.norm (inverse (of_real pi :: complex))"
  let ?K =
    "?P *
      (integral\<^sup>L lborel
        (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x) powr q))
          powr (1 / q)"
  let ?K1 =
    "?P *
      (integral\<^sup>L lborel
        (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr q))
          powr (1 / q)"
  let ?W = "slp_w1p_norm_on b X u Du"
  let ?M = "?K * (192 * ?W)"
  let ?N =
    "?P * ?M * delta *
      (6 * integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
        2 * unit_ball_vol 2)"
  let ?DB = "?K * ((2 / delta) * (4 * ?W))"
  let ?CB =
    "(2 * slp_global_cutoff_L / delta) *
      (?K1 * pi powr (1 / b) * ?M)"
  let ?SB =
    "?P * ?M *
      ((1 / delta) *
          integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
        (1 / delta) * (1 + log 2 (R / delta)) *
          integral\<^sup>L lborel (slp_squared_radial_annulus 1 2))"

  show total_integrable:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
      (slp_oscillatory_modulation tau c
        (slp_restrict_field X u)) c"
    using slp_w1p_zero_pair_near_far_split_center(1)[
      where b=b and A=A and R=R and tau=tau and c=c and X=X
        and delta=delta and u=u and Du=Du,
      OF exponent_above_two radius_nonnegative
        relative_radius_nonnegative set_radius relative_radius
        X_measurable X_bounded delta_positive zero_pair]
    by blast

  have relative_radius_reverse:
      "Real_Vector_Spaces.norm (y - c) \<le> R" if "y \<in> X" for y
    using relative_radius[OF that]
    by (simp only: norm_minus_commute)
  have near_bound: "Real_Vector_Spaces.norm ?near \<le> ?N"
    using slp_w1p_zero_pair_near_center_bound(2)[
      where b=b and A=A and tau=tau and c=c and X=X and delta=delta
        and u=u and Du=Du,
      OF exponent_above_two radius_nonnegative set_radius
        delta_positive zero_pair, folded q_def]
    by blast
  have derivative_bound:
      "Real_Vector_Spaces.norm ?derivative \<le> ?DB + (?CB + ?SB)"
    using slp_w1p_global_far_complete_derivative_center_bound(2)[
      where b=b and A=A and R=R and tau=tau and c=c and X=X
        and delta=delta and u=u and Du=Du,
      OF exponent_above_two radius_nonnegative set_radius
        relative_radius_reverse center_in delta_positive normalized_lower
        zero_pair, folded q_def]
    by blast
  have far_identity:
      "?far =
        (1 / (\<i> * of_real tau)) * (0 - ?derivative)"
    using slp_w1p_zero_pair_partial_psi_inverse_rough_global_far_center[
      where p=b and tau=tau and c=c and X=X and delta=delta
        and u=u and Du=Du,
      OF tau_positive exponent_above_two X_measurable X_bounded
        delta_positive zero_pair]
    by blast
  have scalar_norm:
      "Real_Vector_Spaces.norm
        (1 / (\<i> * of_real tau) :: complex) = 1 / tau"
    using tau_positive
    by (simp only: norm_divide norm_one norm_mult norm_ii norm_of_real
          abs_of_pos)
  have inverse_tau_nonnegative: "0 \<le> 1 / tau"
    using tau_positive by simp
  have zero_minus_derivative:
      "(0 :: complex) - ?derivative = - ?derivative"
    by simp
  have negative_derivative_norm:
      "Real_Vector_Spaces.norm (- ?derivative) =
        Real_Vector_Spaces.norm ?derivative"
    by (rule norm_minus_cancel)
  have far_bound:
      "Real_Vector_Spaces.norm ?far \<le>
        (1 / tau) * (?DB + (?CB + ?SB))"
  proof -
    have "Real_Vector_Spaces.norm ?far =
        Real_Vector_Spaces.norm
          ((1 / (\<i> * of_real tau)) * (0 - ?derivative))"
      by (simp only: far_identity)
    also have "... =
        Real_Vector_Spaces.norm (1 / (\<i> * of_real tau)) *
          Real_Vector_Spaces.norm (0 - ?derivative)"
      by (rule norm_mult)
    also have "... =
        (1 / tau) * Real_Vector_Spaces.norm ?derivative"
      by (simp only: scalar_norm zero_minus_derivative
            negative_derivative_norm)
    also have "... \<le> (1 / tau) * (?DB + (?CB + ?SB))"
      by (rule mult_left_mono[OF derivative_bound
            inverse_tau_nonnegative])
    finally show ?thesis .
  qed
  have operator_split:
      "slp_partial_psi_inverse tau c (slp_restrict_field X u) c =
        ?near + ?far"
    using slp_w1p_zero_pair_near_far_split_center(2)[
      where b=b and A=A and R=R and tau=tau and c=c and X=X
        and delta=delta and u=u and Du=Du,
      OF exponent_above_two radius_nonnegative
        relative_radius_nonnegative set_radius relative_radius
        X_measurable X_bounded delta_positive zero_pair]
    by blast
  have total_bound:
      "Real_Vector_Spaces.norm (slp_partial_psi_inverse tau c
          (slp_restrict_field X u) c) \<le>
        ?N + (1 / tau) * (?DB + (?CB + ?SB))"
  proof -
    have "Real_Vector_Spaces.norm (slp_partial_psi_inverse tau c
        (slp_restrict_field X u) c) =
          Real_Vector_Spaces.norm (?near + ?far)"
      by (simp only: operator_split)
    also have "... \<le>
        Real_Vector_Spaces.norm ?near + Real_Vector_Spaces.norm ?far"
      by (rule norm_triangle_ineq)
    also have "... \<le>
        ?N + (1 / tau) * (?DB + (?CB + ?SB))"
      by (rule add_mono[OF near_bound far_bound])
    finally show ?thesis .
  qed
  show quantitative_bound:
      "(let
      P = Real_Vector_Spaces.norm (inverse (of_real pi :: complex));
      K = P *
        (integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x) powr q))
            powr (1 / q);
      K1 = P *
        (integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr q))
            powr (1 / q);
      W = slp_w1p_norm_on b X u Du;
      M = K * (192 * W);
      N = P * M * delta *
        (6 * integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
          2 * unit_ball_vol 2);
      DB = K * ((2 / delta) * (4 * W));
      CB = (2 * slp_global_cutoff_L / delta) *
        (K1 * pi powr (1 / b) * M);
      SB = P * M *
        ((1 / delta) *
            integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
          (1 / delta) * (1 + log 2 (R / delta)) *
            integral\<^sup>L lborel
              (slp_squared_radial_annulus 1 2))
    in
      Real_Vector_Spaces.norm (slp_partial_psi_inverse tau c
        (slp_restrict_field X u) c) \<le>
        N + (1 / tau) * (DB + (CB + SB)))"
    unfolding Let_def by (rule total_bound)
qed

end

end
