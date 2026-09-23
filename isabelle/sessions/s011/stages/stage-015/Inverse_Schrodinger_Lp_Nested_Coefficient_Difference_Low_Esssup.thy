theory Inverse_Schrodinger_Lp_Nested_Coefficient_Difference_Low_Esssup
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Nested_Coefficient_Product_Low_Esssup"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Actual nested coefficient-difference continuity\<close>

context aim_planar_hls_cauchy
begin

theorem slp_both_nested_coefficient_difference_low_esssup_bounds:
  fixes p :: real
    and X :: "slp_point set"
    and cutoff :: slp_scalar_field
  assumes exponent_lower: "1 < p"
    and exponent_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and cutoff_test: "slp_test_function_on X cutoff"
  shows
    "\<exists>C::real. 0 < C \<and>
      (\<forall>q1 q2 tau c multiplier M.
        aim_complex_lp_on_plane p q1 \<and>
        aim_complex_lp_on_plane p q2 \<and>
        multiplier \<in> borel_measurable lborel \<and>
        (AE x in lborel. norm (multiplier x) \<le> M) \<and>
        0 \<le> M
        \<longrightarrow>
        (\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X
              (slp_partial_psi_inverse tau c
                (\<lambda>x. cutoff x *
                  slp_dbar_psi_inverse tau c
                    (\<lambda>y. (q1 y - q2 y) * multiplier y) x)) z)))
          \<in> borel_measurable (lborel :: slp_point measure)
        \<and>
        esssup (lborel :: slp_point measure)
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_partial_psi_inverse tau c
                  (\<lambda>x. cutoff x *
                    slp_dbar_psi_inverse tau c
                      (\<lambda>y. (q1 y - q2 y) * multiplier y) x)) z)))
          \<le> ereal (C * M *
            aim_complex_lp_norm p (\<lambda>y. q1 y - q2 y))
        \<and>
        (\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X
              (slp_dbar_psi_inverse (- tau) c
                (\<lambda>x. cutoff x *
                  slp_partial_psi_inverse (- tau) c
                    (\<lambda>y. (q1 y - q2 y) * multiplier y) x)) z)))
          \<in> borel_measurable (lborel :: slp_point measure)
        \<and>
        esssup (lborel :: slp_point measure)
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_dbar_psi_inverse (- tau) c
                  (\<lambda>x. cutoff x *
                    slp_partial_psi_inverse (- tau) c
                      (\<lambda>y. (q1 y - q2 y) * multiplier y) x)) z)))
          \<le> ereal (C * M *
            aim_complex_lp_norm p (\<lambda>y. q1 y - q2 y)))"
proof -
  have exponent_positive: "0 < p"
    using exponent_lower by linarith
  obtain C :: real where C_positive: "0 < C"
    and endpoint:
      "\<forall>tau c coefficient multiplier M.
        aim_complex_lp_on_plane p coefficient \<and>
        multiplier \<in> borel_measurable lborel \<and>
        (AE x in lborel. norm (multiplier x) \<le> M) \<and>
        0 \<le> M
        \<longrightarrow>
        (\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X
              (slp_partial_psi_inverse tau c
                (\<lambda>x. cutoff x *
                  slp_dbar_psi_inverse tau c
                    (\<lambda>y. coefficient y * multiplier y) x)) z)))
          \<in> borel_measurable (lborel :: slp_point measure)
        \<and>
        esssup (lborel :: slp_point measure)
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_partial_psi_inverse tau c
                  (\<lambda>x. cutoff x *
                    slp_dbar_psi_inverse tau c
                      (\<lambda>y. coefficient y * multiplier y) x)) z)))
          \<le> ereal (C * M * aim_complex_lp_norm p coefficient)
        \<and>
        (\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X
              (slp_dbar_psi_inverse (- tau) c
                (\<lambda>x. cutoff x *
                  slp_partial_psi_inverse (- tau) c
                    (\<lambda>y. coefficient y * multiplier y) x)) z)))
          \<in> borel_measurable (lborel :: slp_point measure)
        \<and>
        esssup (lborel :: slp_point measure)
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_dbar_psi_inverse (- tau) c
                  (\<lambda>x. cutoff x *
                    slp_partial_psi_inverse (- tau) c
                      (\<lambda>y. coefficient y * multiplier y) x)) z)))
          \<le> ereal (C * M * aim_complex_lp_norm p coefficient)"
    using slp_both_nested_coefficient_product_low_esssup_bounds[
      where a=p and X=X and cutoff=cutoff,
      OF exponent_lower exponent_upper X_measurable X_bounded cutoff_test]
    by blast
  show ?thesis
  proof (rule exI[of _ C], rule conjI[OF C_positive])
    show "\<forall>q1 q2 tau c multiplier M.
        aim_complex_lp_on_plane p q1 \<and>
        aim_complex_lp_on_plane p q2 \<and>
        multiplier \<in> borel_measurable lborel \<and>
        (AE x in lborel. norm (multiplier x) \<le> M) \<and>
        0 \<le> M
        \<longrightarrow>
        (\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X
              (slp_partial_psi_inverse tau c
                (\<lambda>x. cutoff x *
                  slp_dbar_psi_inverse tau c
                    (\<lambda>y. (q1 y - q2 y) * multiplier y) x)) z)))
          \<in> borel_measurable (lborel :: slp_point measure)
        \<and>
        esssup (lborel :: slp_point measure)
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_partial_psi_inverse tau c
                  (\<lambda>x. cutoff x *
                    slp_dbar_psi_inverse tau c
                      (\<lambda>y. (q1 y - q2 y) * multiplier y) x)) z)))
          \<le> ereal (C * M *
            aim_complex_lp_norm p (\<lambda>y. q1 y - q2 y))
        \<and>
        (\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X
              (slp_dbar_psi_inverse (- tau) c
                (\<lambda>x. cutoff x *
                  slp_partial_psi_inverse (- tau) c
                    (\<lambda>y. (q1 y - q2 y) * multiplier y) x)) z)))
          \<in> borel_measurable (lborel :: slp_point measure)
        \<and>
        esssup (lborel :: slp_point measure)
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_dbar_psi_inverse (- tau) c
                  (\<lambda>x. cutoff x *
                    slp_partial_psi_inverse (- tau) c
                      (\<lambda>y. (q1 y - q2 y) * multiplier y) x)) z)))
          \<le> ereal (C * M *
            aim_complex_lp_norm p (\<lambda>y. q1 y - q2 y))"
    proof (intro allI impI)
      fix q1 q2 :: slp_scalar_field and tau :: real and c :: slp_point
        and multiplier :: slp_scalar_field and M :: real
      assume input_data:
        "aim_complex_lp_on_plane p q1 \<and>
          aim_complex_lp_on_plane p q2 \<and>
          multiplier \<in> borel_measurable lborel \<and>
          (AE x in lborel. norm (multiplier x) \<le> M) \<and>
          0 \<le> M"
      have q1_lp: "aim_complex_lp_on_plane p q1"
        by (rule conjunct1[OF input_data])
      have q2_lp: "aim_complex_lp_on_plane p q2"
        by (rule conjunct1[OF conjunct2[OF input_data]])
      have multiplier_data:
          "multiplier \<in> borel_measurable lborel \<and>
            (AE x in lborel. norm (multiplier x) \<le> M) \<and>
            0 \<le> M"
        by (rule conjunct2[OF conjunct2[OF input_data]])
      have difference_lp:
          "aim_complex_lp_on_plane p (\<lambda>y. q1 y - q2 y)"
        by (rule aim_complex_lp_on_plane_diff[
              OF exponent_positive q1_lp q2_lp])
      have endpoint_input:
          "aim_complex_lp_on_plane p (\<lambda>y. q1 y - q2 y) \<and>
            multiplier \<in> borel_measurable lborel \<and>
            (AE x in lborel. norm (multiplier x) \<le> M) \<and>
            0 \<le> M"
        by (rule conjI[OF difference_lp multiplier_data])
      show "(\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X
              (slp_partial_psi_inverse tau c
                (\<lambda>x. cutoff x *
                  slp_dbar_psi_inverse tau c
                    (\<lambda>y. (q1 y - q2 y) * multiplier y) x)) z)))
          \<in> borel_measurable (lborel :: slp_point measure)
        \<and>
        esssup (lborel :: slp_point measure)
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_partial_psi_inverse tau c
                  (\<lambda>x. cutoff x *
                    slp_dbar_psi_inverse tau c
                      (\<lambda>y. (q1 y - q2 y) * multiplier y) x)) z)))
          \<le> ereal (C * M *
            aim_complex_lp_norm p (\<lambda>y. q1 y - q2 y))
        \<and>
        (\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X
              (slp_dbar_psi_inverse (- tau) c
                (\<lambda>x. cutoff x *
                  slp_partial_psi_inverse (- tau) c
                    (\<lambda>y. (q1 y - q2 y) * multiplier y) x)) z)))
          \<in> borel_measurable (lborel :: slp_point measure)
        \<and>
        esssup (lborel :: slp_point measure)
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_dbar_psi_inverse (- tau) c
                  (\<lambda>x. cutoff x *
                    slp_partial_psi_inverse (- tau) c
                      (\<lambda>y. (q1 y - q2 y) * multiplier y) x)) z)))
          \<le> ereal (C * M *
            aim_complex_lp_norm p (\<lambda>y. q1 y - q2 y))"
        by (rule endpoint[rule_format,
              where tau=tau and c=c
                and coefficient="\<lambda>y. q1 y - q2 y"
                and multiplier=multiplier and M=M])
          (rule endpoint_input)
    qed
  qed
qed

end

end
