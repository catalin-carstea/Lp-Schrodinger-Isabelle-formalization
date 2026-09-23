theory Inverse_Schrodinger_Lp_Inner_Cauchy_Coefficient_Product_Cutoff_Norm
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Inner_Cauchy_Fixed_Carrier_Norm"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Concrete coefficient-product cutoff graph bounds\<close>

context slp_cauchy_local_w1s
begin

theorem slp_both_inner_cauchy_coefficient_product_cutoff_w1p_norm_bounds:
  fixes s A B0 B1 :: real
    and X Y :: "slp_point set"
    and cutoff :: slp_scalar_field
  assumes exponent_lower: "1 < s"
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
        aim_complex_lp_on_plane s coefficient \<and>
        {x. coefficient x \<noteq> 0} \<subseteq> Y \<and>
        multiplier \<in> borel_measurable lborel \<and>
        (AE x in lborel. norm (multiplier x) \<le> M) \<and>
        0 \<le> M
        \<longrightarrow>
        slp_w1p_norm_on s X
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
          \<le> C * M * aim_complex_lp_norm s coefficient
        \<and>
        slp_w1p_norm_on s X
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
          \<le> C * M * aim_complex_lp_norm s coefficient)"
proof -
  have exponent_positive: "0 < s"
    using exponent_lower by linarith
  have X_measurable: "X \<in> sets lborel"
    using X_open by simp
  obtain K :: real where K_positive: "0 < K"
    and K_bound:
      "\<And>tau c source.
        aim_complex_lp_on_plane s source \<Longrightarrow>
        {x. source x \<noteq> 0} \<subseteq> Y \<Longrightarrow>
        slp_w1p_norm_on s X
            (slp_dbar_psi_inverse tau c source)
            (slp_dbar_inverse_gradient
              (slp_oscillatory_modulation (- tau) c source))
          \<le> K * aim_complex_lp_norm s source
        \<and>
        slp_w1p_norm_on s X
            (slp_partial_psi_inverse (- tau) c source)
            (slp_partial_inverse_gradient
              (slp_oscillatory_modulation (- tau) c source))
          \<le> K * aim_complex_lp_norm s source"
    using slp_both_inner_cauchy_fixed_carrier_w1p_norm_bounds[
      OF exponent_lower X_measurable X_bounded Y_bounded]
    by blast
  let ?F = "4 * (9 * A + 4 * B0 + 4 * B1)"
  let ?C = "?F * K + 1"
  have inner_nonnegative: "0 \<le> 9 * A + 4 * B0 + 4 * B1"
    using A_nonnegative B0_nonnegative B1_nonnegative by linarith
  have F_nonnegative: "0 \<le> ?F"
    by (rule mult_nonneg_nonneg) (simp_all add: inner_nonnegative)
  have FK_nonnegative: "0 \<le> ?F * K"
    by (rule mult_nonneg_nonneg[OF F_nonnegative
          less_imp_le[OF K_positive]])
  have C_positive: "0 < ?C"
    using FK_nonnegative by linarith
  show ?thesis
  proof (rule exI[of _ ?C], rule conjI[OF C_positive])
    show "\<forall>tau c coefficient multiplier M.
        aim_complex_lp_on_plane s coefficient \<and>
        {x. coefficient x \<noteq> 0} \<subseteq> Y \<and>
        multiplier \<in> borel_measurable lborel \<and>
        (AE x in lborel. norm (multiplier x) \<le> M) \<and>
        0 \<le> M
        \<longrightarrow>
        slp_w1p_norm_on s X
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
          \<le> ?C * M * aim_complex_lp_norm s coefficient
        \<and>
        slp_w1p_norm_on s X
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
          \<le> ?C * M * aim_complex_lp_norm s coefficient"
    proof (intro allI impI, elim conjE)
      fix tau :: real and c :: slp_point
        and coefficient multiplier :: slp_scalar_field and M :: real
      assume coefficient_lp: "aim_complex_lp_on_plane s coefficient"
        and coefficient_carrier: "{x. coefficient x \<noteq> 0} \<subseteq> Y"
        and multiplier_measurable:
          "multiplier \<in> borel_measurable lborel"
        and multiplier_bound:
          "AE x in lborel. norm (multiplier x) \<le> M"
        and M_nonnegative: "0 \<le> M"
      let ?source = "\<lambda>x. coefficient x * multiplier x"
      note product = slp_complex_lp_AE_bounded_multiplier[
        where p=s and multiplier=multiplier and f=coefficient and C=M,
        OF exponent_positive multiplier_measurable multiplier_bound
          M_nonnegative coefficient_lp]
      have source_lp: "aim_complex_lp_on_plane s ?source"
        using product(1) by (simp only: mult.commute)
      have source_norm_bound:
          "aim_complex_lp_norm s ?source \<le>
            M * aim_complex_lp_norm s coefficient"
        using product(2) by (simp only: mult.commute)
      have source_carrier: "{x. ?source x \<noteq> 0} \<subseteq> Y"
        using coefficient_carrier by auto
      have source_support: "bounded {x. ?source x \<noteq> 0}"
        by (rule bounded_subset[OF Y_bounded source_carrier])
      note raw = K_bound[OF source_lp source_carrier]
      note cutoff_graph = slp_both_inner_cauchy_mult_test_w1p_norm_bounds[
        where source="?source",
        OF exponent_lower X_open X_bounded source_lp source_support
          cutoff_test cutoff_bound cutoff_derivative_zero_bound
          cutoff_derivative_one_bound A_nonnegative B0_nonnegative
          B1_nonnegative]
      have source_norm_nonnegative:
          "0 \<le> aim_complex_lp_norm s ?source"
        unfolding aim_complex_lp_norm_def by (rule powr_ge_zero)
      have coefficient_norm_nonnegative:
          "0 \<le> aim_complex_lp_norm s coefficient"
        unfolding aim_complex_lp_norm_def by (rule powr_ge_zero)
      have M_coefficient_nonnegative:
          "0 \<le> M * aim_complex_lp_norm s coefficient"
        by (rule mult_nonneg_nonneg[OF M_nonnegative
              coefficient_norm_nonnegative])
      have common_scaled_bound:
          "?F * (K * aim_complex_lp_norm s ?source) \<le>
            ?C * M * aim_complex_lp_norm s coefficient"
      proof -
        have first:
            "K * aim_complex_lp_norm s ?source \<le>
              K * (M * aim_complex_lp_norm s coefficient)"
          by (rule mult_left_mono[OF source_norm_bound])
             (simp add: less_imp_le[OF K_positive])
        have second:
            "?F * (K * aim_complex_lp_norm s ?source) \<le>
              ?F * (K * (M * aim_complex_lp_norm s coefficient))"
          by (rule mult_left_mono[OF first F_nonnegative])
        have coefficient_le: "?F * K \<le> ?C"
          by simp
        have third:
            "(?F * K) * (M * aim_complex_lp_norm s coefficient) \<le>
              ?C * (M * aim_complex_lp_norm s coefficient)"
          by (rule mult_right_mono[OF coefficient_le
                M_coefficient_nonnegative])
        show ?thesis
          using second third by (simp add: algebra_simps)
      qed
      have dbar_bound:
          "slp_w1p_norm_on s X
              (\<lambda>x. cutoff x *
                slp_dbar_psi_inverse tau c ?source x)
              (\<lambda>x. \<chi> i.
                cutoff x *
                  slp_dbar_inverse_gradient
                    (slp_oscillatory_modulation (- tau) c ?source) x $ i +
                slp_dbar_psi_inverse tau c ?source x *
                  slp_complex_partial_derivative cutoff i x)
            \<le> ?C * M * aim_complex_lp_norm s coefficient"
        apply (rule order_trans[OF conjunct1[OF cutoff_graph]])
        subgoal by simp
        subgoal by simp
        subgoal by simp
        subgoal
          by (rule order_trans[OF mult_left_mono[OF conjunct1[OF raw]
                F_nonnegative] common_scaled_bound])
        done
      have partial_bound:
          "slp_w1p_norm_on s X
              (\<lambda>x. cutoff x *
                slp_partial_psi_inverse (- tau) c ?source x)
              (\<lambda>x. \<chi> i.
                cutoff x *
                  slp_partial_inverse_gradient
                    (slp_oscillatory_modulation (- tau) c ?source) x $ i +
                slp_partial_psi_inverse (- tau) c ?source x *
                  slp_complex_partial_derivative cutoff i x)
            \<le> ?C * M * aim_complex_lp_norm s coefficient"
        apply (rule order_trans[OF conjunct2[OF cutoff_graph]])
        subgoal by simp
        subgoal by simp
        subgoal by simp
        subgoal
          by (rule order_trans[OF mult_left_mono[OF conjunct2[OF raw]
                F_nonnegative] common_scaled_bound])
        done
      show
          "slp_w1p_norm_on s X
              (\<lambda>x. cutoff x *
                slp_dbar_psi_inverse tau c ?source x)
              (\<lambda>x. \<chi> i.
                cutoff x *
                  slp_dbar_inverse_gradient
                    (slp_oscillatory_modulation (- tau) c ?source) x $ i +
                slp_dbar_psi_inverse tau c ?source x *
                  slp_complex_partial_derivative cutoff i x)
            \<le> ?C * M * aim_complex_lp_norm s coefficient
          \<and>
          slp_w1p_norm_on s X
              (\<lambda>x. cutoff x *
                slp_partial_psi_inverse (- tau) c ?source x)
              (\<lambda>x. \<chi> i.
                cutoff x *
                  slp_partial_inverse_gradient
                    (slp_oscillatory_modulation (- tau) c ?source) x $ i +
                slp_partial_psi_inverse (- tau) c ?source x *
                  slp_complex_partial_derivative cutoff i x)
            \<le> ?C * M * aim_complex_lp_norm s coefficient"
        by (rule conjI[OF dbar_bound partial_bound])
    qed
  qed
qed

end

end
