theory Inverse_Schrodinger_Lp_Common_CGO_Tested_Remainder_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_018.Inverse_Schrodinger_Lp_Product_AE_Root_Integral_Domination"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_CGO_Born_Remainder_Measurable"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Integrated literal common-CGO remainder bound\<close>

definition slp_common_cgo_born_geometric_majorant ::
    "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow>
      real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> slp_scalar_field \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_point \<Rightarrow> real"
  where
  "slp_common_cgo_born_geometric_majorant
      N M p epsilon C_left CV_left C_right CV_right tau
      coefficient coefficient_tilde c =
    (C_left * tau powr (-(1 - 1 / p) + epsilon) *
      (aim_complex_lp_norm p coefficient +
        norm (slp_dbar_inverse coefficient c))) *
      (CV_left * tau powr (-(1 - 1 / p) + epsilon)) ^ N /
      (1 - CV_left * tau powr (-(1 - 1 / p) + epsilon)) +
    (C_right * tau powr (-(1 - 1 / p) + epsilon) *
      (aim_complex_lp_norm p coefficient_tilde +
        norm (slp_partial_inverse coefficient_tilde c))) *
      (CV_right * tau powr (-(1 - 1 / p) + epsilon)) ^ M /
      (1 - CV_right * tau powr (-(1 - 1 / p) + epsilon)) +
    ((C_left * tau powr (-(1 - 1 / p) + epsilon) *
      (aim_complex_lp_norm p coefficient +
        norm (slp_dbar_inverse coefficient c))) /
      (1 - CV_left * tau powr (-(1 - 1 / p) + epsilon))) *
    ((C_right * tau powr (-(1 - 1 / p) + epsilon) *
      (aim_complex_lp_norm p coefficient_tilde +
        norm (slp_partial_inverse coefficient_tilde c))) *
      (CV_right * tau powr (-(1 - 1 / p) + epsilon)) ^ M /
      (1 - CV_right * tau powr (-(1 - 1 / p) + epsilon))) +
    ((C_left * tau powr (-(1 - 1 / p) + epsilon) *
      (aim_complex_lp_norm p coefficient +
        norm (slp_dbar_inverse coefficient c))) *
      (CV_left * tau powr (-(1 - 1 / p) + epsilon)) ^ N /
      (1 - CV_left * tau powr (-(1 - 1 / p) + epsilon))) *
    ((C_right * tau powr (-(1 - 1 / p) + epsilon) *
      (aim_complex_lp_norm p coefficient_tilde +
        norm (slp_partial_inverse coefficient_tilde c))) /
      (1 - CV_right * tau powr (-(1 - 1 / p) + epsilon))) +
    ((C_left * tau powr (-(1 - 1 / p) + epsilon) *
      (aim_complex_lp_norm p coefficient +
        norm (slp_dbar_inverse coefficient c))) *
      (CV_left * tau powr (-(1 - 1 / p) + epsilon)) ^ N /
      (1 - CV_left * tau powr (-(1 - 1 / p) + epsilon))) *
    ((C_right * tau powr (-(1 - 1 / p) + epsilon) *
      (aim_complex_lp_norm p coefficient_tilde +
        norm (slp_partial_inverse coefficient_tilde c))) *
      (CV_right * tau powr (-(1 - 1 / p) + epsilon)) ^ M /
      (1 - CV_right * tau powr (-(1 - 1 / p) + epsilon)))"

context aim_planar_hls_cauchy
begin

theorem slp_common_cgo_born_tested_neumann_remainder_bound:
  fixes N M :: nat
    and p epsilon C_left CV_left C_right CV_right tau :: real
    and X Omega centers :: "slp_point set"
    and phi Q cutoff coefficient coefficient_tilde :: slp_scalar_field
  assumes p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and Omega_subset: "Omega \<subseteq> X"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and Q_outside: "\<And>z. z \<notin> Omega \<Longrightarrow> Q z = 0"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and coefficient_lp: "aim_complex_lp_on_plane p coefficient"
    and coefficient_tilde_lp:
      "aim_complex_lp_on_plane p coefficient_tilde"
    and phi_test: "slp_test_function_on Omega phi"
    and carrier_AE:
      "AE c in (lborel :: slp_point measure).
        c \<in> Omega \<longleftrightarrow> c \<in> centers"
    and left_data:
      "slp_left_neumann_joint_geometric_data
        p epsilon X centers cutoff coefficient C_left CV_left T_left"
    and right_data:
      "slp_right_neumann_joint_geometric_data
        p epsilon X centers cutoff coefficient_tilde C_right CV_right T_right"
    and tau_left: "T_left \<le> tau"
    and tau_right: "T_right \<le> tau"
  shows
    "integrable lborel (\<lambda>c. phi c * integral\<^sup>L lborel (\<lambda>z. Q z *
        slp_cgo_born_neumann_remainder
          X N M tau c cutoff coefficient coefficient_tilde z)) \<and>
     norm (slp_cgo_born_tested_neumann_remainder_functional
        X N M tau phi Q cutoff coefficient coefficient_tilde) \<le>
       (tau / pi) *
       (integral\<^sup>L lborel (\<lambda>c. norm (phi c) *
          slp_common_cgo_born_geometric_majorant
            N M p epsilon C_left CV_left C_right CV_right tau
            coefficient coefficient_tilde c)) *
       (integral\<^sup>L lborel (\<lambda>z. norm (Q z)))"
proof -
  let ?g = "slp_common_cgo_born_geometric_majorant
    N M p epsilon C_left CV_left C_right CV_right tau
    coefficient coefficient_tilde"
  have p_one: "1 \<le> p" using p_lower by linarith
  have phi_test_UNIV: "slp_test_function_on UNIV phi"
    using phi_test unfolding slp_test_function_on_def by blast
  have phi_smooth: "smooth_on UNIV phi"
    using phi_test unfolding slp_test_function_on_def by blast
  have phi_measurable: "phi \<in> borel_measurable lborel"
    using borel_measurable_continuous_onI[
      OF smooth_on_imp_continuous_on[OF phi_smooth]] by simp
  have phi_restriction: "slp_restrict_field Omega phi = phi"
    by (rule slp_test_function_restrict_field_eq[OF phi_test])
  have phi_outside: "phi c = 0" if c_outside: "c \<notin> Omega" for c
  proof -
    have "slp_restrict_field Omega phi c = phi c"
      using fun_cong[OF phi_restriction, of c] .
    then show ?thesis
      by (simp add: slp_restrict_field_def c_outside)
  qed
  have center_support:
      "AE c in (lborel :: slp_point measure).
        c \<in> centers \<or> phi c = 0"
    using carrier_AE
  proof eventually_elim
    fix c
    assume carrier: "c \<in> Omega \<longleftrightarrow> c \<in> centers"
    show "c \<in> centers \<or> phi c = 0"
    proof (cases "c \<in> Omega")
      case True
      then show ?thesis using carrier by blast
    next
      case False
      then show ?thesis using phi_outside by blast
    qed
  qed
  have Q_measurable: "Q \<in> borel_measurable lborel"
    using Q_lp unfolding aim_complex_lp_on_plane_def by blast
  have coefficient_measurable:
      "coefficient \<in> borel_measurable lborel"
    using coefficient_lp unfolding aim_complex_lp_on_plane_def by blast
  have coefficient_tilde_measurable:
      "coefficient_tilde \<in> borel_measurable lborel"
    using coefficient_tilde_lp unfolding aim_complex_lp_on_plane_def by blast
  have Q_outside_X: "Q z = 0" if z_outside: "z \<notin> X" for z
  proof -
    have "z \<notin> Omega" using Omega_subset z_outside by blast
    then show ?thesis by (rule Q_outside)
  qed
  have Q_integrable: "integrable lborel Q"
    by (rule aim_complex_lp_on_plane_integrable_bounded_support[
      OF p_one X_measurable X_bounded Q_lp Q_outside_X])
  have remainder_joint_measurable:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          slp_cgo_born_neumann_remainder X N M tau (fst pair) cutoff
            coefficient coefficient_tilde (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_cgo_born_neumann_remainder_joint_measurable[
      OF X_measurable cutoff_measurable coefficient_measurable
        coefficient_tilde_measurable])
  have weighted_joint_measurable:
      "(\<lambda>pair :: slp_point \<times> slp_point. Q (snd pair) *
          slp_cgo_born_neumann_remainder X N M tau (fst pair) cutoff
            coefficient coefficient_tilde (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using Q_measurable remainder_joint_measurable by measurable
  have outer_measurable:
      "(\<lambda>c. phi c * integral\<^sup>L lborel (\<lambda>z. Q z *
          slp_cgo_born_neumann_remainder X N M tau c cutoff coefficient
            coefficient_tilde z)) \<in> borel_measurable lborel"
    by (rule slp_cgo_born_tested_neumann_remainder_outer_measurable[
      OF X_measurable phi_measurable Q_measurable cutoff_measurable
        coefficient_measurable coefficient_tilde_measurable])
  note left_parts =
    left_data[unfolded slp_left_neumann_joint_geometric_data_def]
  note C_left_positive = conjunct1[OF left_parts]
  note left_after_C = conjunct2[OF left_parts]
  note CV_left_positive = conjunct1[OF left_after_C]
  note left_after_CV = conjunct2[OF left_after_C]
  note T_left_lower = conjunct1[OF left_after_CV]
  note left_universal = conjunct2[OF left_after_CV]
  note right_parts =
    right_data[unfolded slp_right_neumann_joint_geometric_data_def]
  note C_right_positive = conjunct1[OF right_parts]
  note right_after_C = conjunct2[OF right_parts]
  note CV_right_positive = conjunct1[OF right_after_C]
  note right_after_CV = conjunct2[OF right_after_C]
  note right_universal = conjunct2[OF right_after_CV]
  have tau_nonnegative: "0 \<le> tau"
    using T_left_lower tau_left by linarith
  have rho_left_upper:
      "CV_left * tau powr (-(1 - 1 / p) + epsilon) \<le> 1 / 2"
    using left_universal[rule_format, OF tau_left]
    by (simp only: Let_def)
  have rho_right_upper:
      "CV_right * tau powr (-(1 - 1 / p) + epsilon) \<le> 1 / 2"
    using right_universal[rule_format, OF tau_right]
    by (simp only: Let_def)
  have rho_left_nonnegative:
      "0 \<le> CV_left * tau powr (-(1 - 1 / p) + epsilon)"
    by (rule mult_nonneg_nonneg)
      (use CV_left_positive in linarith, rule powr_ge_zero)
  have rho_right_nonnegative:
      "0 \<le> CV_right * tau powr (-(1 - 1 / p) + epsilon)"
    by (rule mult_nonneg_nonneg)
      (use CV_right_positive in linarith, rule powr_ge_zero)
  have left_denominator_positive:
      "0 < 1 - CV_left * tau powr (-(1 - 1 / p) + epsilon)"
    using rho_left_upper by linarith
  have right_denominator_positive:
      "0 < 1 - CV_right * tau powr (-(1 - 1 / p) + epsilon)"
    using rho_right_upper by linarith
  have coefficient_norm_nonnegative:
      "0 \<le> aim_complex_lp_norm p coefficient"
    by (simp add: aim_complex_lp_norm_def)
  have coefficient_tilde_norm_nonnegative:
      "0 \<le> aim_complex_lp_norm p coefficient_tilde"
    by (simp add: aim_complex_lp_norm_def)
  have left_base_nonnegative:
      "0 \<le> C_left * tau powr (-(1 - 1 / p) + epsilon) *
        (aim_complex_lp_norm p coefficient +
          norm (slp_dbar_inverse coefficient c))" for c
    apply (intro mult_nonneg_nonneg add_nonneg_nonneg)
    subgoal using C_left_positive by linarith
    subgoal by (rule powr_ge_zero)
    subgoal by (rule coefficient_norm_nonnegative)
    subgoal by (rule norm_ge_zero)
    done
  have right_base_nonnegative:
      "0 \<le> C_right * tau powr (-(1 - 1 / p) + epsilon) *
        (aim_complex_lp_norm p coefficient_tilde +
          norm (slp_partial_inverse coefficient_tilde c))" for c
    apply (intro mult_nonneg_nonneg add_nonneg_nonneg)
    subgoal using C_right_positive by linarith
    subgoal by (rule powr_ge_zero)
    subgoal by (rule coefficient_tilde_norm_nonnegative)
    subgoal by (rule norm_ge_zero)
    done
  have left_prefix_nonnegative:
      "0 \<le> (C_left * tau powr (-(1 - 1 / p) + epsilon) *
        (aim_complex_lp_norm p coefficient +
          norm (slp_dbar_inverse coefficient c))) /
        (1 - CV_left * tau powr (-(1 - 1 / p) + epsilon))" for c
    by (rule divide_nonneg_pos[OF left_base_nonnegative
          left_denominator_positive])
  have right_prefix_nonnegative:
      "0 \<le> (C_right * tau powr (-(1 - 1 / p) + epsilon) *
        (aim_complex_lp_norm p coefficient_tilde +
          norm (slp_partial_inverse coefficient_tilde c))) /
        (1 - CV_right * tau powr (-(1 - 1 / p) + epsilon))" for c
    by (rule divide_nonneg_pos[OF right_base_nonnegative
          right_denominator_positive])
  have rho_left_power_nonnegative:
      "0 \<le> (CV_left * tau powr (-(1 - 1 / p) + epsilon)) ^ N"
    by (rule zero_le_power[OF rho_left_nonnegative])
  have rho_right_power_nonnegative:
      "0 \<le> (CV_right * tau powr (-(1 - 1 / p) + epsilon)) ^ M"
    by (rule zero_le_power[OF rho_right_nonnegative])
  have left_tail_nonnegative:
      "0 \<le> (C_left * tau powr (-(1 - 1 / p) + epsilon) *
        (aim_complex_lp_norm p coefficient +
          norm (slp_dbar_inverse coefficient c))) *
        (CV_left * tau powr (-(1 - 1 / p) + epsilon)) ^ N /
        (1 - CV_left * tau powr (-(1 - 1 / p) + epsilon))" for c
    by (rule divide_nonneg_pos[OF
          mult_nonneg_nonneg[OF left_base_nonnegative
            rho_left_power_nonnegative]
          left_denominator_positive])
  have right_tail_nonnegative:
      "0 \<le> (C_right * tau powr (-(1 - 1 / p) + epsilon) *
        (aim_complex_lp_norm p coefficient_tilde +
          norm (slp_partial_inverse coefficient_tilde c))) *
        (CV_right * tau powr (-(1 - 1 / p) + epsilon)) ^ M /
        (1 - CV_right * tau powr (-(1 - 1 / p) + epsilon))" for c
    by (rule divide_nonneg_pos[OF
          mult_nonneg_nonneg[OF right_base_nonnegative
            rho_right_power_nonnegative]
          right_denominator_positive])
  have g_nonnegative_at: "0 \<le> ?g c" for c
    unfolding slp_common_cgo_born_geometric_majorant_def
    by (intro add_nonneg_nonneg mult_nonneg_nonneg left_tail_nonnegative
          right_tail_nonnegative left_prefix_nonnegative
          right_prefix_nonnegative)
  have g_nonnegative:
      "AE c in (lborel :: slp_point measure). 0 \<le> ?g c"
    by (simp add: g_nonnegative_at)
  note pair_bound_all =
    slp_common_cgo_born_neumann_remainder_geometric_bound_AE[
      OF left_data right_data tau_left tau_right]
  have pair_bound:
      "AE pair in lborel \<Otimes>\<^sub>M lborel.
        fst pair \<in> centers \<longrightarrow>
          norm (slp_cgo_born_neumann_remainder X N M tau (fst pair)
            cutoff coefficient coefficient_tilde (snd pair)) \<le>
          ?g (fst pair)"
    unfolding slp_common_cgo_born_geometric_majorant_def
    using pair_bound_all
    by eventually_elim blast
  have majorant_integrable:
      "integrable lborel (\<lambda>c. norm (phi c) * ?g c)"
    using slp_common_cgo_born_tested_geometric_majorant_integrable[
      OF p_lower p_upper coefficient_lp coefficient_tilde_lp phi_test_UNIV,
      where N=N and M=M and epsilon=epsilon and C_left=C_left
        and CV_left=CV_left and C_right=C_right and CV_right=CV_right
        and tau=tau]
    unfolding slp_common_cgo_born_geometric_majorant_def .
  note core = slp_product_AE_root_integral_domination[
    OF Q_integrable weighted_joint_measurable outer_measurable center_support
      g_nonnegative pair_bound majorant_integrable]
  have nested_integrable:
      "integrable lborel (\<lambda>c. phi c * integral\<^sup>L lborel (\<lambda>z. Q z *
        slp_cgo_born_neumann_remainder
          X N M tau c cutoff coefficient coefficient_tilde z))"
    by (rule conjunct1[OF core])
  have nested_bound:
      "norm (integral\<^sup>L lborel (\<lambda>c. phi c * integral\<^sup>L lborel
        (\<lambda>z. Q z * slp_cgo_born_neumann_remainder
          X N M tau c cutoff coefficient coefficient_tilde z))) \<le>
       (integral\<^sup>L lborel (\<lambda>c. norm (phi c) * ?g c)) *
       (integral\<^sup>L lborel (\<lambda>z. norm (Q z)))"
    by (rule conjunct2[OF core])
  have factor_nonnegative: "0 \<le> tau / pi"
    by (rule divide_nonneg_pos[OF tau_nonnegative pi_gt_zero])
  have factor_norm:
      "norm ((of_real tau * inverse (of_real pi)) :: complex) = tau / pi"
    using tau_nonnegative
    by (simp only: norm_mult norm_of_real norm_inverse abs_of_nonneg
          abs_of_pos pi_gt_zero divide_inverse)
  show ?thesis
    unfolding slp_cgo_born_tested_neumann_remainder_functional_def
    apply (rule conjI)
    subgoal by (rule nested_integrable)
    subgoal
      apply (subst norm_mult)
      apply (simp only: factor_norm)
      apply (simp only: mult.assoc)
      by (rule mult_left_mono[OF nested_bound factor_nonnegative])
    done
qed

end

end
