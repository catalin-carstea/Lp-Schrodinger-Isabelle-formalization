theory Inverse_Schrodinger_Lp_Common_CGO_Joint_Series_Tails
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_Joint_Geometric_Series_Tail"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_CGO_Born_Finite_Expansion"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Literal joint Neumann tails from the common geometric data\<close>

theorem slp_left_neumann_joint_geometric_data_tail_AE:
  fixes p epsilon C CV T tau :: real
    and X centers :: "slp_point set"
    and cutoff coefficient :: slp_scalar_field
  assumes data:
      "slp_left_neumann_joint_geometric_data
        p epsilon X centers cutoff coefficient C CV T"
    and tau_large: "T \<le> tau"
  shows
    "AE pair in lborel \<Otimes>\<^sub>M lborel.
      fst pair \<in> centers \<longrightarrow> (\<forall>N.
        norm (slp_left_neumann_series_tail X N tau (fst pair)
          cutoff coefficient (snd pair)) \<le>
        (C * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient +
            norm (slp_dbar_inverse coefficient (fst pair)))) *
        (CV * tau powr (-(1 - 1 / p) + epsilon)) ^ N /
        (1 - CV * tau powr (-(1 - 1 / p) + epsilon)))"
proof -
  note data_parts =
    data[unfolded slp_left_neumann_joint_geometric_data_def]
  note C_positive = conjunct1[OF data_parts]
  note after_C = conjunct2[OF data_parts]
  note CV_positive = conjunct1[OF after_C]
  note after_CV = conjunct2[OF after_C]
  note universal = conjunct2[OF after_CV]
  let ?rho = "CV * tau powr (-(1 - 1 / p) + epsilon)"
  let ?majorant = "\<lambda>c.
    if c \<in> centers
    then C * tau powr (-(1 - 1 / p) + epsilon) *
      (aim_complex_lp_norm p coefficient +
        norm (slp_dbar_inverse coefficient c))
    else 0"
  let ?U = "\<lambda>j pair :: slp_point \<times> slp_point.
    if fst pair \<in> centers
    then slp_restrict_field X
      (slp_neumann_iterate
        (slp_left_neumann_step tau (fst pair) cutoff coefficient)
        (slp_left_neumann_base tau (fst pair) cutoff coefficient
          SLP_Dbar_Inverse) j) (snd pair)
    else 0"
  note tau_data = universal[rule_format, OF tau_large]
  then have rho_le: "?rho \<le> 1 / 2"
    and simultaneous:
      "AE pair in lborel \<Otimes>\<^sub>M lborel. \<forall>j.
        norm (?U j pair) \<le> ?majorant (fst pair) * ?rho ^ j"
    by (simp_all add: Let_def)
  have majorant_nonnegative: "\<And>c. 0 \<le> ?majorant c"
  proof -
    fix c :: slp_point
    show "0 \<le> ?majorant c"
    proof (cases "c \<in> centers")
      case True
      have scale_nonnegative:
          "0 \<le> C * tau powr (-(1 - 1 / p) + epsilon)"
        by (rule mult_nonneg_nonneg)
          (use C_positive in linarith, rule powr_ge_zero)
      have datum_nonnegative:
          "0 \<le> aim_complex_lp_norm p coefficient +
            norm (slp_dbar_inverse coefficient c)"
        unfolding aim_complex_lp_norm_def by simp
      show ?thesis
        using True mult_nonneg_nonneg[
          OF scale_nonnegative datum_nonnegative] by simp
    next
      case False
      then show ?thesis by simp
    qed
  qed
  have rho_nonnegative: "0 \<le> ?rho"
    using CV_positive by (simp add: less_imp_le)
  have rho_strict: "?rho < 1"
    using rho_le by linarith
  have totalized_tail:
      "AE pair in lborel \<Otimes>\<^sub>M lborel. \<forall>N.
        norm ((\<Sum>j. ?U j pair) - (\<Sum>j<N. ?U j pair)) \<le>
          ?majorant (fst pair) * ?rho ^ N / (1 - ?rho)"
    by (rule slp_variable_majorant_geometric_series_tail_AE[
          OF majorant_nonnegative rho_nonnegative rho_strict simultaneous])
  show ?thesis
    using totalized_tail
  proof eventually_elim
    fix pair :: "slp_point \<times> slp_point"
    assume tails:
      "\<forall>N. norm ((\<Sum>j. ?U j pair) - (\<Sum>j<N. ?U j pair)) \<le>
        ?majorant (fst pair) * ?rho ^ N / (1 - ?rho)"
    show
      "fst pair \<in> centers \<longrightarrow> (\<forall>N.
        norm (slp_left_neumann_series_tail X N tau (fst pair)
          cutoff coefficient (snd pair)) \<le>
        (C * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient +
            norm (slp_dbar_inverse coefficient (fst pair)))) *
        ?rho ^ N / (1 - ?rho))"
    proof
      assume center_in: "fst pair \<in> centers"
      show
        "\<forall>N. norm (slp_left_neumann_series_tail X N tau (fst pair)
          cutoff coefficient (snd pair)) \<le>
        (C * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient +
            norm (slp_dbar_inverse coefficient (fst pair)))) *
        ?rho ^ N / (1 - ?rho)"
      proof
        fix N
        show
          "norm (slp_left_neumann_series_tail X N tau (fst pair)
            cutoff coefficient (snd pair)) \<le>
          (C * tau powr (-(1 - 1 / p) + epsilon) *
            (aim_complex_lp_norm p coefficient +
              norm (slp_dbar_inverse coefficient (fst pair)))) *
          ?rho ^ N / (1 - ?rho)"
          using tails[rule_format, of N] center_in
          unfolding slp_left_neumann_series_tail_def
            slp_left_neumann_series_sum_def
            slp_left_neumann_partial_sum_def
          by simp
      qed
    qed
  qed
qed

theorem slp_right_neumann_joint_geometric_data_tail_AE:
  fixes p epsilon C CV T tau :: real
    and X centers :: "slp_point set"
    and cutoff coefficient :: slp_scalar_field
  assumes data:
      "slp_right_neumann_joint_geometric_data
        p epsilon X centers cutoff coefficient C CV T"
    and tau_large: "T \<le> tau"
  shows
    "AE pair in lborel \<Otimes>\<^sub>M lborel.
      fst pair \<in> centers \<longrightarrow> (\<forall>N.
        norm (slp_right_neumann_series_tail X N tau (fst pair)
          cutoff coefficient (snd pair)) \<le>
        (C * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient +
            norm (slp_partial_inverse coefficient (fst pair)))) *
        (CV * tau powr (-(1 - 1 / p) + epsilon)) ^ N /
        (1 - CV * tau powr (-(1 - 1 / p) + epsilon)))"
proof -
  note data_parts =
    data[unfolded slp_right_neumann_joint_geometric_data_def]
  note C_positive = conjunct1[OF data_parts]
  note after_C = conjunct2[OF data_parts]
  note CV_positive = conjunct1[OF after_C]
  note after_CV = conjunct2[OF after_C]
  note universal = conjunct2[OF after_CV]
  let ?rho = "CV * tau powr (-(1 - 1 / p) + epsilon)"
  let ?majorant = "\<lambda>c.
    if c \<in> centers
    then C * tau powr (-(1 - 1 / p) + epsilon) *
      (aim_complex_lp_norm p coefficient +
        norm (slp_partial_inverse coefficient c))
    else 0"
  let ?U = "\<lambda>j pair :: slp_point \<times> slp_point.
    if fst pair \<in> centers
    then slp_restrict_field X
      (slp_neumann_iterate
        (slp_right_neumann_step tau (fst pair) cutoff coefficient)
        (slp_right_neumann_base tau (fst pair) cutoff coefficient
          SLP_Partial_Inverse) j) (snd pair)
    else 0"
  note tau_data = universal[rule_format, OF tau_large]
  then have rho_le: "?rho \<le> 1 / 2"
    and simultaneous:
      "AE pair in lborel \<Otimes>\<^sub>M lborel. \<forall>j.
        norm (?U j pair) \<le> ?majorant (fst pair) * ?rho ^ j"
    by (simp_all add: Let_def)
  have majorant_nonnegative: "\<And>c. 0 \<le> ?majorant c"
  proof -
    fix c :: slp_point
    show "0 \<le> ?majorant c"
    proof (cases "c \<in> centers")
      case True
      have scale_nonnegative:
          "0 \<le> C * tau powr (-(1 - 1 / p) + epsilon)"
        by (rule mult_nonneg_nonneg)
          (use C_positive in linarith, rule powr_ge_zero)
      have datum_nonnegative:
          "0 \<le> aim_complex_lp_norm p coefficient +
            norm (slp_partial_inverse coefficient c)"
        unfolding aim_complex_lp_norm_def by simp
      show ?thesis
        using True mult_nonneg_nonneg[
          OF scale_nonnegative datum_nonnegative] by simp
    next
      case False
      then show ?thesis by simp
    qed
  qed
  have rho_nonnegative: "0 \<le> ?rho"
    using CV_positive by (simp add: less_imp_le)
  have rho_strict: "?rho < 1"
    using rho_le by linarith
  have totalized_tail:
      "AE pair in lborel \<Otimes>\<^sub>M lborel. \<forall>N.
        norm ((\<Sum>j. ?U j pair) - (\<Sum>j<N. ?U j pair)) \<le>
          ?majorant (fst pair) * ?rho ^ N / (1 - ?rho)"
    by (rule slp_variable_majorant_geometric_series_tail_AE[
          OF majorant_nonnegative rho_nonnegative rho_strict simultaneous])
  show ?thesis
    using totalized_tail
  proof eventually_elim
    fix pair :: "slp_point \<times> slp_point"
    assume tails:
      "\<forall>N. norm ((\<Sum>j. ?U j pair) - (\<Sum>j<N. ?U j pair)) \<le>
        ?majorant (fst pair) * ?rho ^ N / (1 - ?rho)"
    show
      "fst pair \<in> centers \<longrightarrow> (\<forall>N.
        norm (slp_right_neumann_series_tail X N tau (fst pair)
          cutoff coefficient (snd pair)) \<le>
        (C * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient +
            norm (slp_partial_inverse coefficient (fst pair)))) *
        ?rho ^ N / (1 - ?rho))"
    proof
      assume center_in: "fst pair \<in> centers"
      show
        "\<forall>N. norm (slp_right_neumann_series_tail X N tau (fst pair)
          cutoff coefficient (snd pair)) \<le>
        (C * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient +
            norm (slp_partial_inverse coefficient (fst pair)))) *
        ?rho ^ N / (1 - ?rho)"
      proof
        fix N
        show
          "norm (slp_right_neumann_series_tail X N tau (fst pair)
            cutoff coefficient (snd pair)) \<le>
          (C * tau powr (-(1 - 1 / p) + epsilon) *
            (aim_complex_lp_norm p coefficient +
              norm (slp_partial_inverse coefficient (fst pair)))) *
          ?rho ^ N / (1 - ?rho)"
          using tails[rule_format, of N] center_in
          unfolding slp_right_neumann_series_tail_def
            slp_right_neumann_series_sum_def
            slp_right_neumann_partial_sum_def
          by simp
      qed
    qed
  qed
qed

end
