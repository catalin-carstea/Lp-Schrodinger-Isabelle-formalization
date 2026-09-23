theory Inverse_Schrodinger_Lp_Common_CGO_Born_Remainder_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_Common_CGO_Joint_Series_Tails"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_Common_CGO_Joint_Partial_Sums"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_CGO_Born_Remainder_Norm"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Common-CGO nonlinear remainder majorant\<close>

theorem slp_common_cgo_born_neumann_remainder_geometric_bound_AE:
  fixes p epsilon C_left CV_left T_left :: real
    and C_right CV_right T_right tau :: real
    and X centers :: "slp_point set"
    and cutoff coefficient coefficient_tilde :: slp_scalar_field
  assumes left_data:
      "slp_left_neumann_joint_geometric_data p epsilon X centers cutoff
        coefficient C_left CV_left T_left"
    and right_data:
      "slp_right_neumann_joint_geometric_data p epsilon X centers cutoff
        coefficient_tilde C_right CV_right T_right"
    and tau_left: "T_left \<le> tau"
    and tau_right: "T_right \<le> tau"
  shows
    "AE pair in lborel \<Otimes>\<^sub>M lborel.
      fst pair \<in> centers \<longrightarrow> (\<forall>N M.
        norm (slp_cgo_born_neumann_remainder X N M tau (fst pair) cutoff
          coefficient coefficient_tilde (snd pair)) \<le>
        (C_left * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient +
            norm (slp_dbar_inverse coefficient (fst pair)))) *
          (CV_left * tau powr (-(1 - 1 / p) + epsilon)) ^ N /
          (1 - CV_left * tau powr (-(1 - 1 / p) + epsilon)) +
        (C_right * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient_tilde +
            norm (slp_partial_inverse coefficient_tilde (fst pair)))) *
          (CV_right * tau powr (-(1 - 1 / p) + epsilon)) ^ M /
          (1 - CV_right * tau powr (-(1 - 1 / p) + epsilon)) +
        ((C_left * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient +
            norm (slp_dbar_inverse coefficient (fst pair)))) /
          (1 - CV_left * tau powr (-(1 - 1 / p) + epsilon))) *
        ((C_right * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient_tilde +
            norm (slp_partial_inverse coefficient_tilde (fst pair)))) *
          (CV_right * tau powr (-(1 - 1 / p) + epsilon)) ^ M /
          (1 - CV_right * tau powr (-(1 - 1 / p) + epsilon))) +
        ((C_left * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient +
            norm (slp_dbar_inverse coefficient (fst pair)))) *
          (CV_left * tau powr (-(1 - 1 / p) + epsilon)) ^ N /
          (1 - CV_left * tau powr (-(1 - 1 / p) + epsilon))) *
        ((C_right * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient_tilde +
            norm (slp_partial_inverse coefficient_tilde (fst pair)))) /
          (1 - CV_right * tau powr (-(1 - 1 / p) + epsilon))) +
        ((C_left * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient +
            norm (slp_dbar_inverse coefficient (fst pair)))) *
          (CV_left * tau powr (-(1 - 1 / p) + epsilon)) ^ N /
          (1 - CV_left * tau powr (-(1 - 1 / p) + epsilon))) *
        ((C_right * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient_tilde +
            norm (slp_partial_inverse coefficient_tilde (fst pair)))) *
          (CV_right * tau powr (-(1 - 1 / p) + epsilon)) ^ M /
          (1 - CV_right * tau powr (-(1 - 1 / p) + epsilon))))"
proof -
  note left_tails =
    slp_left_neumann_joint_geometric_data_tail_AE[OF left_data tau_left]
  note right_tails =
    slp_right_neumann_joint_geometric_data_tail_AE[OF right_data tau_right]
  note left_prefixes =
    slp_left_neumann_joint_geometric_data_partial_sum_AE[
      OF left_data tau_left]
  note right_prefixes =
    slp_right_neumann_joint_geometric_data_partial_sum_AE[
      OF right_data tau_right]
  show ?thesis
    using left_tails right_tails left_prefixes right_prefixes
  proof eventually_elim
    fix pair :: "slp_point \<times> slp_point"
    assume left_tail_bounds:
      "fst pair \<in> centers \<longrightarrow> (\<forall>N.
        norm (slp_left_neumann_series_tail X N tau (fst pair) cutoff
          coefficient (snd pair)) \<le>
        (C_left * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient +
            norm (slp_dbar_inverse coefficient (fst pair)))) *
        (CV_left * tau powr (-(1 - 1 / p) + epsilon)) ^ N /
        (1 - CV_left * tau powr (-(1 - 1 / p) + epsilon)))"
      and right_tail_bounds:
      "fst pair \<in> centers \<longrightarrow> (\<forall>M.
        norm (slp_right_neumann_series_tail X M tau (fst pair) cutoff
          coefficient_tilde (snd pair)) \<le>
        (C_right * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient_tilde +
            norm (slp_partial_inverse coefficient_tilde (fst pair)))) *
        (CV_right * tau powr (-(1 - 1 / p) + epsilon)) ^ M /
        (1 - CV_right * tau powr (-(1 - 1 / p) + epsilon)))"
      and left_prefix_bounds:
      "fst pair \<in> centers \<longrightarrow> (\<forall>N.
        norm (slp_left_neumann_partial_sum X N tau (fst pair) cutoff
          coefficient (snd pair)) \<le>
        (C_left * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient +
            norm (slp_dbar_inverse coefficient (fst pair)))) /
        (1 - CV_left * tau powr (-(1 - 1 / p) + epsilon)))"
      and right_prefix_bounds:
      "fst pair \<in> centers \<longrightarrow> (\<forall>M.
        norm (slp_right_neumann_partial_sum X M tau (fst pair) cutoff
          coefficient_tilde (snd pair)) \<le>
        (C_right * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient_tilde +
            norm (slp_partial_inverse coefficient_tilde (fst pair)))) /
        (1 - CV_right * tau powr (-(1 - 1 / p) + epsilon)))"
    show
      "fst pair \<in> centers \<longrightarrow> (\<forall>N M.
        norm (slp_cgo_born_neumann_remainder X N M tau (fst pair) cutoff
          coefficient coefficient_tilde (snd pair)) \<le>
        (C_left * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient +
            norm (slp_dbar_inverse coefficient (fst pair)))) *
          (CV_left * tau powr (-(1 - 1 / p) + epsilon)) ^ N /
          (1 - CV_left * tau powr (-(1 - 1 / p) + epsilon)) +
        (C_right * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient_tilde +
            norm (slp_partial_inverse coefficient_tilde (fst pair)))) *
          (CV_right * tau powr (-(1 - 1 / p) + epsilon)) ^ M /
          (1 - CV_right * tau powr (-(1 - 1 / p) + epsilon)) +
        ((C_left * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient +
            norm (slp_dbar_inverse coefficient (fst pair)))) /
          (1 - CV_left * tau powr (-(1 - 1 / p) + epsilon))) *
        ((C_right * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient_tilde +
            norm (slp_partial_inverse coefficient_tilde (fst pair)))) *
          (CV_right * tau powr (-(1 - 1 / p) + epsilon)) ^ M /
          (1 - CV_right * tau powr (-(1 - 1 / p) + epsilon))) +
        ((C_left * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient +
            norm (slp_dbar_inverse coefficient (fst pair)))) *
          (CV_left * tau powr (-(1 - 1 / p) + epsilon)) ^ N /
          (1 - CV_left * tau powr (-(1 - 1 / p) + epsilon))) *
        ((C_right * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient_tilde +
            norm (slp_partial_inverse coefficient_tilde (fst pair)))) /
          (1 - CV_right * tau powr (-(1 - 1 / p) + epsilon))) +
        ((C_left * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient +
            norm (slp_dbar_inverse coefficient (fst pair)))) *
          (CV_left * tau powr (-(1 - 1 / p) + epsilon)) ^ N /
          (1 - CV_left * tau powr (-(1 - 1 / p) + epsilon))) *
        ((C_right * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient_tilde +
            norm (slp_partial_inverse coefficient_tilde (fst pair)))) *
          (CV_right * tau powr (-(1 - 1 / p) + epsilon)) ^ M /
          (1 - CV_right * tau powr (-(1 - 1 / p) + epsilon))))"
    proof
      assume center_in: "fst pair \<in> centers"
      show "\<forall>N M.
        norm (slp_cgo_born_neumann_remainder X N M tau (fst pair) cutoff
          coefficient coefficient_tilde (snd pair)) \<le>
        (C_left * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient +
            norm (slp_dbar_inverse coefficient (fst pair)))) *
          (CV_left * tau powr (-(1 - 1 / p) + epsilon)) ^ N /
          (1 - CV_left * tau powr (-(1 - 1 / p) + epsilon)) +
        (C_right * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient_tilde +
            norm (slp_partial_inverse coefficient_tilde (fst pair)))) *
          (CV_right * tau powr (-(1 - 1 / p) + epsilon)) ^ M /
          (1 - CV_right * tau powr (-(1 - 1 / p) + epsilon)) +
        ((C_left * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient +
            norm (slp_dbar_inverse coefficient (fst pair)))) /
          (1 - CV_left * tau powr (-(1 - 1 / p) + epsilon))) *
        ((C_right * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient_tilde +
            norm (slp_partial_inverse coefficient_tilde (fst pair)))) *
          (CV_right * tau powr (-(1 - 1 / p) + epsilon)) ^ M /
          (1 - CV_right * tau powr (-(1 - 1 / p) + epsilon))) +
        ((C_left * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient +
            norm (slp_dbar_inverse coefficient (fst pair)))) *
          (CV_left * tau powr (-(1 - 1 / p) + epsilon)) ^ N /
          (1 - CV_left * tau powr (-(1 - 1 / p) + epsilon))) *
        ((C_right * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient_tilde +
            norm (slp_partial_inverse coefficient_tilde (fst pair)))) /
          (1 - CV_right * tau powr (-(1 - 1 / p) + epsilon))) +
        ((C_left * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient +
            norm (slp_dbar_inverse coefficient (fst pair)))) *
          (CV_left * tau powr (-(1 - 1 / p) + epsilon)) ^ N /
          (1 - CV_left * tau powr (-(1 - 1 / p) + epsilon))) *
        ((C_right * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient_tilde +
            norm (slp_partial_inverse coefficient_tilde (fst pair)))) *
          (CV_right * tau powr (-(1 - 1 / p) + epsilon)) ^ M /
          (1 - CV_right * tau powr (-(1 - 1 / p) + epsilon)))"
      proof (intro allI)
        fix N M
        note left_prefix =
          left_prefix_bounds[rule_format, OF center_in, of N]
        note left_tail =
          left_tail_bounds[rule_format, OF center_in, of N]
        note right_prefix =
          right_prefix_bounds[rule_format, OF center_in, of M]
        note right_tail =
          right_tail_bounds[rule_format, OF center_in, of M]
        show
          "norm (slp_cgo_born_neumann_remainder X N M tau (fst pair)
            cutoff coefficient coefficient_tilde (snd pair)) \<le>
          (C_left * tau powr (-(1 - 1 / p) + epsilon) *
            (aim_complex_lp_norm p coefficient +
              norm (slp_dbar_inverse coefficient (fst pair)))) *
            (CV_left * tau powr (-(1 - 1 / p) + epsilon)) ^ N /
            (1 - CV_left * tau powr (-(1 - 1 / p) + epsilon)) +
          (C_right * tau powr (-(1 - 1 / p) + epsilon) *
            (aim_complex_lp_norm p coefficient_tilde +
              norm (slp_partial_inverse coefficient_tilde (fst pair)))) *
            (CV_right * tau powr (-(1 - 1 / p) + epsilon)) ^ M /
            (1 - CV_right * tau powr (-(1 - 1 / p) + epsilon)) +
          ((C_left * tau powr (-(1 - 1 / p) + epsilon) *
            (aim_complex_lp_norm p coefficient +
              norm (slp_dbar_inverse coefficient (fst pair)))) /
            (1 - CV_left * tau powr (-(1 - 1 / p) + epsilon))) *
          ((C_right * tau powr (-(1 - 1 / p) + epsilon) *
            (aim_complex_lp_norm p coefficient_tilde +
              norm (slp_partial_inverse coefficient_tilde (fst pair)))) *
            (CV_right * tau powr (-(1 - 1 / p) + epsilon)) ^ M /
            (1 - CV_right * tau powr (-(1 - 1 / p) + epsilon))) +
          ((C_left * tau powr (-(1 - 1 / p) + epsilon) *
            (aim_complex_lp_norm p coefficient +
              norm (slp_dbar_inverse coefficient (fst pair)))) *
            (CV_left * tau powr (-(1 - 1 / p) + epsilon)) ^ N /
            (1 - CV_left * tau powr (-(1 - 1 / p) + epsilon))) *
          ((C_right * tau powr (-(1 - 1 / p) + epsilon) *
            (aim_complex_lp_norm p coefficient_tilde +
              norm (slp_partial_inverse coefficient_tilde (fst pair)))) /
            (1 - CV_right * tau powr (-(1 - 1 / p) + epsilon))) +
          ((C_left * tau powr (-(1 - 1 / p) + epsilon) *
            (aim_complex_lp_norm p coefficient +
              norm (slp_dbar_inverse coefficient (fst pair)))) *
            (CV_left * tau powr (-(1 - 1 / p) + epsilon)) ^ N /
            (1 - CV_left * tau powr (-(1 - 1 / p) + epsilon))) *
          ((C_right * tau powr (-(1 - 1 / p) + epsilon) *
            (aim_complex_lp_norm p coefficient_tilde +
              norm (slp_partial_inverse coefficient_tilde (fst pair)))) *
            (CV_right * tau powr (-(1 - 1 / p) + epsilon)) ^ M /
            (1 - CV_right * tau powr (-(1 - 1 / p) + epsilon)))"
          by (rule slp_cgo_born_neumann_remainder_norm_le[
                OF left_prefix left_tail right_prefix right_tail])
      qed
    qed
  qed
qed

end
