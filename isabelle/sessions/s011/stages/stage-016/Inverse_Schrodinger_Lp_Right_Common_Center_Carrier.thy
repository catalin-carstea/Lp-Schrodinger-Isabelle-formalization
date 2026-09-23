theory Inverse_Schrodinger_Lp_Right_Common_Center_Carrier
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Common_Center_Carrier"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Right_Neumann_Joint_Geometric_Series"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Right_Neumann_Series_Esssup_Convergence"
begin

section \<open>Canonical totalized right series on a common center carrier\<close>

definition slp_right_neumann_joint_series_on ::
    "slp_point set \<Rightarrow> slp_point set \<Rightarrow> real \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow>
      slp_point \<times> slp_point \<Rightarrow> complex"
  where
  "slp_right_neumann_joint_series_on centers X tau cutoff coefficient =
    (\<lambda>pair. \<Sum>j.
      if fst pair \<in> centers
      then slp_restrict_field X
        (slp_neumann_iterate
          (slp_right_neumann_step tau (fst pair) cutoff coefficient)
          (slp_right_neumann_base tau (fst pair) cutoff coefficient
            SLP_Partial_Inverse) j) (snd pair)
      else 0)"

theorem slp_right_neumann_joint_series_on_fiber:
  "slp_right_neumann_joint_series_on centers X tau cutoff coefficient (c, z) =
    (if c \<in> centers
     then slp_right_neumann_series_sum X tau c cutoff coefficient z
     else 0)"
proof (cases "c \<in> centers")
  case True
  then show ?thesis
    unfolding slp_right_neumann_joint_series_on_def
      slp_right_neumann_series_sum_def
    by simp
next
  case False
  then show ?thesis
    unfolding slp_right_neumann_joint_series_on_def by simp
qed

end
