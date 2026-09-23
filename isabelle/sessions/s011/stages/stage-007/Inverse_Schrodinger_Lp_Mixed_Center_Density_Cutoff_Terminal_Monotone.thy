theory Inverse_Schrodinger_Lp_Mixed_Center_Density_Cutoff_Terminal_Monotone
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Density_Terminal_Monotone"
begin

section \<open>Cutoff-weighted terminal monotonicity\<close>

theorem slp_positive_output_density_cutoff_terminal_mono:
  assumes terminal_mono:
      "\<And>x. ennreal (cmod (cutoff x)) * terminal_weight x \<le>
        ennreal (cmod (cutoff x)) * terminal_majorant x"
  shows
    "slp_positive_output_density R cutoff potential terminal_weight n origin
        target \<le>
      slp_positive_output_density R cutoff potential terminal_majorant n
        origin target"
proof (induction n arbitrary: origin target)
  case 0
  note base = terminal_mono[of target]
  show ?case
  proof -
    have
      "ennreal (inverse pi) *
          ennreal (slp_localized_cauchy_kernel R (origin - target)) *
          ennreal (cmod (cutoff target)) * terminal_weight target =
        (ennreal (inverse pi) *
          ennreal (slp_localized_cauchy_kernel R (origin - target))) *
          (ennreal (cmod (cutoff target)) * terminal_weight target)"
      by (simp add: mult.assoc)
    also have "... \<le>
        (ennreal (inverse pi) *
          ennreal (slp_localized_cauchy_kernel R (origin - target))) *
          (ennreal (cmod (cutoff target)) * terminal_majorant target)"
      by (rule mult_left_mono[OF base], simp)
    also have "... =
        ennreal (inverse pi) *
          ennreal (slp_localized_cauchy_kernel R (origin - target)) *
          ennreal (cmod (cutoff target)) * terminal_majorant target"
      by (simp add: mult.assoc)
    finally show ?thesis
      unfolding slp_positive_output_density.simps .
  qed
next
  case (Suc n)
  show ?case
    unfolding slp_positive_output_density.simps
    apply (rule mult_left_mono)
    apply (rule nn_integral_mono)
    apply (rule nn_integral_mono)
    apply (rule mult_left_mono)
    subgoal by (rule Suc.IH)
    by simp_all
qed

theorem slp_left_positive_output_density_cutoff_terminal_mono:
  assumes terminal_mono:
      "\<And>x. ennreal (cmod (cutoff x)) * terminal_weight x \<le>
        ennreal (cmod (cutoff x)) * terminal_majorant x"
  shows
    "slp_left_positive_output_density R cutoff potential terminal_weight n
        origin target \<le>
      slp_left_positive_output_density R cutoff potential terminal_majorant n
        origin target"
  unfolding slp_left_positive_output_density_def
  by (rule slp_positive_output_density_cutoff_terminal_mono[OF
        terminal_mono])

theorem slp_right_positive_output_density_cutoff_terminal_mono:
  assumes terminal_mono:
      "\<And>x. ennreal (cmod (cutoff x)) * terminal_weight x \<le>
        ennreal (cmod (cutoff x)) * terminal_majorant x"
  shows
    "slp_right_positive_output_density R cutoff potential terminal_weight n
        origin target \<le>
      slp_right_positive_output_density R cutoff potential terminal_majorant n
        origin target"
  unfolding slp_right_positive_output_density_def
  by (rule slp_positive_output_density_cutoff_terminal_mono[OF
        terminal_mono])

theorem slp_mixed_center_density_cutoff_terminal_mono:
  assumes left_terminal_mono:
      "\<And>x. ennreal (cmod (cutoff x)) * left_terminal_weight x \<le>
        ennreal (cmod (cutoff x)) * left_terminal_majorant x"
    and right_terminal_mono:
      "\<And>x. ennreal (cmod (cutoff x)) * right_terminal_weight x \<le>
        ennreal (cmod (cutoff x)) * right_terminal_majorant x"
  shows
    "slp_mixed_center_density R cutoff left_potential right_potential
        left_terminal_weight right_terminal_weight left_order right_order
        root_weight center \<le>
      slp_mixed_center_density R cutoff left_potential right_potential
        left_terminal_majorant right_terminal_majorant left_order right_order
        root_weight center"
proof -
  have left_mono:
      "slp_left_positive_output_density R cutoff left_potential
          left_terminal_weight left_order root target \<le>
        slp_left_positive_output_density R cutoff left_potential
          left_terminal_majorant left_order root target"
    for root target
    by (rule slp_left_positive_output_density_cutoff_terminal_mono[OF
          left_terminal_mono])
  have right_mono:
      "slp_right_positive_output_density R cutoff right_potential
          right_terminal_weight right_order root target \<le>
        slp_right_positive_output_density R cutoff right_potential
          right_terminal_majorant right_order root target"
    for root target
    by (rule slp_right_positive_output_density_cutoff_terminal_mono[OF
          right_terminal_mono])
  show ?thesis
    unfolding slp_mixed_center_density_def
    apply (rule nn_integral_mono)
    apply (rule nn_integral_mono)
    apply (rule mult_mono)
    subgoal by (rule mult_left_mono[OF left_mono], simp)
    subgoal by (rule right_mono)
    subgoal by simp
    subgoal by simp
    done
qed

end
