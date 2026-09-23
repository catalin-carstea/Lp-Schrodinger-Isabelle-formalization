theory Inverse_Schrodinger_Lp_Exact_Neumann_Iterate_Bridge
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Right_Neumann_Iterate"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Neumann_Iterates"
begin

section \<open>Exact recursive coefficients as abstract Neumann iterates\<close>

definition slp_left_neumann_base ::
    "real \<Rightarrow> slp_point \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      slp_cauchy_orientation \<Rightarrow> slp_point \<Rightarrow> complex"
where
  "slp_left_neumann_base tau center cutoff potential orientation =
    slp_partial_psi_inverse tau center
      (\<lambda>terminal. cutoff terminal *
        (slp_cauchy_transform orientation potential terminal -
          slp_cauchy_transform orientation potential center))"

definition slp_left_neumann_step ::
    "real \<Rightarrow> slp_point \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow> slp_point \<Rightarrow> complex"
where
  "slp_left_neumann_step tau center cutoff potential f =
    slp_partial_psi_inverse tau center
      (\<lambda>pos. cutoff pos *
        slp_dbar_psi_inverse tau center
          (\<lambda>neg. potential neg * f neg) pos)"

lemma slp_left_neumann_iterate_zero_eq_base:
  "slp_left_neumann_iterate 0 tau center cutoff potential orientation =
    slp_left_neumann_base tau center cutoff potential orientation"
  by (simp only: slp_left_neumann_iterate_zero slp_left_neumann_base_def)

lemma slp_left_neumann_iterate_Suc_eq_step:
  "slp_left_neumann_iterate (Suc n) tau center cutoff potential orientation =
    slp_left_neumann_step tau center cutoff potential
      (slp_left_neumann_iterate n tau center cutoff potential orientation)"
  by (simp only: slp_left_neumann_iterate_Suc slp_left_neumann_step_def)

theorem slp_left_neumann_iterate_eq_abstract:
  "slp_left_neumann_iterate n tau center cutoff potential orientation =
    slp_neumann_iterate
      (slp_left_neumann_step tau center cutoff potential)
      (slp_left_neumann_base tau center cutoff potential orientation) n"
proof (induction n)
  case 0
  show ?case
    by (simp only: slp_left_neumann_iterate_zero_eq_base
        slp_neumann_iterate_zero)
next
  case (Suc n)
  show ?case
    by (simp only: slp_left_neumann_iterate_Suc_eq_step Suc.IH
        slp_neumann_iterate_Suc)
qed

definition slp_right_neumann_base ::
    "real \<Rightarrow> slp_point \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      slp_cauchy_orientation \<Rightarrow> slp_point \<Rightarrow> complex"
where
  "slp_right_neumann_base tau center cutoff potential orientation =
    slp_dbar_psi_inverse (- tau) center
      (\<lambda>terminal. cutoff terminal *
        (slp_cauchy_transform orientation potential terminal -
          slp_cauchy_transform orientation potential center))"

definition slp_right_neumann_step ::
    "real \<Rightarrow> slp_point \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow> slp_point \<Rightarrow> complex"
where
  "slp_right_neumann_step tau center cutoff potential f =
    slp_dbar_psi_inverse (- tau) center
      (\<lambda>pos. cutoff pos *
        slp_partial_psi_inverse (- tau) center
          (\<lambda>neg. potential neg * f neg) pos)"

lemma slp_right_neumann_iterate_zero_eq_base:
  "slp_right_neumann_iterate 0 tau center cutoff potential orientation =
    slp_right_neumann_base tau center cutoff potential orientation"
  by (simp only: slp_right_neumann_iterate_zero slp_right_neumann_base_def)

lemma slp_right_neumann_iterate_Suc_eq_step:
  "slp_right_neumann_iterate (Suc n) tau center cutoff potential orientation =
    slp_right_neumann_step tau center cutoff potential
      (slp_right_neumann_iterate n tau center cutoff potential orientation)"
  by (simp only: slp_right_neumann_iterate_Suc slp_right_neumann_step_def)

theorem slp_right_neumann_iterate_eq_abstract:
  "slp_right_neumann_iterate n tau center cutoff potential orientation =
    slp_neumann_iterate
      (slp_right_neumann_step tau center cutoff potential)
      (slp_right_neumann_base tau center cutoff potential orientation) n"
proof (induction n)
  case 0
  show ?case
    by (simp only: slp_right_neumann_iterate_zero_eq_base
        slp_neumann_iterate_zero)
next
  case (Suc n)
  show ?case
    by (simp only: slp_right_neumann_iterate_Suc_eq_step Suc.IH
        slp_neumann_iterate_Suc)
qed

end
