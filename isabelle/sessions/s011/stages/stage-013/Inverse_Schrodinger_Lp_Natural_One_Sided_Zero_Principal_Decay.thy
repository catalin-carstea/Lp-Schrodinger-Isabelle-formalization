theory Inverse_Schrodinger_Lp_Natural_One_Sided_Zero_Principal_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_One_Sided_Positive_Principal_Decay"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Zero-order one-sided principal identity and decay\<close>

lemma slp_natural_one_sided_zero_principal_amplitudes_equal:
  "slp_natural_one_sided_weighted_amplitude 0 Q cutoff q T H z =
    slp_natural_one_sided_weighted_amplitude 0 Q cutoff q (\<lambda>_. 1)
      (\<lambda>u. H u * T u) z"
  unfolding slp_natural_one_sided_weighted_amplitude_def Let_def
  by (simp add: slp_left_branch_complex_terminal_def algebra_simps)

theorem slp_natural_one_sided_zero_principal_decay:
  fixes Q cutoff q A phi :: slp_scalar_field
  shows "let P = PiM {..<0} (\<lambda>_::nat. (lborel :: slp_point measure));
             MJ = ((P \<Otimes>\<^sub>M P) \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M lborel;
             ps = (\<lambda>z. map (\<lambda>k.
               (fst (fst (fst z)) k, snd (fst (fst z)) k)) [0..<0]);
             residual = (\<lambda>z. slp_left_branch_residual (ps z) (snd (fst z)))
    in ((\<lambda>omega::real. integral\<^sup>L MJ
      (\<lambda>z. exp (\<i> * of_real (omega * residual z)) *
        (slp_natural_one_sided_weighted_amplitude 0 Q cutoff q A phi z -
         slp_natural_one_sided_weighted_amplitude 0 Q cutoff q (\<lambda>_. 1)
           (\<lambda>u. phi u * A u) z))) \<longlongrightarrow> 0) at_top"
proof -
  have bracket_zero:
    "slp_natural_one_sided_weighted_amplitude 0 Q cutoff q A phi z -
      slp_natural_one_sided_weighted_amplitude 0 Q cutoff q (\<lambda>_. 1)
        (\<lambda>u. phi u * A u) z = 0" for z
  proof -
    have amplitudes_equal:
      "slp_natural_one_sided_weighted_amplitude 0 Q cutoff q A phi z =
        slp_natural_one_sided_weighted_amplitude 0 Q cutoff q (\<lambda>_. 1)
          (\<lambda>u. phi u * A u) z"
      unfolding slp_natural_one_sided_weighted_amplitude_def Let_def
      by (simp add: slp_left_branch_complex_terminal_def algebra_simps)
    show ?thesis using amplitudes_equal by simp
  qed
  show ?thesis
    unfolding Let_def by (simp add: bracket_zero)
qed

end
