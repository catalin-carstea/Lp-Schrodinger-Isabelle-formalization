theory Inverse_Schrodinger_Lp_Natural_Right_One_Sided_Amplitude
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Right_Graph_Natural_Conjugate"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_One_Sided_Amplitude_Bound"
begin

section \<open>The exact natural right one-sided weighted amplitude\<close>

definition slp_natural_right_one_sided_weighted_amplitude ::
  "nat \<Rightarrow> slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow>
    ((((nat \<Rightarrow> slp_point) \<times> (nat \<Rightarrow> slp_point)) \<times>
      slp_point) \<times> slp_point) \<Rightarrow> complex"
where
  "slp_natural_right_one_sided_weighted_amplitude n Q cutoff q T H z =
    (let b = fst z; x = snd z;
         ps = map (\<lambda>k. (fst (fst b) k, snd (fst b) k)) [0..<n]
     in Q x *
       cnj (slp_left_branch_complex_kernel_list
         (\<lambda>y. cnj (cutoff y)) (\<lambda>y. cnj (q y))
         (\<lambda>y. cnj (T y)) ps x (snd b)) *
       H (slp_right_branch_output ps (snd b)))"

theorem slp_natural_right_one_sided_weighted_amplitude_conjugate:
  "slp_natural_right_one_sided_weighted_amplitude n Q cutoff q T H z =
    cnj (slp_natural_one_sided_weighted_amplitude n
      (\<lambda>x. cnj (Q x)) (\<lambda>x. cnj (cutoff x))
      (\<lambda>x. cnj (q x)) (\<lambda>x. cnj (T x))
      (\<lambda>x. cnj (H x)) z)"
  unfolding slp_natural_right_one_sided_weighted_amplitude_def
    slp_natural_one_sided_weighted_amplitude_def Let_def
  by (simp add: slp_left_branch_output_eq_right algebra_simps)

theorem slp_natural_right_one_sided_weighted_amplitude_norm [simp]:
  "cmod (slp_natural_right_one_sided_weighted_amplitude
      n Q cutoff q T H z) =
    cmod (slp_natural_one_sided_weighted_amplitude n
      (\<lambda>x. cnj (Q x)) (\<lambda>x. cnj (cutoff x))
      (\<lambda>x. cnj (q x)) (\<lambda>x. cnj (T x))
      (\<lambda>x. cnj (H x)) z)"
  by (simp only:
      slp_natural_right_one_sided_weighted_amplitude_conjugate complex_mod_cnj)

theorem slp_natural_right_one_sided_weighted_amplitude_integrable_iff:
  "integrable M (slp_natural_right_one_sided_weighted_amplitude
      n Q cutoff q T H) \<longleftrightarrow>
    integrable M (slp_natural_one_sided_weighted_amplitude n
      (\<lambda>x. cnj (Q x)) (\<lambda>x. cnj (cutoff x))
      (\<lambda>x. cnj (q x)) (\<lambda>x. cnj (T x))
      (\<lambda>x. cnj (H x)))"
proof -
  let ?left = "slp_natural_one_sided_weighted_amplitude n
    (\<lambda>x. cnj (Q x)) (\<lambda>x. cnj (cutoff x))
    (\<lambda>x. cnj (q x)) (\<lambda>x. cnj (T x))
    (\<lambda>x. cnj (H x))"
  have right_eq:
      "slp_natural_right_one_sided_weighted_amplitude n Q cutoff q T H =
        (\<lambda>z. cnj (?left z))"
    by (rule ext)
      (rule slp_natural_right_one_sided_weighted_amplitude_conjugate)
  show ?thesis
    unfolding right_eq
  proof
    assume right_integrable: "integrable M (\<lambda>z. cnj (?left z))"
    have twice_integrable:
        "integrable M (\<lambda>z. cnj (cnj (?left z)))"
      by (rule integrable_cnj[OF right_integrable])
    show "integrable M ?left"
      using twice_integrable by simp
  next
    assume left_integrable: "integrable M ?left"
    show "integrable M (\<lambda>z. cnj (?left z))"
      by (rule integrable_cnj[OF left_integrable])
  qed
qed

end
