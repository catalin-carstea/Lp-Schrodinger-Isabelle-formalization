theory Inverse_Schrodinger_Lp_Qone_Active_Lebesgue_Transport
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Signed_Tail_Lebesgue_Transport"
begin

section \<open>Terminal and signed-tail coordinates for QONE\<close>

definition slp_qone_active_merge ::
    "(real^bool) \<times> (real^(('i::finite + 'i) \<times> bool)) \<Rightarrow>
      real^((unit + ('i + 'i)) \<times> bool)"
where
  "slp_qone_active_merge = slp_signed_product_to_cartesian"

lemma slp_qone_active_merge_measurable:
  "(slp_qone_active_merge ::
      (real^bool) \<times> (real^(('i::finite + 'i) \<times> bool)) \<Rightarrow>
        real^((unit + ('i + 'i)) \<times> bool))
    \<in> measurable (lborel \<Otimes>\<^sub>M lborel) lborel"
  unfolding slp_qone_active_merge_def
  using slp_signed_product_to_cartesian_measurable[
    where 'i = "'i + 'i"]
  by (simp only: lborel_prod)

theorem slp_qone_active_merge_distr_lborel:
  "distr
      ((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
        (lborel :: (real^(('i::finite + 'i) \<times> bool)) measure))
      (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure)
      slp_qone_active_merge =
    (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure)"
  unfolding slp_qone_active_merge_def
  using slp_signed_product_to_cartesian_distr_lborel[
    where 'i = "'i + 'i"]
  by (simp only: lborel_prod)

end
