theory Inverse_Schrodinger_Lp_Signed_Product_Lebesgue_Transport
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cartesian_Sum_Merge"
begin

section \<open>Reverse Lebesgue transport for signed product coordinates\<close>

theorem slp_signed_product_to_cartesian_distr_lborel:
  "distr
      (lborel :: ((real^bool) \<times> (real^('i::finite \<times> bool))) measure)
      (lborel :: (real^((unit + 'i) \<times> bool)) measure)
      slp_signed_product_to_cartesian =
    (lborel :: (real^((unit + 'i) \<times> bool)) measure)"
proof -
  let ?F = "slp_signed_cartesian_to_product ::
    real^((unit + 'i) \<times> bool) \<Rightarrow>
      (real^bool) \<times> (real^('i \<times> bool))"
  let ?G = "slp_signed_product_to_cartesian ::
    ((real^bool) \<times> (real^('i \<times> bool))) \<Rightarrow>
      real^((unit + 'i) \<times> bool)"
  have composition: "?G \<circ> ?F = id"
  proof (rule ext)
    fix x :: "real^((unit + 'i) \<times> bool)"
    show "(?G \<circ> ?F) x = id x"
      by (simp only: comp_apply id_apply
          slp_signed_product_to_cartesian_to_product)
  qed
  have "distr
      (lborel :: ((real^bool) \<times> (real^('i \<times> bool))) measure)
      (lborel :: (real^((unit + 'i) \<times> bool)) measure) ?G =
    distr
      (distr
        (lborel :: (real^((unit + 'i) \<times> bool)) measure)
        (lborel :: ((real^bool) \<times> (real^('i \<times> bool))) measure)
        ?F)
      (lborel :: (real^((unit + 'i) \<times> bool)) measure) ?G"
    by (simp only: slp_signed_cartesian_to_product_distr_lborel)
  also have "... = distr
      (lborel :: (real^((unit + 'i) \<times> bool)) measure)
      (lborel :: (real^((unit + 'i) \<times> bool)) measure)
      (?G \<circ> ?F)"
    by (rule distr_distr[
          OF slp_signed_product_to_cartesian_measurable
            slp_signed_cartesian_to_product_measurable])
  also have "... = distr
      (lborel :: (real^((unit + 'i) \<times> bool)) measure)
      (lborel :: (real^((unit + 'i) \<times> bool)) measure) id"
    by (simp only: composition)
  also have "... = (lborel :: (real^((unit + 'i) \<times> bool)) measure)"
    by (simp only: id_def distr_id)
  finally show ?thesis .
qed

end
