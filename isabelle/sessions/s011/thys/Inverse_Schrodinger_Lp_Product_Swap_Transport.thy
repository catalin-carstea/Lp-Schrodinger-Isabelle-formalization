theory Inverse_Schrodinger_Lp_Product_Swap_Transport
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Point_Family_Signed_Tail_Transport"
begin

section \<open>Exact swapping of sigma-finite product measures\<close>

lemma slp_pair_swap_distr:
  assumes M_sigma: "sigma_finite_measure M"
    and N_sigma: "sigma_finite_measure N"
  shows
    "distr (M \<Otimes>\<^sub>M N) (N \<Otimes>\<^sub>M M)
        (\<lambda>(x, y). (y, x)) =
      N \<Otimes>\<^sub>M M"
proof -
  interpret N: sigma_finite_measure N
    by (rule N_sigma)
  interpret M: sigma_finite_measure M
    by (rule M_sigma)
  interpret swapped: pair_sigma_finite N M ..
  show ?thesis
    using swapped.distr_pair_swap
    by (rule sym)
qed

end
