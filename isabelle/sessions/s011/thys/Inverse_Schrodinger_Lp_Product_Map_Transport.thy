theory Inverse_Schrodinger_Lp_Product_Map_Transport
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Qone_Active_Lebesgue_Transport"
begin

section \<open>Componentwise exact push-forwards on product measures\<close>

lemma slp_distr_pair_map_eq:
  assumes f_measurable: "f \<in> measurable M S"
    and g_measurable: "g \<in> measurable N T"
    and f_distr: "distr M S f = S"
    and g_distr: "distr N T g = T"
    and target_sigma: "sigma_finite_measure T"
  shows
    "distr (M \<Otimes>\<^sub>M N) (S \<Otimes>\<^sub>M T)
        (\<lambda>(x, y). (f x, g y)) =
      S \<Otimes>\<^sub>M T"
proof -
  have transported_sigma:
    "sigma_finite_measure (distr N T g)"
    using target_sigma
    by (simp only: g_distr)
  have product_transport:
    "distr (M \<Otimes>\<^sub>M N) (S \<Otimes>\<^sub>M T)
        (\<lambda>(x, y). (f x, g y)) =
      distr M S f \<Otimes>\<^sub>M distr N T g"
    by (rule pair_measure_distr[
          OF f_measurable g_measurable transported_sigma, symmetric])
  show ?thesis
    by (simp only: product_transport f_distr g_distr)
qed

end
