theory Inverse_Schrodinger_Lp_Positive_Ennreal_Bounded_Support_L1_Predicate
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Positive_Ennreal_Convolution_Shifted_L1_Lp"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Positive_Ennreal_Bounded_Support_L1"
begin

section \<open>Bounded-support promotion to the project L1 predicate\<close>

lemma slp_positive_ennreal_lp_bounded_support_to_L1:
  fixes p :: real
    and F :: "slp_point \<Rightarrow> ennreal"
  assumes p_at_least_one: "1 \<le> p"
    and F_lp: "slp_positive_ennreal_lp_on_plane p F"
    and F_support: "bounded {x. F x \<noteq> 0}"
  shows "slp_positive_ennreal_lp_on_plane 1 F"
proof -
  have F_measurable: "F \<in> borel_measurable lborel"
    and F_finite: "AE x in lborel. F x < top_class.top"
    using F_lp unfolding slp_positive_ennreal_lp_on_plane_def by blast+
  have F_real_integrable: "integrable lborel (\<lambda>x. enn2real (F x))"
    by (rule slp_positive_ennreal_lp_integrable_bounded_support[OF
          p_at_least_one F_lp F_support])
  show ?thesis
    unfolding slp_positive_ennreal_lp_on_plane_def
    using F_measurable F_finite F_real_integrable by simp
qed

end
