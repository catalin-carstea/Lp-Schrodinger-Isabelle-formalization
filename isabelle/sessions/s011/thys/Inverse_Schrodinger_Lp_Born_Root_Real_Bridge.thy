theory Inverse_Schrodinger_Lp_Born_Root_Real_Bridge
  imports Inverse_Schrodinger_Lp_Born_Root_Real_Finite_Power
begin

section \<open>Exact real representative of the root-paired density\<close>

lemma slp_positive_root_output_density_real_lift_AE:
  fixes R :: real
    and cutoff potential root_weight :: "slp_point \<Rightarrow> complex"
    and terminal_weight :: "slp_point \<Rightarrow> ennreal"
  assumes cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
    and terminal_weight_measurable:
      "terminal_weight \<in> borel_measurable lborel"
    and root_weight_integrable: "integrable lborel root_weight"
    and density_finite:
      "\<And>root. AE output in lborel.
        slp_positive_output_density R cutoff potential terminal_weight n
          root output < top"
    and real_fiber_integrable:
      "AE output in lborel. integrable lborel
        (\<lambda>root. norm (root_weight root) *
          enn2real (slp_positive_output_density R cutoff potential
            terminal_weight n root output))"
  shows
    "AE output in lborel.
      slp_positive_root_output_density R cutoff potential terminal_weight n
        root_weight output =
      ennreal (integral\<^sup>L lborel
        (\<lambda>root. norm (root_weight root) *
          enn2real (slp_positive_output_density R cutoff potential
            terminal_weight n root output)))"
proof -
  let ?density =
    "slp_positive_output_density R cutoff potential terminal_weight n"
  let ?real = "\<lambda>output root. norm (root_weight root) *
    enn2real (?density root output)"
  have root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    using root_weight_integrable by measurable
  have density_joint[measurable]:
      "case_prod ?density \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_positive_output_density_joint_measurable[OF
          cutoff_measurable potential_measurable terminal_weight_measurable])
  have finite_root_output:
      "AE root in lborel. AE output in lborel. ?density root output < top"
  proof (rule AE_I2)
    fix root :: slp_point
    show "AE output in lborel. ?density root output < top"
      by (rule density_finite)
  qed
  have finite_predicate_set:
      "{root_output \<in> space (lborel \<Otimes>\<^sub>M lborel).
        ?density (fst root_output) (snd root_output) < top}
        \<in> sets (lborel \<Otimes>\<^sub>M lborel)"
    by measurable
  have finite_output_root:
      "AE output in lborel. AE root in lborel. ?density root output < top"
    using finite_root_output
      lborel_pair.AE_commute[OF finite_predicate_set]
    by blast
  show ?thesis
    using real_fiber_integrable finite_output_root
  proof eventually_elim
    fix out :: slp_point
    assume fiber_integrable:
      "integrable lborel (\<lambda>root. ?real out root)"
      and finite:
      "AE root in lborel. ?density root out < top"
    have integrand_lift:
        "AE root in lborel.
          ennreal (?real out root) =
            ennreal (norm (root_weight root)) * ?density root out"
      using finite
    proof eventually_elim
      fix root :: slp_point
      assume density_less_top: "?density root out < top"
      show "ennreal (?real out root) =
          ennreal (norm (root_weight root)) * ?density root out"
        using density_less_top
        by (simp add: ennreal_mult ennreal_enn2real)
    qed
    have real_nn:
        "(\<integral>\<^sup>+ root. ?real out root \<partial>lborel) =
          ennreal (integral\<^sup>L lborel (\<lambda>root. ?real out root))"
      by (rule nn_integral_eq_integral[OF fiber_integrable])
        (rule AE_I2, simp)
    have extended_real:
        "(\<integral>\<^sup>+ root.
            ennreal (norm (root_weight root)) * ?density root out
            \<partial>lborel) =
          ennreal (integral\<^sup>L lborel (\<lambda>root. ?real out root))"
    proof -
      have congruence:
          "(\<integral>\<^sup>+ root.
              ennreal (norm (root_weight root)) * ?density root out
              \<partial>lborel) =
            (\<integral>\<^sup>+ root. ?real out root \<partial>lborel)"
        by (rule nn_integral_cong_AE)
          (use integrand_lift in \<open>eventually_elim, simp\<close>)
      show ?thesis using congruence real_nn by simp
    qed
    show "slp_positive_root_output_density R cutoff potential
          terminal_weight n root_weight out =
        ennreal (integral\<^sup>L lborel (\<lambda>root. ?real out root))"
      unfolding slp_positive_root_output_density_def
      by (rule extended_real)
  qed
qed

end
