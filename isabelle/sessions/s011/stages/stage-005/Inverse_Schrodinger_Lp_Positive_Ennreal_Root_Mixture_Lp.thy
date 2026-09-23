theory Inverse_Schrodinger_Lp_Positive_Ennreal_Root_Mixture_Lp
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Integral_Minkowski_Power_Plane_AE"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Positive_Ennreal_Real_Representatives"
begin

section \<open>Positive extended-real root mixtures\<close>

definition slp_positive_ennreal_root_mixture ::
    "(slp_point \<Rightarrow> real) \<Rightarrow>
      (slp_point \<Rightarrow> slp_point \<Rightarrow> ennreal) \<Rightarrow>
      slp_point \<Rightarrow> ennreal"
where
  "slp_positive_ennreal_root_mixture weight datum output =
    (\<integral>\<^sup>+ root.
      ennreal (weight root) * datum root output \<partial>lborel)"

lemma slp_positive_ennreal_root_mixture_measurable:
  assumes weight_measurable[measurable]:
      "weight \<in> borel_measurable lborel"
    and datum_joint_measurable[measurable]:
      "case_prod datum \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
  shows
    "slp_positive_ennreal_root_mixture weight datum
      \<in> borel_measurable lborel"
  unfolding slp_positive_ennreal_root_mixture_def by measurable

theorem slp_positive_ennreal_root_mixture_Lp:
  fixes a b L :: real
    and weight :: "slp_point \<Rightarrow> real"
    and datum :: "slp_point \<Rightarrow> slp_point \<Rightarrow> ennreal"
  assumes a_lower: "1 < a"
    and b_lower: "1 < b"
    and conjugate: "1 / a + 1 / b = 1"
    and weight_measurable: "weight \<in> borel_measurable lborel"
    and datum_joint_measurable:
      "case_prod datum \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    and weight_nonnegative: "\<And>root. 0 \<le> weight root"
    and weight_integrable: "integrable lborel weight"
    and datum_lp:
      "\<And>root. slp_positive_ennreal_lp_on_plane a (datum root)"
    and datum_power_bound:
      "\<And>root. integral\<^sup>L lborel
        (\<lambda>output. enn2real (datum root output) powr a) \<le> L"
    and L_nonnegative: "0 \<le> L"
  shows mixture_lp:
    "slp_positive_ennreal_lp_on_plane a
      (slp_positive_ennreal_root_mixture weight datum)"
    and mixture_power_bound:
    "integral\<^sup>L lborel
        (\<lambda>output.
          enn2real (slp_positive_ennreal_root_mixture weight datum output)
            powr a)
      \<le> (integral\<^sup>L lborel weight) powr (a / b) *
        (L * integral\<^sup>L lborel weight)"
proof -
  let ?real_datum = "\<lambda>root output. enn2real (datum root output)"
  let ?mixture = "slp_positive_ennreal_root_mixture weight datum"
  let ?H = "\<lambda>output. integral\<^sup>L lborel
    (\<lambda>root. weight root * ?real_datum root output)"
  note [measurable] = weight_measurable datum_joint_measurable
  have real_datum_joint_measurable:
      "case_prod ?real_datum
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by measurable
  have real_datum_nonnegative:
      "0 \<le> ?real_datum root out"
    for root out
    by simp
  have datum_power_integrable:
      "integrable lborel
        (\<lambda>output. ?real_datum root output powr a)"
    for root
    using datum_lp[of root]
    unfolding slp_positive_ennreal_lp_on_plane_def by blast
  have fiber_power_integrable_AE:
      "AE output in lborel. integrable lborel
        (\<lambda>root. weight root * ?real_datum root output powr a)"
    by (rule slp_weighted_source_power_bound_plane(2)[OF
          weight_measurable real_datum_joint_measurable weight_nonnegative
          real_datum_nonnegative weight_integrable datum_power_integrable
          datum_power_bound L_nonnegative])
  have source_power_integrable:
      "integrable lborel
        (\<lambda>output. integral\<^sup>L lborel
          (\<lambda>root. weight root * ?real_datum root output powr a))"
    by (rule slp_weighted_source_power_bound_plane(3)[OF
          weight_measurable real_datum_joint_measurable weight_nonnegative
          real_datum_nonnegative weight_integrable datum_power_integrable
          datum_power_bound L_nonnegative])
  have source_power_bound:
      "integral\<^sup>L lborel
          (\<lambda>output. integral\<^sup>L lborel
            (\<lambda>root. weight root * ?real_datum root output powr a))
        \<le> L * integral\<^sup>L lborel weight"
    by (rule slp_weighted_source_power_bound_plane(4)[OF
          weight_measurable real_datum_joint_measurable weight_nonnegative
          real_datum_nonnegative weight_integrable datum_power_integrable
          datum_power_bound L_nonnegative])
  have real_fiber_integrable:
      "AE output in lborel. integrable lborel
        (\<lambda>root. weight root * ?real_datum root output)"
    using fiber_power_integrable_AE
  proof eventually_elim
    fix out :: slp_point
    assume fiber_power:
      "integrable lborel
        (\<lambda>root. weight root * ?real_datum root out powr a)"
    have datum_section_measurable:
        "(\<lambda>root. ?real_datum root out)
          \<in> borel_measurable lborel"
      by measurable
    show "integrable lborel
        (\<lambda>root. weight root * ?real_datum root out)"
      by (rule slp_weighted_holder_power(1)[OF
            a_lower b_lower conjugate weight_measurable
            datum_section_measurable weight_nonnegative _ weight_integrable
            fiber_power])
        (rule real_datum_nonnegative)
  qed
  have real_power_integrable:
      "integrable lborel (\<lambda>output. ?H output powr a)"
    by (rule slp_integral_minkowski_power_plane_AE(1)[OF
          a_lower b_lower conjugate weight_measurable
          real_datum_joint_measurable weight_nonnegative
          real_datum_nonnegative weight_integrable fiber_power_integrable_AE
          source_power_integrable])
  have real_power_minkowski:
      "integral\<^sup>L lborel (\<lambda>output. ?H output powr a) \<le>
        (integral\<^sup>L lborel weight) powr (a / b) *
          integral\<^sup>L lborel
            (\<lambda>output. integral\<^sup>L lborel
              (\<lambda>root.
                weight root * ?real_datum root output powr a))"
    by (rule slp_integral_minkowski_power_plane_AE(2)[OF
          a_lower b_lower conjugate weight_measurable
          real_datum_joint_measurable weight_nonnegative
          real_datum_nonnegative weight_integrable fiber_power_integrable_AE
          source_power_integrable])
  have scale_nonnegative:
      "0 \<le> (integral\<^sup>L lborel weight) powr (a / b)"
    by simp
  have scaled_source_bound:
      "(integral\<^sup>L lborel weight) powr (a / b) *
          integral\<^sup>L lborel
            (\<lambda>output. integral\<^sup>L lborel
              (\<lambda>root.
                weight root * ?real_datum root output powr a))
        \<le> (integral\<^sup>L lborel weight) powr (a / b) *
          (L * integral\<^sup>L lborel weight)"
    by (rule mult_left_mono[OF source_power_bound scale_nonnegative])
  have real_power_bound:
      "integral\<^sup>L lborel (\<lambda>output. ?H output powr a) \<le>
        (integral\<^sup>L lborel weight) powr (a / b) *
          (L * integral\<^sup>L lborel weight)"
    using real_power_minkowski scaled_source_bound by linarith
  have datum_finite:
      "AE root in lborel. AE output in lborel. datum root output < top"
  proof (rule AE_I2)
    fix root :: slp_point
    show "AE output in lborel. datum root output < top"
      using datum_lp[of root]
      unfolding slp_positive_ennreal_lp_on_plane_def by blast
  qed
  have finite_predicate_set:
      "{root_output \<in> space (lborel \<Otimes>\<^sub>M lborel).
        datum (fst root_output) (snd root_output) < top}
        \<in> sets (lborel \<Otimes>\<^sub>M lborel)"
    by measurable
  have datum_finite_swapped:
      "AE output in lborel. AE root in lborel. datum root output < top"
    using datum_finite lborel_pair.AE_commute[OF finite_predicate_set]
    by blast
  have mixture_real_lift:
      "AE output in lborel. ?mixture output = ennreal (?H output)"
    using real_fiber_integrable datum_finite_swapped
  proof eventually_elim
    fix out :: slp_point
    assume fiber_integrable:
      "integrable lborel
        (\<lambda>root. weight root * ?real_datum root out)"
      and finite: "AE root in lborel. datum root out < top"
    have integrand_lift:
        "AE root in lborel.
          ennreal (weight root * ?real_datum root out) =
            ennreal (weight root) * datum root out"
      using finite
    proof eventually_elim
      fix root :: slp_point
      assume datum_less_top: "datum root out < top"
      show "ennreal (weight root * ?real_datum root out) =
          ennreal (weight root) * datum root out"
        using datum_less_top weight_nonnegative[of root]
        by (simp add: ennreal_mult ennreal_enn2real)
    qed
    have real_nn:
        "(\<integral>\<^sup>+ root.
            weight root * ?real_datum root out \<partial>lborel) =
          ennreal (?H out)"
      by (rule nn_integral_eq_integral[OF fiber_integrable])
        (rule AE_I2, simp add: weight_nonnegative)
    have extended_real:
        "(\<integral>\<^sup>+ root.
            ennreal (weight root) * datum root out \<partial>lborel) =
          ennreal (?H out)"
    proof -
      have congruence:
          "(\<integral>\<^sup>+ root.
              ennreal (weight root) * datum root out \<partial>lborel) =
            (\<integral>\<^sup>+ root.
              weight root * ?real_datum root out \<partial>lborel)"
        by (rule nn_integral_cong_AE)
          (use integrand_lift in \<open>eventually_elim, simp\<close>)
      show ?thesis using congruence real_nn by simp
    qed
    show "?mixture out = ennreal (?H out)"
      unfolding slp_positive_ennreal_root_mixture_def
      by (rule extended_real)
  qed
  have mixture_measurable:
      "?mixture \<in> borel_measurable lborel"
    by (rule slp_positive_ennreal_root_mixture_measurable[OF
          weight_measurable datum_joint_measurable])
  have mixture_finite: "AE output in lborel. ?mixture output < top"
    using mixture_real_lift by eventually_elim simp
  have H_nonnegative: "0 \<le> ?H out" for out
    by (rule integral_nonneg_AE)
      (rule AE_I2, simp add: weight_nonnegative)
  have mixture_power_identity:
      "AE output in lborel.
        enn2real (?mixture output) powr a = ?H output powr a"
    using mixture_real_lift
  proof eventually_elim
    fix out :: slp_point
    assume mixture_eq: "?mixture out = ennreal (?H out)"
    show "enn2real (?mixture out) powr a = ?H out powr a"
      using mixture_eq H_nonnegative[of out] by simp
  qed
  have mixture_power_measurable:
      "(\<lambda>output. enn2real (?mixture output) powr a)
        \<in> borel_measurable lborel"
    using mixture_measurable by measurable
  have real_power_measurable:
      "(\<lambda>output. ?H output powr a) \<in> borel_measurable lborel"
    using real_power_integrable by measurable
  have mixture_power_integrable:
      "integrable lborel
        (\<lambda>output. enn2real (?mixture output) powr a)"
    by (rule integrable_cong_AE_imp[OF
          real_power_integrable mixture_power_measurable])
      (use mixture_power_identity in eventually_elim; simp)
  show "slp_positive_ennreal_lp_on_plane a ?mixture"
    unfolding slp_positive_ennreal_lp_on_plane_def
    using mixture_measurable mixture_finite mixture_power_integrable by blast
  have exact_power:
      "integral\<^sup>L lborel
          (\<lambda>output. enn2real (?mixture output) powr a) =
        integral\<^sup>L lborel (\<lambda>output. ?H output powr a)"
    by (rule integral_cong_AE[OF mixture_power_measurable
          real_power_measurable mixture_power_identity])
  show "integral\<^sup>L lborel
        (\<lambda>output. enn2real (?mixture output) powr a) \<le>
      (integral\<^sup>L lborel weight) powr (a / b) *
        (L * integral\<^sup>L lborel weight)"
    using real_power_bound by (simp only: exact_power)
qed

end
