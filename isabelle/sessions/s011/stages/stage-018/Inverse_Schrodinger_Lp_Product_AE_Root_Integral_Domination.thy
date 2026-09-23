theory Inverse_Schrodinger_Lp_Product_AE_Root_Integral_Domination
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_018.Inverse_Schrodinger_Lp_Common_CGO_Tested_Majorant_Integrable"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Nested tested-integral domination from a product-AE root bound\<close>

theorem slp_product_AE_root_integral_domination:
  fixes centers :: "slp_point set"
    and Q phi :: slp_scalar_field
    and R :: "slp_point \<Rightarrow> slp_point \<Rightarrow> complex"
    and g :: "slp_point \<Rightarrow> real"
  assumes Q_integrable: "integrable lborel Q"
    and weighted_joint_measurable:
      "(\<lambda>pair :: slp_point \<times> slp_point.
          Q (snd pair) * R (fst pair) (snd pair)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    and outer_measurable:
      "(\<lambda>c. phi c * integral\<^sup>L lborel (\<lambda>z. Q z * R c z)) \<in>
        borel_measurable lborel"
    and center_support:
      "AE c in (lborel :: slp_point measure). c \<in> centers \<or> phi c = 0"
    and g_nonnegative:
      "AE c in (lborel :: slp_point measure). 0 \<le> g c"
    and pair_bound:
      "AE pair in lborel \<Otimes>\<^sub>M lborel.
        fst pair \<in> centers \<longrightarrow>
          norm (R (fst pair) (snd pair)) \<le> g (fst pair)"
    and majorant_integrable:
      "integrable lborel (\<lambda>c. norm (phi c) * g c)"
  shows
    "integrable lborel
        (\<lambda>c. phi c * integral\<^sup>L lborel (\<lambda>z. Q z * R c z)) \<and>
     norm (integral\<^sup>L lborel
        (\<lambda>c. phi c * integral\<^sup>L lborel (\<lambda>z. Q z * R c z))) \<le>
       (integral\<^sup>L lborel (\<lambda>c. norm (phi c) * g c)) *
       (integral\<^sup>L lborel (\<lambda>z. norm (Q z)))"
proof -
  let ?qmass = "integral\<^sup>L lborel (\<lambda>z. norm (Q z))"
  have Q_norm_integrable:
      "integrable lborel (\<lambda>z. norm (Q z))"
    by (rule integrable_norm[OF Q_integrable])
  have qmass_nonnegative: "0 \<le> ?qmass"
    by (rule Bochner_Integration.integral_nonneg_AE) simp
  have weighted_fiber_measurable:
      "(\<lambda>z. Q z * R c z) \<in> borel_measurable lborel" for c
    using measurable_Pair2[OF weighted_joint_measurable, where x=c] by simp
  note fiber_bounds = lborel_pair.AE_pair[OF pair_bound]
  have outer_bound_at:
      "norm (phi c * integral\<^sup>L lborel (\<lambda>z. Q z * R c z)) \<le>
        (norm (phi c) * g c) * ?qmass"
    if support: "c \<in> centers \<or> phi c = 0"
      and g_nonnegative_at: "0 \<le> g c"
      and fiber_bound:
        "AE z in lborel. c \<in> centers \<longrightarrow> norm (R c z) \<le> g c"
    for c
  proof (cases "c \<in> centers")
    case True
    have root_majorant_integrable:
        "integrable lborel (\<lambda>z. norm (Q z) * g c)"
      by (rule Bochner_Integration.integrable_mult_left)
        (use Q_norm_integrable in simp)
    have root_norm_bound:
        "AE z in lborel.
          norm (Q z * R c z) \<le> norm (Q z) * g c"
      using fiber_bound
    proof eventually_elim
      fix z
      assume bound: "c \<in> centers \<longrightarrow> norm (R c z) \<le> g c"
      have R_bound: "norm (R c z) \<le> g c"
        using bound True by blast
      show "norm (Q z * R c z) \<le> norm (Q z) * g c"
        unfolding norm_mult
        by (rule mult_left_mono[OF R_bound]) simp
    qed
    have root_integrable:
        "integrable lborel (\<lambda>z. Q z * R c z)"
    proof (rule Bochner_Integration.integrable_bound[OF
          root_majorant_integrable weighted_fiber_measurable])
      show "AE z in lborel.
          norm (Q z * R c z) \<le> norm (norm (Q z) * g c)"
        using root_norm_bound
      proof eventually_elim
        fix z
        assume bound: "norm (Q z * R c z) \<le> norm (Q z) * g c"
        have nonnegative: "0 \<le> norm (Q z) * g c"
          by (rule mult_nonneg_nonneg[OF norm_ge_zero g_nonnegative_at])
        show "norm (Q z * R c z) \<le> norm (norm (Q z) * g c)"
          using bound by (simp only: real_norm_def abs_of_nonneg nonnegative)
      qed
    qed
    have root_integral_bound:
        "norm (integral\<^sup>L lborel (\<lambda>z. Q z * R c z)) \<le>
          ?qmass * g c"
    proof -
      have first:
          "norm (integral\<^sup>L lborel (\<lambda>z. Q z * R c z)) \<le>
            integral\<^sup>L lborel (\<lambda>z. norm (Q z * R c z))"
        by (rule Bochner_Integration.integral_norm_bound)
      have second:
          "integral\<^sup>L lborel (\<lambda>z. norm (Q z * R c z)) \<le>
            integral\<^sup>L lborel (\<lambda>z. norm (Q z) * g c)"
        by (rule Bochner_Integration.integral_mono_AE[OF
              integrable_norm[OF root_integrable]
              root_majorant_integrable root_norm_bound])
      have root_majorant_value:
          "integral\<^sup>L lborel (\<lambda>z. norm (Q z) * g c) =
            ?qmass * g c"
        by (simp add: Q_norm_integrable)
      show ?thesis using first second root_majorant_value by linarith
    qed
    show ?thesis
      unfolding norm_mult
      by (rule order_trans[OF
            mult_left_mono[OF root_integral_bound norm_ge_zero]])
        (simp only: mult_ac)
  next
    case False
    then have phi_zero: "phi c = 0" using support by blast
    show ?thesis by (simp add: phi_zero)
  qed
  have outer_bound:
      "AE c in (lborel :: slp_point measure).
        norm (phi c * integral\<^sup>L lborel (\<lambda>z. Q z * R c z)) \<le>
          (norm (phi c) * g c) * ?qmass"
    using center_support g_nonnegative fiber_bounds
    by eventually_elim
      (rule outer_bound_at; simp only: fst_conv snd_conv)
  have outer_majorant_integrable:
      "integrable lborel (\<lambda>c. (norm (phi c) * g c) * ?qmass)"
    by (rule Bochner_Integration.integrable_mult_left)
      (use majorant_integrable in simp)
  have outer_integrable:
      "integrable lborel
        (\<lambda>c. phi c * integral\<^sup>L lborel (\<lambda>z. Q z * R c z))"
  proof (rule Bochner_Integration.integrable_bound[OF
        outer_majorant_integrable outer_measurable])
    show "AE c in lborel.
        norm (phi c * integral\<^sup>L lborel (\<lambda>z. Q z * R c z)) \<le>
          norm ((norm (phi c) * g c) * ?qmass)"
      using outer_bound g_nonnegative
    proof eventually_elim
      fix c
      assume bound:
          "norm (phi c * integral\<^sup>L lborel (\<lambda>z. Q z * R c z)) \<le>
            (norm (phi c) * g c) * ?qmass"
        and g_nonnegative_at: "0 \<le> g c"
      have nonnegative: "0 \<le> (norm (phi c) * g c) * ?qmass"
        by (rule mult_nonneg_nonneg[OF
              mult_nonneg_nonneg[OF norm_ge_zero g_nonnegative_at]
              qmass_nonnegative])
      show
        "norm (phi c * integral\<^sup>L lborel (\<lambda>z. Q z * R c z)) \<le>
          norm ((norm (phi c) * g c) * ?qmass)"
        using bound by (simp only: real_norm_def abs_of_nonneg nonnegative)
    qed
  qed
  have outer_norm_bound:
      "norm (integral\<^sup>L lborel
          (\<lambda>c. phi c * integral\<^sup>L lborel (\<lambda>z. Q z * R c z))) \<le>
        integral\<^sup>L lborel
          (\<lambda>c. norm (phi c * integral\<^sup>L lborel (\<lambda>z. Q z * R c z)))"
    by (rule Bochner_Integration.integral_norm_bound)
  have outer_mass_bound:
      "integral\<^sup>L lborel
          (\<lambda>c. norm (phi c * integral\<^sup>L lborel (\<lambda>z. Q z * R c z))) \<le>
        integral\<^sup>L lborel (\<lambda>c. (norm (phi c) * g c) * ?qmass)"
    by (rule Bochner_Integration.integral_mono_AE[OF
          integrable_norm[OF outer_integrable]
          outer_majorant_integrable outer_bound])
  have outer_majorant_value:
      "integral\<^sup>L lborel (\<lambda>c. (norm (phi c) * g c) * ?qmass) =
        (integral\<^sup>L lborel (\<lambda>c. norm (phi c) * g c)) * ?qmass"
    by (simp add: majorant_integrable)
  show ?thesis
    using outer_integrable outer_norm_bound outer_mass_bound
      outer_majorant_value by linarith
qed

end
