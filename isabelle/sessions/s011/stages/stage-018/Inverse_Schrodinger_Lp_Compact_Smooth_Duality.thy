theory Inverse_Schrodinger_Lp_Compact_Smooth_Duality
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_018.Inverse_Schrodinger_Lp_Open_Test_Localization"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Quantitative_Complex_Holder"
    "Paper_ISLP_Evans_Compact_Smooth_Lp_Density.Evans_Compact_Smooth_Lp_Density_Interface"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Compact-smooth duality and almost-everywhere recovery\<close>

lemma slp_hormander_compact_smooth_amplitude_lp:
  fixes q :: real and u :: slp_scalar_field
  assumes exponent_positive: "0 < q"
    and amplitude: "hormander_compact_smooth_amplitude u"
  shows "aim_complex_lp_on_plane q u"
proof -
  let ?K = "closure {x. u x \<noteq> 0}"
  have u_smooth: "smooth_on UNIV u"
    and K_compact: "compact ?K"
    using amplitude unfolding hormander_compact_smooth_amplitude_def by blast+
  have u_continuous: "continuous_on UNIV u"
    by (rule smooth_on_imp_continuous_on[OF u_smooth])
  have u_measurable: "u \<in> borel_measurable lborel"
    using borel_measurable_continuous_onI[OF u_continuous] by simp
  have power_continuous:
      "continuous_on UNIV (\<lambda>x. norm_class.norm (u x) powr q)"
  proof (rule continuous_on_powr')
    show "continuous_on UNIV (\<lambda>x. norm_class.norm (u x))"
      using u_continuous by (intro continuous_intros)
    show "continuous_on UNIV (\<lambda>_. q)"
      by simp
    show "\<forall>x\<in>UNIV. 0 \<le> norm_class.norm (u x) \<and>
        (norm_class.norm (u x) = 0 \<longrightarrow> 0 < q)"
      using exponent_positive by simp
  qed
  have restricted_power_integrable:
      "integrable lborel
        (\<lambda>x. indicator ?K x *\<^sub>R
          (norm_class.norm (u x) powr q))"
    by (rule borel_integrable_compact[OF K_compact])
       (rule continuous_on_subset[OF power_continuous subset_UNIV])
  have restricted_power_eq:
      "(\<lambda>x. indicator ?K x *\<^sub>R
          (norm_class.norm (u x) powr q)) =
        (\<lambda>x. norm_class.norm (u x) powr q)"
  proof (rule ext)
    fix x
    show "indicator ?K x *\<^sub>R (norm_class.norm (u x) powr q) =
        norm_class.norm (u x) powr q"
    proof (cases "x \<in> ?K")
      case True
      then show ?thesis by (simp add: indicator_def)
    next
      case False
      have "u x = 0"
      proof (rule ccontr)
        assume "u x \<noteq> 0"
        then have "x \<in> {y. u y \<noteq> 0}" by simp
        then show False using False closure_subset by blast
      qed
      then show ?thesis by (simp add: False indicator_def exponent_positive)
    qed
  qed
  have power_integrable:
      "integrable lborel (\<lambda>x. norm_class.norm (u x) powr q)"
    using restricted_power_integrable unfolding restricted_power_eq .
  show ?thesis
    unfolding aim_complex_lp_on_plane_def
    using u_measurable power_integrable by blast
qed

theorem slp_compact_smooth_pairing_AE_zero:
  fixes p :: real and Q :: slp_scalar_field
  assumes exponent_lower: "1 < p"
    and field_lp: "aim_complex_lp_on_plane p Q"
    and density:
      "evans_compact_smooth_lp_density_claim TYPE(2)"
    and test_pairing_zero:
      "\<And>u. hormander_compact_smooth_amplitude u \<Longrightarrow>
        integral\<^sup>L lborel (\<lambda>x. Q x * u x) = 0"
  shows "AE x in lborel. Q x = 0"
proof -
  let ?q = "p / (p - 1)"
  have p_positive: "0 < p" and denominator_positive: "0 < p - 1"
    using exponent_lower by linarith+
  have denominator_nonzero: "p - 1 \<noteq> 0"
    using denominator_positive by simp
  have q_lower: "1 < ?q"
    using denominator_positive exponent_lower
    by (simp add: less_divide_eq)
  have q_positive: "0 < ?q"
    using q_lower by linarith
  have q_at_least_one: "1 \<le> ?q"
    using q_lower by simp
  have conjugate: "1 / p + 1 / ?q = 1"
    using p_positive denominator_nonzero
    by (simp add: divide_simps algebra_simps)
  have exponent_product: "(p - 1) * ?q = p"
    using denominator_nonzero by simp

  have Q_measurable: "Q \<in> borel_measurable lborel"
    and Q_power_integrable:
      "integrable lborel (\<lambda>x. norm_class.norm (Q x) powr p)"
    using field_lp unfolding aim_complex_lp_on_plane_def by blast+

  let ?F = "\<lambda>x.
    if Q x = 0 then 0
    else
      (cnj (Q x) / of_real (norm_class.norm (Q x))) *
        of_real (norm_class.norm (Q x) powr (p - 1))"
  have cnj_borel_measurable: "cnj \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF continuous_on_cnj[OF continuous_on_id]])
  have Q_conjugate_measurable:
      "(\<lambda>x. cnj (Q x)) \<in> borel_measurable lborel"
  proof -
    have "cnj \<circ> Q \<in> borel_measurable lborel"
      using measurable_comp[OF Q_measurable cnj_borel_measurable] .
    then show ?thesis
      by (simp add: comp_def)
  qed
  have Q_norm_measurable:
      "(\<lambda>x. norm_class.norm (Q x)) \<in> borel_measurable lborel"
    using Q_measurable by measurable
  have Q_norm_complex_measurable:
      "(\<lambda>x. (of_real (norm_class.norm (Q x)) :: complex))
        \<in> borel_measurable lborel"
    using Q_norm_measurable by measurable
  have Q_power_measurable:
      "(\<lambda>x. norm_class.norm (Q x) powr (p - 1))
        \<in> borel_measurable lborel"
    using Q_norm_measurable by measurable
  have Q_power_complex_measurable:
      "(\<lambda>x. (of_real (norm_class.norm (Q x) powr (p - 1)) :: complex))
        \<in> borel_measurable lborel"
    using Q_power_measurable by measurable
  have Q_zero_set: "{x \<in> space lborel. Q x = 0} \<in> sets lborel"
    using Q_measurable by measurable
  have F_measurable: "?F \<in> borel_measurable lborel"
    using Q_conjugate_measurable Q_norm_complex_measurable
      Q_power_complex_measurable Q_zero_set
    by measurable

  have F_norm:
      "norm_class.norm (?F x) =
        norm_class.norm (Q x) powr (p - 1)" for x
  proof (cases "Q x = 0")
    case True
    then show ?thesis using denominator_positive by simp
  next
    case False
    have norm_positive: "0 < norm_class.norm (Q x)"
      using False by simp
    have phase_norm:
        "norm_class.norm
          (cnj (Q x) / of_real (norm_class.norm (Q x))) = 1"
      using norm_positive by (simp add: norm_divide)
    show ?thesis
      using norm_positive
      by (simp only: False if_False norm_mult phase_norm norm_of_real
          abs_of_nonneg powr_ge_zero mult_1_left)
  qed

  have F_product:
      "Q x * ?F x = of_real (norm_class.norm (Q x) powr p)" for x
  proof (cases "Q x = 0")
    case True
    then show ?thesis using p_positive by simp
  next
    case False
    let ?n = "norm_class.norm (Q x)"
    have n_positive: "0 < ?n" using False by simp
    have n_nonzero: "?n \<noteq> 0" using n_positive by simp
    have numerator:
        "Q x * cnj (Q x) = of_real (?n\<^sup>2)"
      using complex_norm_square[of "Q x"] by simp
    have phase_product:
        "Q x * (cnj (Q x) / of_real ?n) = of_real ?n"
      using numerator n_nonzero
      by (simp add: times_divide_eq_right power2_eq_square)
    have n_power:
        "?n * (?n powr (p - 1)) = ?n powr p"
    proof -
      have "?n * (?n powr (p - 1)) =
          (?n powr 1) * (?n powr (p - 1))"
        using n_positive by simp
      also have "... = ?n powr (1 + (p - 1))"
        by (rule powr_add[symmetric])
      also have "... = ?n powr p"
        by simp
      finally show ?thesis .
    qed
    have F_expand:
        "?F x =
          (cnj (Q x) / of_real ?n) *
            of_real (?n powr (p - 1))"
      using False by simp
    show ?thesis
      using F_expand phase_product n_power
      by (simp only: F_expand mult.assoc[symmetric] phase_product
          of_real_mult[symmetric] n_power)
  qed

  have F_power:
      "norm_class.norm (?F x) powr ?q =
        norm_class.norm (Q x) powr p" for x
  proof (cases "Q x = 0")
    case True
    then show ?thesis using p_positive q_positive by simp
  next
    case False
    have norm_positive: "0 < norm_class.norm (Q x)"
      using False by simp
    have power_identity:
        "(norm_class.norm (Q x) powr (p - 1)) powr ?q =
          norm_class.norm (Q x) powr p"
      using norm_positive exponent_product
      by (simp add: powr_powr)
    show ?thesis
      using power_identity
      by (simp only: F_norm power_identity)
  qed
  have F_power_integrable:
      "integrable lborel (\<lambda>x. norm_class.norm (?F x) powr ?q)"
    using Q_power_integrable by (simp only: F_power)
  have F_lp: "aim_complex_lp_on_plane ?q ?F"
    unfolding aim_complex_lp_on_plane_def
    using F_measurable F_power_integrable by blast

  have QF_integrable: "integrable lborel (\<lambda>x. Q x * ?F x)"
    using Q_power_integrable by (simp add: F_product)

  have QF_integral_zero:
      "integral\<^sup>L lborel (\<lambda>x. Q x * ?F x) = 0"
  proof (rule ccontr)
    assume integral_nonzero:
      "integral\<^sup>L lborel (\<lambda>x. Q x * ?F x) \<noteq> 0"
    let ?I = "norm_class.norm
      (integral\<^sup>L lborel (\<lambda>x. Q x * ?F x))"
    let ?A = "(integral\<^sup>L lborel
      (\<lambda>x. norm_class.norm (Q x) powr p)) powr (1 / p)"
    have I_positive: "0 < ?I"
      using integral_nonzero by simp
    have A_nonnegative: "0 \<le> ?A"
      by (rule powr_ge_zero)
    have denominator_A_positive: "0 < ?A + 1"
      using A_nonnegative by linarith
    let ?epsilon = "?I / (?A + 1)"
    have epsilon_positive: "0 < ?epsilon"
      using I_positive denominator_A_positive by simp
    obtain u where u_amplitude: "hormander_compact_smooth_amplitude u"
      and u_close:
        "(integral\<^sup>L lborel
          (\<lambda>x. norm_class.norm (?F x - u x) powr ?q)) powr
            (1 / ?q) < ?epsilon"
      using density q_at_least_one F_measurable F_power_integrable
        epsilon_positive
      unfolding evans_compact_smooth_lp_density_claim_def
      by blast
    have u_lp: "aim_complex_lp_on_plane ?q u"
      by (rule slp_hormander_compact_smooth_amplitude_lp[OF
            q_positive u_amplitude])
    have error_lp:
        "aim_complex_lp_on_plane ?q (\<lambda>x. ?F x - u x)"
      by (rule aim_complex_lp_on_plane_diff[OF q_positive F_lp u_lp])
    have Qu_integrable: "integrable lborel (\<lambda>x. Q x * u x)"
      by (rule slp_aim_complex_lp_on_plane_holder_integral_bound(1)[OF
            exponent_lower q_lower conjugate field_lp u_lp])
    have error_integral_identity:
        "integral\<^sup>L lborel (\<lambda>x. Q x * (?F x - u x)) =
          integral\<^sup>L lborel (\<lambda>x. Q x * ?F x) -
          integral\<^sup>L lborel (\<lambda>x. Q x * u x)"
    proof -
      have integrand_identity:
          "(\<lambda>x. Q x * (?F x - u x)) =
            (\<lambda>x. Q x * ?F x - Q x * u x)"
        by (rule ext) (simp add: algebra_simps)
      show ?thesis
        unfolding integrand_identity
        by (rule Bochner_Integration.integral_diff[OF
              QF_integrable Qu_integrable])
    qed
    have QF_as_error:
        "integral\<^sup>L lborel (\<lambda>x. Q x * ?F x) =
          integral\<^sup>L lborel (\<lambda>x. Q x * (?F x - u x))"
      using error_integral_identity test_pairing_zero[OF u_amplitude]
      by simp
    have holder_bound:
        "norm_class.norm
          (integral\<^sup>L lborel (\<lambda>x. Q x * (?F x - u x))) \<le>
          ?A *
            (integral\<^sup>L lborel
              (\<lambda>x. norm_class.norm (?F x - u x) powr ?q)) powr
                (1 / ?q)"
      by (rule slp_aim_complex_lp_on_plane_holder_integral_bound(2)[OF
            exponent_lower q_lower conjugate field_lp error_lp])
    have close_nonstrict:
        "(integral\<^sup>L lborel
          (\<lambda>x. norm_class.norm (?F x - u x) powr ?q)) powr
            (1 / ?q) \<le> ?epsilon"
      using u_close by simp
    have scaled_close:
        "?A *
          (integral\<^sup>L lborel
            (\<lambda>x. norm_class.norm (?F x - u x) powr ?q)) powr
              (1 / ?q) \<le> ?A * ?epsilon"
      by (rule mult_left_mono[OF close_nonstrict A_nonnegative])
    have ratio_less_one: "?A / (?A + 1) < 1"
      using denominator_A_positive by (simp add: divide_less_eq)
    have scaled_epsilon_less: "?A * ?epsilon < ?I"
    proof -
      have "?I * (?A / (?A + 1)) < ?I * 1"
        by (rule mult_strict_left_mono[OF ratio_less_one I_positive])
      then show ?thesis
        using denominator_A_positive
        by (simp add: algebra_simps)
    qed
    have "?I \<le> ?A * ?epsilon"
      using holder_bound scaled_close QF_as_error by simp
    then show False using scaled_epsilon_less by simp
  qed

  have power_integral_zero:
      "integral\<^sup>L lborel
        (\<lambda>x. norm_class.norm (Q x) powr p) = 0"
  proof -
    have integral_identity:
        "integral\<^sup>L lborel (\<lambda>x. Q x * ?F x) =
          of_real (integral\<^sup>L lborel
            (\<lambda>x. norm_class.norm (Q x) powr p))"
      by (simp only: F_product integral_complex_of_real)
    show ?thesis
      using QF_integral_zero integral_identity by simp
  qed
  have power_zero_AE:
      "AE x in lborel. norm_class.norm (Q x) powr p = 0"
    using integral_nonneg_eq_0_iff_AE[OF Q_power_integrable]
      power_integral_zero
    by simp
  show ?thesis
    using power_zero_AE
  proof eventually_elim
    fix x
    assume "norm_class.norm (Q x) powr p = 0"
    then have "norm_class.norm (Q x) = 0"
      using p_positive by simp
    then show "Q x = 0" by simp
  qed
qed

end
