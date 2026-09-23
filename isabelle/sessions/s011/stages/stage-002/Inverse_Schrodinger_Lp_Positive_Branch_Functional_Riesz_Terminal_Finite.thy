theory Inverse_Schrodinger_Lp_Positive_Branch_Functional_Riesz_Terminal_Finite
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Positive_Ennreal_Bounded_Support_L1"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Output_Pushforward"
begin

section \<open>Fixed-root finiteness for the Riesz terminal and unit output\<close>

context aim_planar_riesz_hls
begin

theorem slp_positive_branch_functional_riesz_terminal_unit_finite:
  fixes R C p :: real
    and cutoff potential :: "slp_point \<Rightarrow> complex"
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "slp_positive_branch_functional R cutoff potential
      (slp_positive_terminal_riesz_weight R potential) n origin
      (\<lambda>_. 1) < top_class.top"
proof -
  let ?q = "slp_branch_power_exponent p"
  let ?F = "slp_positive_output_density R cutoff potential
    (slp_positive_terminal_riesz_weight R potential) n origin"
  note weighted =
    slp_positive_output_density_all_orders_terminal_weighted[OF
      radius_nonnegative p_lower p_upper cutoff_measurable potential_lp
      cutoff_bound C_nonnegative]
  have q_lower: "1 < ?q"
    using weighted(1) by blast
  obtain L where F_lp: "slp_positive_ennreal_lp_on_plane ?q ?F"
    using weighted(2)[of n] by blast
  have potential_measurable:
      "potential \<in> borel_measurable lborel"
    using potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have terminal_weight_measurable:
      "slp_positive_terminal_riesz_weight R potential
        \<in> borel_measurable lborel"
    by (rule slp_positive_terminal_riesz_weight_measurable[OF
          potential_measurable])
  have F_support: "bounded {out. ?F out \<noteq> 0}"
    unfolding bounded_iff
  proof (intro exI[of _
      "Real_Vector_Spaces.norm origin + real (Suc n) * R"] ballI)
    fix out
    assume out_in: "out \<in> {out. ?F out \<noteq> 0}"
    show "Real_Vector_Spaces.norm out \<le>
      Real_Vector_Spaces.norm origin + real (Suc n) * R"
    proof (rule ccontr)
      assume not_bounded:
        "\<not> Real_Vector_Spaces.norm out \<le>
          Real_Vector_Spaces.norm origin + real (Suc n) * R"
      have triangle:
          "Real_Vector_Spaces.norm out \<le>
            Real_Vector_Spaces.norm (out - origin) +
            Real_Vector_Spaces.norm origin"
        using norm_triangle_ineq[of "out - origin" origin] by simp
      have outside:
          "real (Suc n) * R < Real_Vector_Spaces.norm (out - origin)"
        using not_bounded triangle by linarith
      have F_zero: "?F out = 0"
        by (rule slp_positive_output_density_outside[OF
              radius_nonnegative outside])
      show False using out_in F_zero by simp
    qed
  qed
  have F_real_integrable:
      "integrable lborel (\<lambda>out. enn2real (?F out))"
    by (rule slp_positive_ennreal_lp_integrable_bounded_support[OF
          less_imp_le[OF q_lower] F_lp F_support])
  have F_ae_finite: "AE out in lborel. ?F out < top_class.top"
    using F_lp unfolding slp_positive_ennreal_lp_on_plane_def by blast
  have F_lifted:
      "AE out in lborel. ?F out = ennreal (enn2real (?F out))"
    using F_ae_finite
    by eventually_elim simp
  have nonnegative:
      "AE out in lborel. 0 \<le> enn2real (?F out)"
    by simp
  have F_nn_lift:
      "(\<integral>\<^sup>+ out. ?F out \<partial>lborel) =
        (\<integral>\<^sup>+ out. ennreal (enn2real (?F out)) \<partial>lborel)"
    by (rule nn_integral_cong_AE) (use F_lifted in eventually_elim; simp)
  have F_lift_eq:
      "(\<integral>\<^sup>+ out. ennreal (enn2real (?F out)) \<partial>lborel) =
        ennreal (integral\<^sup>L lborel (\<lambda>out. enn2real (?F out)))"
    by (rule nn_integral_eq_integral[OF F_real_integrable nonnegative])
  have F_nn_eq:
      "(\<integral>\<^sup>+ out. ?F out \<partial>lborel) =
        ennreal (integral\<^sup>L lborel (\<lambda>out. enn2real (?F out)))"
    using F_nn_lift F_lift_eq by simp
  have F_nn_finite: "(\<integral>\<^sup>+ out. ?F out \<partial>lborel) < top_class.top"
    using F_nn_eq by simp
  have unit_test_measurable:
      "(\<lambda>_ :: slp_point.
          ennreal (Real_Vector_Spaces.norm (1 :: complex)))
        \<in> borel_measurable lborel"
    by measurable
  have pushforward:
      "(\<integral>\<^sup>+ output.
          ennreal (Real_Vector_Spaces.norm (1 :: complex)) * ?F output
          \<partial>lborel) =
        slp_positive_branch_functional R cutoff potential
          (slp_positive_terminal_riesz_weight R potential) n origin
          (\<lambda>_. 1)"
    using slp_positive_output_density_pushforward[OF
        cutoff_measurable potential_measurable terminal_weight_measurable
        unit_test_measurable]
    by simp
  show ?thesis
    using F_nn_finite pushforward by simp
qed

end

end
