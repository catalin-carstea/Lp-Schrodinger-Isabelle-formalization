theory Inverse_Schrodinger_Lp_Positive_Output_Density_Bounded_Support
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Positive_Ennreal_Bounded_Support_L1_Predicate"
begin

section \<open>Bounded propagation for fixed-origin output densities\<close>

theorem slp_positive_output_density_bounded_support:
  assumes radius_nonnegative: "0 \<le> R"
  shows
    "bounded {out.
      slp_positive_output_density R cutoff potential terminal_weight n
        origin out \<noteq> 0}"
proof (rule bounded_subset[OF bounded_cball])
  show
    "{out.
      slp_positive_output_density R cutoff potential terminal_weight n
        origin out \<noteq> 0}
      \<subseteq> cball origin (real (Suc n) * R)"
  proof
    fix out :: slp_point
    assume output_nonzero:
      "out \<in> {out.
        slp_positive_output_density R cutoff potential terminal_weight n
          origin out \<noteq> 0}"
    have near_origin:
        "Real_Vector_Spaces.norm (out - origin) \<le> real (Suc n) * R"
    proof (rule ccontr)
      assume not_near:
        "\<not> Real_Vector_Spaces.norm (out - origin) \<le>
          real (Suc n) * R"
      have outside:
        "real (Suc n) * R < Real_Vector_Spaces.norm (out - origin)"
        using not_near by simp
      have density_zero:
        "slp_positive_output_density R cutoff potential terminal_weight n
          origin out = 0"
        by (rule slp_positive_output_density_outside[OF
              radius_nonnegative outside])
      show False using output_nonzero density_zero by simp
    qed
    show "out \<in> cball origin (real (Suc n) * R)"
      using near_origin by (simp add: dist_norm norm_minus_commute)
  qed
qed

corollary slp_left_positive_output_density_bounded_support:
  assumes radius_nonnegative: "0 \<le> R"
  shows
    "bounded {out.
      slp_left_positive_output_density R cutoff potential terminal_weight n
        origin out \<noteq> 0}"
  unfolding slp_left_positive_output_density_def
  by (rule slp_positive_output_density_bounded_support[OF
        radius_nonnegative])

corollary slp_right_positive_output_density_bounded_support:
  assumes radius_nonnegative: "0 \<le> R"
  shows
    "bounded {out.
      slp_right_positive_output_density R cutoff potential terminal_weight n
        origin out \<noteq> 0}"
  unfolding slp_right_positive_output_density_def
  by (rule slp_positive_output_density_bounded_support[OF
        radius_nonnegative])

end
