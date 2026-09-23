theory Inverse_Schrodinger_Lp_Born_One_Sided_Center_Average_Pairing_Limits
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_One_Sided_All_Order_L1"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Center_Average_Pairing"
begin

section \<open>Exact one-sided density center-average pairing limits\<close>

context aim_planar_riesz_hls
begin

theorem slp_left_right_one_sided_output_density_center_average_pairing_limits:
  fixes R C p :: real
    and X :: "slp_point set"
    and cutoff potential source :: "slp_point \<Rightarrow> complex"
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and potential_outside: "\<And>x. x \<notin> X \<Longrightarrow> potential x = 0"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and source_integrable: "integrable lborel source"
    and source_bounded: "bounded (range source)"
    and source_uniform_convergence:
      "uniform_limit UNIV
        (\<lambda>tau. slp_center_average tau source) source at_top"
  shows left_limit:
      "((\<lambda>tau. integral\<^sup>L lborel (\<lambda>output.
          of_real (enn2real
            (slp_left_one_sided_output_density R cutoff potential
              (\<lambda>_. 1) n potential output)) *
          slp_center_average tau source output))
        \<longlongrightarrow>
          integral\<^sup>L lborel (\<lambda>output.
            of_real (enn2real
              (slp_left_one_sided_output_density R cutoff potential
                (\<lambda>_. 1) n potential output)) * source output)) at_top"
    and right_limit:
      "((\<lambda>tau. integral\<^sup>L lborel (\<lambda>output.
          of_real (enn2real
            (slp_right_one_sided_output_density R cutoff potential
              (\<lambda>_. 1) n potential output)) *
          slp_center_average tau source output))
        \<longlongrightarrow>
          integral\<^sup>L lborel (\<lambda>output.
            of_real (enn2real
              (slp_right_one_sided_output_density R cutoff potential
                (\<lambda>_. 1) n potential output)) * source output)) at_top"
proof -
  have left_real_integrable:
      "integrable lborel (\<lambda>output. enn2real
        (slp_left_one_sided_output_density R cutoff potential
          (\<lambda>_. 1) n potential output))"
    by (rule slp_left_right_one_sided_output_density_real_all_orders_l1(1)[OF
          radius_nonnegative p_lower p_upper X_measurable X_bounded
          cutoff_measurable potential_lp potential_outside cutoff_bound
          C_nonnegative])
  have right_real_integrable:
      "integrable lborel (\<lambda>output. enn2real
        (slp_right_one_sided_output_density R cutoff potential
          (\<lambda>_. 1) n potential output))"
    by (rule slp_left_right_one_sided_output_density_real_all_orders_l1(2)[OF
          radius_nonnegative p_lower p_upper X_measurable X_bounded
          cutoff_measurable potential_lp potential_outside cutoff_bound
          C_nonnegative])
  have left_complex_integrable:
      "integrable lborel (\<lambda>output. of_real (enn2real
        (slp_left_one_sided_output_density R cutoff potential
          (\<lambda>_. 1) n potential output)))"
    using left_real_integrable by simp
  have right_complex_integrable:
      "integrable lborel (\<lambda>output. of_real (enn2real
        (slp_right_one_sided_output_density R cutoff potential
          (\<lambda>_. 1) n potential output)))"
    using right_real_integrable by simp
  show left_limit:
      "((\<lambda>tau. integral\<^sup>L lborel (\<lambda>output.
          of_real (enn2real
            (slp_left_one_sided_output_density R cutoff potential
              (\<lambda>_. 1) n potential output)) *
          slp_center_average tau source output))
        \<longlongrightarrow>
          integral\<^sup>L lborel (\<lambda>output.
            of_real (enn2real
              (slp_left_one_sided_output_density R cutoff potential
                (\<lambda>_. 1) n potential output)) * source output)) at_top"
    by (rule slp_center_average_pairing_convergence[OF
          left_complex_integrable source_integrable source_bounded
          source_uniform_convergence])
  show right_limit:
      "((\<lambda>tau. integral\<^sup>L lborel (\<lambda>output.
          of_real (enn2real
            (slp_right_one_sided_output_density R cutoff potential
              (\<lambda>_. 1) n potential output)) *
          slp_center_average tau source output))
        \<longlongrightarrow>
          integral\<^sup>L lborel (\<lambda>output.
            of_real (enn2real
              (slp_right_one_sided_output_density R cutoff potential
                (\<lambda>_. 1) n potential output)) * source output)) at_top"
    by (rule slp_center_average_pairing_convergence[OF
          right_complex_integrable source_integrable source_bounded
          source_uniform_convergence])
qed

end

end
