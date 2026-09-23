theory Inverse_Schrodinger_Lp_Born_One_Sided_Center_Average_Error_Limits
  imports
    Inverse_Schrodinger_Lp_Born_One_Sided_L2_Error_Pairing_Limits
    Inverse_Schrodinger_Lp_Cauchy_Gradient_Lp
begin

section \<open>One-sided center-average error limits\<close>

context aim_planar_riesz_hls
begin

theorem slp_left_right_one_sided_center_average_error_pairing_limits:
  fixes R C p :: real
    and X :: "slp_point set"
    and cutoff potential source :: "slp_point \<Rightarrow> complex"
    and n :: nat
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
    and source_l2: "aim_complex_lp_on_plane 2 source"
    and center_average_l2:
      "\<And>tau. aim_complex_lp_on_plane 2 (slp_center_average tau source)"
    and center_average_error_square_decay:
      "((\<lambda>tau. \<integral>\<^sup>+x. ennreal (Real_Vector_Spaces.norm
          (slp_center_average tau source x - source x)) ^ 2 \<partial>lborel)
        \<longlongrightarrow> 0) at_top"
  shows left_limit:
      "((\<lambda>tau. integral\<^sup>L lborel (\<lambda>output.
          of_real (enn2real
            (slp_left_one_sided_output_density R cutoff potential
              (\<lambda>_. 1) n potential output)) *
          (slp_center_average tau source output - source output)))
        \<longlongrightarrow> 0) at_top"
    and right_limit:
      "((\<lambda>tau. integral\<^sup>L lborel (\<lambda>output.
          of_real (enn2real
            (slp_right_one_sided_output_density R cutoff potential
              (\<lambda>_. 1) n potential output)) *
          (slp_center_average tau source output - source output)))
        \<longlongrightarrow> 0) at_top"
proof -
  have error_l2:
      "aim_complex_lp_on_plane 2
        (\<lambda>x. slp_center_average tau source x - source x)" for tau
    by (rule aim_complex_lp_on_plane_diff[OF zero_less_numeral
          center_average_l2 source_l2])
  show left_limit:
      "((\<lambda>tau. integral\<^sup>L lborel (\<lambda>output.
          of_real (enn2real
            (slp_left_one_sided_output_density R cutoff potential
              (\<lambda>_. 1) n potential output)) *
          (slp_center_average tau source output - source output)))
        \<longlongrightarrow> 0) at_top"
    by (rule slp_left_right_one_sided_l2_error_pairing_limits(1)[OF
          radius_nonnegative p_lower p_upper X_measurable X_bounded
          cutoff_measurable potential_lp potential_outside cutoff_bound
          C_nonnegative error_l2 center_average_error_square_decay])
  show right_limit:
      "((\<lambda>tau. integral\<^sup>L lborel (\<lambda>output.
          of_real (enn2real
            (slp_right_one_sided_output_density R cutoff potential
              (\<lambda>_. 1) n potential output)) *
          (slp_center_average tau source output - source output)))
        \<longlongrightarrow> 0) at_top"
    by (rule slp_left_right_one_sided_l2_error_pairing_limits(2)[OF
          radius_nonnegative p_lower p_upper X_measurable X_bounded
          cutoff_measurable potential_lp potential_outside cutoff_bound
          C_nonnegative error_l2 center_average_error_square_decay])
qed

end

end
