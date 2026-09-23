theory Inverse_Schrodinger_Lp_Born_One_Sided_L2_Error_Pairing_Limits
  imports Inverse_Schrodinger_Lp_Real_Complex_L2_Pairing_Limit
begin

section \<open>All-order one-sided strong-\(L^2\) error pairings\<close>

context aim_planar_riesz_hls
begin

theorem slp_left_right_one_sided_l2_error_pairing_limits:
  fixes R C p :: real
    and X :: "slp_point set"
    and cutoff potential :: "slp_point \<Rightarrow> complex"
    and error :: "'a \<Rightarrow> slp_point \<Rightarrow> complex"
    and F :: "'a filter"
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
    and error_l2: "\<And>i. aim_complex_lp_on_plane 2 (error i)"
    and error_square_decay:
      "((\<lambda>i. \<integral>\<^sup>+x.
          ennreal (Real_Vector_Spaces.norm (error i x)) ^ 2 \<partial>lborel)
        \<longlongrightarrow> 0) F"
  shows left_limit:
      "((\<lambda>i. integral\<^sup>L lborel (\<lambda>output.
          of_real (enn2real
            (slp_left_one_sided_output_density R cutoff potential
              (\<lambda>_. 1) n potential output)) * error i output))
        \<longlongrightarrow> 0) F"
    and right_limit:
      "((\<lambda>i. integral\<^sup>L lborel (\<lambda>output.
          of_real (enn2real
            (slp_right_one_sided_output_density R cutoff potential
              (\<lambda>_. 1) n potential output)) * error i output))
        \<longlongrightarrow> 0) F"
proof -
  have left_l2:
      "aim_real_lp_on_plane 2 (\<lambda>output. enn2real
        (slp_left_one_sided_output_density R cutoff potential
          (\<lambda>_. 1) n potential output))"
    by (rule slp_left_right_one_sided_output_density_real_all_orders_l2(2)[OF
          radius_nonnegative p_lower p_upper X_measurable X_bounded
          cutoff_measurable potential_lp potential_outside cutoff_bound
          C_nonnegative])
  have right_l2:
      "aim_real_lp_on_plane 2 (\<lambda>output. enn2real
        (slp_right_one_sided_output_density R cutoff potential
          (\<lambda>_. 1) n potential output))"
    by (rule slp_left_right_one_sided_output_density_real_all_orders_l2(3)[OF
          radius_nonnegative p_lower p_upper X_measurable X_bounded
          cutoff_measurable potential_lp potential_outside cutoff_bound
          C_nonnegative])
  show left_limit:
      "((\<lambda>i. integral\<^sup>L lborel (\<lambda>output.
          of_real (enn2real
            (slp_left_one_sided_output_density R cutoff potential
              (\<lambda>_. 1) n potential output)) * error i output))
        \<longlongrightarrow> 0) F"
    by (rule slp_real_complex_l2_pairing_limit[OF
          left_l2 error_l2 error_square_decay])
  show right_limit:
      "((\<lambda>i. integral\<^sup>L lborel (\<lambda>output.
          of_real (enn2real
            (slp_right_one_sided_output_density R cutoff potential
              (\<lambda>_. 1) n potential output)) * error i output))
        \<longlongrightarrow> 0) F"
    by (rule slp_real_complex_l2_pairing_limit[OF
          right_l2 error_l2 error_square_decay])
qed

end

end
