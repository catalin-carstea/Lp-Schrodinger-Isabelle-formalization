theory Inverse_Schrodinger_Lp_Mixed_Center_Unit_Terminal_Fiber_Finite_Target
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Positive_Ennreal_Convolution_Finite_Target_Uniform_Power"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Output_Density_All_Order_Unit_Terminal_Finite_Target"
begin

section \<open>Unit-terminal mixed fibers at finite targets\<close>

context aim_planar_riesz_hls
begin

theorem slp_mixed_center_unit_terminal_fibers_finite_target:
  fixes R C p t :: real
    and cutoff left_potential right_potential ::
      "slp_point \<Rightarrow> complex"
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and t_lower: "1 < t"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and left_potential_lp: "aim_complex_lp_on_plane p left_potential"
    and right_potential_lp: "aim_complex_lp_on_plane p right_potential"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "\<And>left_order right_order. \<exists>K. 0 \<le> K \<and>
      (\<forall>root. slp_positive_ennreal_lp_on_plane t
        (slp_positive_ennreal_convolution
          (slp_left_positive_output_density R cutoff left_potential
            (\<lambda>_. 1) left_order root)
          (\<lambda>offset.
            slp_right_positive_output_density R cutoff right_potential
              (\<lambda>_. 1) right_order root (root + offset)))) \<and>
      (\<forall>root. integral\<^sup>L lborel
        (\<lambda>center. enn2real
          (slp_positive_ennreal_convolution
            (slp_left_positive_output_density R cutoff left_potential
              (\<lambda>_. 1) left_order root)
            (\<lambda>offset.
              slp_right_positive_output_density R cutoff right_potential
                (\<lambda>_. 1) right_order root (root + offset)) center)
          powr t) \<le> K)"
proof -
  note left_unit =
    slp_left_right_positive_output_density_all_orders_unit_terminal_finite_target[
      OF radius_nonnegative p_lower p_upper t_lower cutoff_measurable
        left_potential_lp cutoff_bound C_nonnegative]
  note right_unit =
    slp_left_right_positive_output_density_all_orders_unit_terminal_finite_target[
      OF radius_nonnegative p_lower p_upper t_lower cutoff_measurable
        right_potential_lp cutoff_bound C_nonnegative]
  show "\<exists>K. 0 \<le> K \<and>
      (\<forall>root. slp_positive_ennreal_lp_on_plane t
        (slp_positive_ennreal_convolution
          (slp_left_positive_output_density R cutoff left_potential
            (\<lambda>_. 1) left_order root)
          (\<lambda>offset.
            slp_right_positive_output_density R cutoff right_potential
              (\<lambda>_. 1) right_order root (root + offset)))) \<and>
      (\<forall>root. integral\<^sup>L lborel
        (\<lambda>center. enn2real
          (slp_positive_ennreal_convolution
            (slp_left_positive_output_density R cutoff left_potential
              (\<lambda>_. 1) left_order root)
            (\<lambda>offset.
              slp_right_positive_output_density R cutoff right_potential
                (\<lambda>_. 1) right_order root (root + offset)) center)
          powr t) \<le> K)"
    for left_order right_order
  proof -
    let ?a = "slp_mixed_unweighted_branch_exponent t"
    obtain A where A_nonnegative: "0 \<le> A"
      and left_lp: "\<forall>root. slp_positive_ennreal_lp_on_plane ?a
        (slp_left_positive_output_density R cutoff left_potential
          (\<lambda>_. 1) left_order root)"
      and left_bound: "\<forall>root. integral\<^sup>L lborel
        (\<lambda>output. enn2real
          (slp_left_positive_output_density R cutoff left_potential
            (\<lambda>_. 1) left_order root output) powr ?a) \<le> A"
      using left_unit(1)[of left_order] by blast
    obtain B where B_nonnegative: "0 \<le> B"
      and right_lp: "\<forall>root. slp_positive_ennreal_lp_on_plane ?a
        (slp_right_positive_output_density R cutoff right_potential
          (\<lambda>_. 1) right_order root)"
      and right_bound: "\<forall>root. integral\<^sup>L lborel
        (\<lambda>output. enn2real
          (slp_right_positive_output_density R cutoff right_potential
            (\<lambda>_. 1) right_order root output) powr ?a) \<le> B"
      using right_unit(2)[of right_order] by blast
    have shifted_lp:
        "slp_positive_ennreal_lp_on_plane ?a
          (\<lambda>offset.
            slp_right_positive_output_density R cutoff right_potential
              (\<lambda>_. 1) right_order root (root + offset))"
      for root
      by (rule slp_positive_ennreal_lp_translate(1)[OF
            right_lp[rule_format]])
    have shifted_bound:
        "integral\<^sup>L lborel
          (\<lambda>offset. enn2real
            (slp_right_positive_output_density R cutoff right_potential
              (\<lambda>_. 1) right_order root (root + offset)) powr ?a)
          \<le> B"
      for root
    proof -
      have translated:
          "integral\<^sup>L lborel
              (\<lambda>offset. enn2real
                (slp_right_positive_output_density R cutoff right_potential
                  (\<lambda>_. 1) right_order root (root + offset)) powr ?a) =
            integral\<^sup>L lborel
              (\<lambda>offset. enn2real
                (slp_right_positive_output_density R cutoff right_potential
                  (\<lambda>_. 1) right_order root offset) powr ?a)"
        by (rule slp_positive_ennreal_lp_translate(2)[OF
              right_lp[rule_format]])
      show ?thesis
        using translated right_bound[rule_format, of root] by simp
    qed
    note uniform =
      slp_positive_ennreal_convolution_finite_target_uniform_power[
        where F="\<lambda>root.
          slp_left_positive_output_density R cutoff left_potential
            (\<lambda>_. 1) left_order root"
        and G="\<lambda>root offset.
          slp_right_positive_output_density R cutoff right_potential
            (\<lambda>_. 1) right_order root (root + offset)", OF
        t_lower A_nonnegative B_nonnegative left_lp[rule_format] shifted_lp
        left_bound[rule_format] shifted_bound]
    show ?thesis using uniform(1) uniform(2) uniform(3) by blast
  qed
qed

end

end
