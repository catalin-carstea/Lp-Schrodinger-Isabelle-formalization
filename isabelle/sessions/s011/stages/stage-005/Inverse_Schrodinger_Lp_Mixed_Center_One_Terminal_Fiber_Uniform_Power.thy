theory Inverse_Schrodinger_Lp_Mixed_Center_One_Terminal_Fiber_Uniform_Power
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Positive_Ennreal_Convolution_Mixed_Uniform_Power"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Mixed_Center_One_Terminal_Fiber_L2"
begin

section \<open>Uniform square-power caps for one-terminal mixed fibers\<close>

context aim_planar_riesz_hls
begin

theorem slp_mixed_center_one_terminal_fibers_uniform_power:
  fixes R C p :: real
    and cutoff left_potential right_potential :: "slp_point \<Rightarrow> complex"
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and left_potential_lp: "aim_complex_lp_on_plane p left_potential"
    and right_potential_lp: "aim_complex_lp_on_plane p right_potential"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows left_terminal_right_unit:
    "\<And>left_order right_order. \<exists>K. 0 \<le> K \<and>
      (\<forall>root. slp_positive_ennreal_lp_on_plane 2
        (slp_positive_ennreal_convolution
          (slp_left_positive_output_density R cutoff left_potential
            (slp_positive_terminal_riesz_weight R left_potential)
            left_order root)
          (\<lambda>offset.
            slp_right_positive_output_density R cutoff right_potential
              (\<lambda>_. 1) right_order root (root + offset)))) \<and>
      (\<forall>root. integral\<^sup>L lborel
        (\<lambda>out. enn2real
          (slp_positive_ennreal_convolution
            (slp_left_positive_output_density R cutoff left_potential
              (slp_positive_terminal_riesz_weight R left_potential)
              left_order root)
            (\<lambda>offset.
              slp_right_positive_output_density R cutoff right_potential
                (\<lambda>_. 1) right_order root (root + offset)) out) powr 2)
        \<le> K)"
    and left_unit_right_terminal:
    "\<And>left_order right_order. \<exists>K. 0 \<le> K \<and>
      (\<forall>root. slp_positive_ennreal_lp_on_plane 2
        (slp_positive_ennreal_convolution
          (slp_left_positive_output_density R cutoff left_potential
            (\<lambda>_. 1) left_order root)
          (\<lambda>offset.
            slp_right_positive_output_density R cutoff right_potential
              (slp_positive_terminal_riesz_weight R right_potential)
              right_order root (root + offset)))) \<and>
      (\<forall>root. integral\<^sup>L lborel
        (\<lambda>out. enn2real
          (slp_positive_ennreal_convolution
            (slp_left_positive_output_density R cutoff left_potential
              (\<lambda>_. 1) left_order root)
            (\<lambda>offset.
              slp_right_positive_output_density R cutoff right_potential
                (slp_positive_terminal_riesz_weight R right_potential)
                right_order root (root + offset)) out) powr 2)
        \<le> K)"
proof -
  note exponents = slp_mixed_one_terminal_exponents[OF p_lower p_upper]
  note split = slp_mixed_one_terminal_convolution_exponents[OF
      p_lower p_upper]
  note left_weighted =
    slp_left_right_positive_output_density_all_orders_terminal_weighted[OF
      radius_nonnegative p_lower p_upper cutoff_measurable left_potential_lp
      cutoff_bound C_nonnegative]
  note right_weighted =
    slp_left_right_positive_output_density_all_orders_terminal_weighted[OF
      radius_nonnegative p_lower p_upper cutoff_measurable right_potential_lp
      cutoff_bound C_nonnegative]
  note left_unit =
    slp_left_right_positive_output_density_all_orders_unit_terminal_companion[OF
      radius_nonnegative p_lower p_upper cutoff_measurable left_potential_lp
      cutoff_bound C_nonnegative]
  note right_unit =
    slp_left_right_positive_output_density_all_orders_unit_terminal_companion[OF
      radius_nonnegative p_lower p_upper cutoff_measurable right_potential_lp
      cutoff_bound C_nonnegative]
  show "\<exists>K. 0 \<le> K \<and>
      (\<forall>root. slp_positive_ennreal_lp_on_plane 2
        (slp_positive_ennreal_convolution
          (slp_left_positive_output_density R cutoff left_potential
            (slp_positive_terminal_riesz_weight R left_potential)
            left_order root)
          (\<lambda>offset.
            slp_right_positive_output_density R cutoff right_potential
              (\<lambda>_. 1) right_order root (root + offset)))) \<and>
      (\<forall>root. integral\<^sup>L lborel
        (\<lambda>out. enn2real
          (slp_positive_ennreal_convolution
            (slp_left_positive_output_density R cutoff left_potential
              (slp_positive_terminal_riesz_weight R left_potential)
              left_order root)
            (\<lambda>offset.
              slp_right_positive_output_density R cutoff right_potential
                (\<lambda>_. 1) right_order root (root + offset)) out) powr 2)
        \<le> K)"
    for left_order right_order
  proof -
    obtain A where A_nonnegative: "0 \<le> A"
      and left_lp: "\<forall>root. slp_positive_ennreal_lp_on_plane
        (slp_branch_power_exponent p)
        (slp_left_positive_output_density R cutoff left_potential
          (slp_positive_terminal_riesz_weight R left_potential)
          left_order root)"
      and left_bound: "\<forall>root. integral\<^sup>L lborel
        (\<lambda>out. enn2real
          (slp_left_positive_output_density R cutoff left_potential
            (slp_positive_terminal_riesz_weight R left_potential)
            left_order root out) powr slp_branch_power_exponent p) \<le> A"
      using left_weighted(2)[of left_order] by blast
    obtain B where B_nonnegative: "0 \<le> B"
      and right_lp: "\<forall>root. slp_positive_ennreal_lp_on_plane
        (slp_mixed_unit_branch_exponent p)
        (slp_right_positive_output_density R cutoff right_potential
          (\<lambda>_. 1) right_order root)"
      and right_bound: "\<forall>root. integral\<^sup>L lborel
        (\<lambda>out. enn2real
          (slp_right_positive_output_density R cutoff right_potential
            (\<lambda>_. 1) right_order root out) powr
            slp_mixed_unit_branch_exponent p) \<le> B"
      using right_unit(2)[of right_order] by blast
    have shifted_lp:
        "slp_positive_ennreal_lp_on_plane
          (slp_mixed_unit_branch_exponent p)
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
              (\<lambda>_. 1) right_order root (root + offset)) powr
              slp_mixed_unit_branch_exponent p) \<le> B"
      for root
    proof -
      have translated:
          "integral\<^sup>L lborel
              (\<lambda>offset. enn2real
                (slp_right_positive_output_density R cutoff right_potential
                  (\<lambda>_. 1) right_order root (root + offset)) powr
                  slp_mixed_unit_branch_exponent p) =
            integral\<^sup>L lborel
              (\<lambda>offset. enn2real
                (slp_right_positive_output_density R cutoff right_potential
                  (\<lambda>_. 1) right_order root offset) powr
                  slp_mixed_unit_branch_exponent p)"
        by (rule slp_positive_ennreal_lp_translate(2)[OF
              right_lp[rule_format]])
      show ?thesis using translated right_bound[rule_format, of root]
        by simp
    qed
    note uniform = slp_positive_ennreal_convolution_mixed_uniform_power[
        where F="\<lambda>root.
          slp_left_positive_output_density R cutoff left_potential
            (slp_positive_terminal_riesz_weight R left_potential)
            left_order root"
        and G="\<lambda>root offset.
          slp_right_positive_output_density R cutoff right_potential
            (\<lambda>_. 1) right_order root (root + offset)", OF
        exponents(1) exponents(2) exponents(3) exponents(4)
        split(1) split(2) split(3) split(4) split(5)
        A_nonnegative B_nonnegative left_lp[rule_format] shifted_lp
        left_bound[rule_format] shifted_bound]
    show ?thesis using uniform(1) uniform(2) uniform(3) by blast
  qed
  show "\<exists>K. 0 \<le> K \<and>
      (\<forall>root. slp_positive_ennreal_lp_on_plane 2
        (slp_positive_ennreal_convolution
          (slp_left_positive_output_density R cutoff left_potential
            (\<lambda>_. 1) left_order root)
          (\<lambda>offset.
            slp_right_positive_output_density R cutoff right_potential
              (slp_positive_terminal_riesz_weight R right_potential)
              right_order root (root + offset)))) \<and>
      (\<forall>root. integral\<^sup>L lborel
        (\<lambda>out. enn2real
          (slp_positive_ennreal_convolution
            (slp_left_positive_output_density R cutoff left_potential
              (\<lambda>_. 1) left_order root)
            (\<lambda>offset.
              slp_right_positive_output_density R cutoff right_potential
                (slp_positive_terminal_riesz_weight R right_potential)
                right_order root (root + offset)) out) powr 2)
        \<le> K)"
    for left_order right_order
  proof -
    obtain A where A_nonnegative: "0 \<le> A"
      and left_lp: "\<forall>root. slp_positive_ennreal_lp_on_plane
        (slp_mixed_unit_branch_exponent p)
        (slp_left_positive_output_density R cutoff left_potential
          (\<lambda>_. 1) left_order root)"
      and left_bound: "\<forall>root. integral\<^sup>L lborel
        (\<lambda>out. enn2real
          (slp_left_positive_output_density R cutoff left_potential
            (\<lambda>_. 1) left_order root out) powr
            slp_mixed_unit_branch_exponent p) \<le> A"
      using left_unit(1)[of left_order] by blast
    obtain B where B_nonnegative: "0 \<le> B"
      and right_lp: "\<forall>root. slp_positive_ennreal_lp_on_plane
        (slp_branch_power_exponent p)
        (slp_right_positive_output_density R cutoff right_potential
          (slp_positive_terminal_riesz_weight R right_potential)
          right_order root)"
      and right_bound: "\<forall>root. integral\<^sup>L lborel
        (\<lambda>out. enn2real
          (slp_right_positive_output_density R cutoff right_potential
            (slp_positive_terminal_riesz_weight R right_potential)
            right_order root out) powr slp_branch_power_exponent p) \<le> B"
      using right_weighted(3)[of right_order] by blast
    have shifted_lp:
        "slp_positive_ennreal_lp_on_plane (slp_branch_power_exponent p)
          (\<lambda>offset.
            slp_right_positive_output_density R cutoff right_potential
              (slp_positive_terminal_riesz_weight R right_potential)
              right_order root (root + offset))"
      for root
      by (rule slp_positive_ennreal_lp_translate(1)[OF
            right_lp[rule_format]])
    have shifted_bound:
        "integral\<^sup>L lborel
          (\<lambda>offset. enn2real
            (slp_right_positive_output_density R cutoff right_potential
              (slp_positive_terminal_riesz_weight R right_potential)
              right_order root (root + offset)) powr
              slp_branch_power_exponent p) \<le> B"
      for root
    proof -
      have translated:
          "integral\<^sup>L lborel
              (\<lambda>offset. enn2real
                (slp_right_positive_output_density R cutoff right_potential
                  (slp_positive_terminal_riesz_weight R right_potential)
                  right_order root (root + offset)) powr
                  slp_branch_power_exponent p) =
            integral\<^sup>L lborel
              (\<lambda>offset. enn2real
                (slp_right_positive_output_density R cutoff right_potential
                  (slp_positive_terminal_riesz_weight R right_potential)
                  right_order root offset) powr slp_branch_power_exponent p)"
        by (rule slp_positive_ennreal_lp_translate(2)[OF
              right_lp[rule_format]])
      show ?thesis using translated right_bound[rule_format, of root]
        by simp
    qed
    have conjugate_swapped:
        "1 / slp_mixed_unit_split_exponent p +
          1 / slp_mixed_weight_split_exponent p = 1"
      using split(3) by linarith
    note uniform = slp_positive_ennreal_convolution_mixed_uniform_power[
        where F="\<lambda>root.
          slp_left_positive_output_density R cutoff left_potential
            (\<lambda>_. 1) left_order root"
        and G="\<lambda>root offset.
          slp_right_positive_output_density R cutoff right_potential
            (slp_positive_terminal_riesz_weight R right_potential)
            right_order root (root + offset)", OF
        exponents(3) exponents(4) exponents(1) exponents(2)
        split(2) split(1) conjugate_swapped split(5) split(4)
        A_nonnegative B_nonnegative left_lp[rule_format] shifted_lp
        left_bound[rule_format] shifted_bound]
    show ?thesis using uniform(1) uniform(2) uniform(3) by blast
  qed
qed

end

end
