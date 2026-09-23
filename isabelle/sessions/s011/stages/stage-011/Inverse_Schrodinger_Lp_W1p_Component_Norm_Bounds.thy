theory Inverse_Schrodinger_Lp_W1p_Component_Norm_Bounds
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Wirtinger_Coordinate_Bound"
begin

section \<open>Component bounds carried by the reviewed Sobolev norm\<close>

theorem slp_w1p_norm_on_component_bounds:
  assumes exponent_positive: "0 < p"
    and pair: "slp_w1p_pair_on p X u Du"
  shows function_component:
      "aim_complex_lp_on_plane p (slp_restrict_field X u) \<and>
        aim_complex_lp_norm p (slp_restrict_field X u)
          \<le> slp_w1p_norm_on p X u Du"
    and derivative_zero_component:
      "aim_complex_lp_on_plane p
          (slp_restrict_field X (\<lambda>x. Du x $ 0)) \<and>
        aim_complex_lp_norm p
          (slp_restrict_field X (\<lambda>x. Du x $ 0))
          \<le> slp_w1p_norm_on p X u Du"
    and derivative_one_component:
      "aim_complex_lp_on_plane p
          (slp_restrict_field X (\<lambda>x. Du x $ 1)) \<and>
        aim_complex_lp_norm p
          (slp_restrict_field X (\<lambda>x. Du x $ 1))
          \<le> slp_w1p_norm_on p X u Du"
proof -
  let ?U = "integral\<^sup>L lborel
    (\<lambda>x. Real_Vector_Spaces.norm (slp_restrict_field X u x) powr p)"
  let ?D0 = "integral\<^sup>L lborel
    (\<lambda>x. Real_Vector_Spaces.norm
      (slp_restrict_field X (\<lambda>y. Du y $ 0) x) powr p)"
  let ?D1 = "integral\<^sup>L lborel
    (\<lambda>x. Real_Vector_Spaces.norm
      (slp_restrict_field X (\<lambda>y. Du y $ 1) x) powr p)"
  have inverse_nonnegative: "0 \<le> 1 / p"
    using exponent_positive by simp
  have U_nonnegative: "0 \<le> ?U"
    by (rule integral_nonneg_AE) simp
  have D0_nonnegative: "0 \<le> ?D0"
    by (rule integral_nonneg_AE) simp
  have D1_nonnegative: "0 \<le> ?D1"
    by (rule integral_nonneg_AE) simp
  have U_bound: "?U \<le> ?U + ?D0 + ?D1"
    using D0_nonnegative D1_nonnegative by linarith
  have D0_bound: "?D0 \<le> ?U + ?D0 + ?D1"
    using U_nonnegative D1_nonnegative by linarith
  have D1_bound: "?D1 \<le> ?U + ?D0 + ?D1"
    using U_nonnegative D0_nonnegative by linarith
  have U_root_bound:
      "?U powr (1 / p) \<le> (?U + ?D0 + ?D1) powr (1 / p)"
    by (rule powr_mono2[OF inverse_nonnegative U_nonnegative U_bound])
  have D0_root_bound:
      "?D0 powr (1 / p) \<le> (?U + ?D0 + ?D1) powr (1 / p)"
    by (rule powr_mono2[OF inverse_nonnegative D0_nonnegative D0_bound])
  have D1_root_bound:
      "?D1 powr (1 / p) \<le> (?U + ?D0 + ?D1) powr (1 / p)"
    by (rule powr_mono2[OF inverse_nonnegative D1_nonnegative D1_bound])
  have function_lp:
      "aim_complex_lp_on_plane p (slp_restrict_field X u)"
    using slp_w1p_pair_onD(2)[OF pair]
    unfolding slp_complex_lp_on_def .
  have derivative_zero_lp:
      "aim_complex_lp_on_plane p
        (slp_restrict_field X (\<lambda>x. Du x $ 0))"
    using slp_w1p_pair_onD(3)[OF pair]
    unfolding slp_complex_lp_on_def .
  have derivative_one_lp:
      "aim_complex_lp_on_plane p
        (slp_restrict_field X (\<lambda>x. Du x $ 1))"
    using slp_w1p_pair_onD(4)[OF pair]
    unfolding slp_complex_lp_on_def .
  show "aim_complex_lp_on_plane p (slp_restrict_field X u) \<and>
      aim_complex_lp_norm p (slp_restrict_field X u)
        \<le> slp_w1p_norm_on p X u Du"
    unfolding aim_complex_lp_norm_def slp_w1p_norm_on_def
    using function_lp U_root_bound by blast
  show "aim_complex_lp_on_plane p
        (slp_restrict_field X (\<lambda>x. Du x $ 0)) \<and>
      aim_complex_lp_norm p
        (slp_restrict_field X (\<lambda>x. Du x $ 0))
        \<le> slp_w1p_norm_on p X u Du"
    unfolding aim_complex_lp_norm_def slp_w1p_norm_on_def
    using derivative_zero_lp D0_root_bound by blast
  show "aim_complex_lp_on_plane p
        (slp_restrict_field X (\<lambda>x. Du x $ 1)) \<and>
      aim_complex_lp_norm p
        (slp_restrict_field X (\<lambda>x. Du x $ 1))
        \<le> slp_w1p_norm_on p X u Du"
    unfolding aim_complex_lp_norm_def slp_w1p_norm_on_def
    using derivative_one_lp D1_root_bound by blast
qed

end
