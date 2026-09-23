theory Inverse_Schrodinger_Lp_W1p_Valid_Pair_Guards
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Semantics"
begin

section \<open>Guard facts for valid first-order Sobolev pairs\<close>

theorem slp_w1p_pair_onD:
  assumes pair: "slp_w1p_pair_on p X u Du"
  shows weak_gradient: "slp_weak_gradient_on X u Du"
    and function_lp: "slp_complex_lp_on p X u"
    and derivative_zero_lp: "slp_complex_lp_on p X (\<lambda>x. Du x $ 0)"
    and derivative_one_lp: "slp_complex_lp_on p X (\<lambda>x. Du x $ 1)"
  using pair unfolding slp_w1p_pair_on_def by auto

theorem slp_w1p_pair_power_integrable:
  assumes pair: "slp_w1p_pair_on p X u Du"
  shows function_power:
      "integrable lborel
        (\<lambda>x. Real_Vector_Spaces.norm (slp_restrict_field X u x) powr p)"
    and derivative_zero_power:
      "integrable lborel
        (\<lambda>x. Real_Vector_Spaces.norm
          (slp_restrict_field X (\<lambda>y. Du y $ 0) x) powr p)"
    and derivative_one_power:
      "integrable lborel
        (\<lambda>x. Real_Vector_Spaces.norm
          (slp_restrict_field X (\<lambda>y. Du y $ 1) x) powr p)"
proof -
  have function_plane:
      "aim_complex_lp_on_plane p (slp_restrict_field X u)"
    using slp_w1p_pair_onD(2)[OF pair]
    unfolding slp_complex_lp_on_def .
  have derivative_zero_plane:
      "aim_complex_lp_on_plane p
        (slp_restrict_field X (\<lambda>y. Du y $ 0))"
    using slp_w1p_pair_onD(3)[OF pair]
    unfolding slp_complex_lp_on_def .
  have derivative_one_plane:
      "aim_complex_lp_on_plane p
        (slp_restrict_field X (\<lambda>y. Du y $ 1))"
    using slp_w1p_pair_onD(4)[OF pair]
    unfolding slp_complex_lp_on_def .
  show "integrable lborel
      (\<lambda>x. Real_Vector_Spaces.norm (slp_restrict_field X u x) powr p)"
    using function_plane unfolding aim_complex_lp_on_plane_def by auto
  show "integrable lborel
      (\<lambda>x. Real_Vector_Spaces.norm
        (slp_restrict_field X (\<lambda>y. Du y $ 0) x) powr p)"
    using derivative_zero_plane unfolding aim_complex_lp_on_plane_def by auto
  show "integrable lborel
      (\<lambda>x. Real_Vector_Spaces.norm
        (slp_restrict_field X (\<lambda>y. Du y $ 1) x) powr p)"
    using derivative_one_plane unfolding aim_complex_lp_on_plane_def by auto
qed

theorem slp_w1p_pair_difference_lp_components:
  assumes exponent_one_le: "1 \<le> p"
    and first_pair: "slp_w1p_pair_on p X u Du"
    and second_pair: "slp_w1p_pair_on p X v Dv"
  shows function_difference:
      "slp_complex_lp_on p X (\<lambda>x. u x - v x)"
    and derivative_zero_difference:
      "slp_complex_lp_on p X (\<lambda>x. (Du x - Dv x) $ 0)"
    and derivative_one_difference:
      "slp_complex_lp_on p X (\<lambda>x. (Du x - Dv x) $ 1)"
proof -
  have exponent_positive: "0 < p"
    using exponent_one_le by linarith
  have function_plane:
      "aim_complex_lp_on_plane p
        (\<lambda>x. slp_restrict_field X u x - slp_restrict_field X v x)"
    by (rule aim_complex_lp_on_plane_diff[OF exponent_positive])
      (use first_pair second_pair in
        \<open>auto simp: slp_w1p_pair_on_def slp_complex_lp_on_def\<close>)
  have derivative_zero_plane:
      "aim_complex_lp_on_plane p
        (\<lambda>x. slp_restrict_field X (\<lambda>y. Du y $ 0) x -
          slp_restrict_field X (\<lambda>y. Dv y $ 0) x)"
    by (rule aim_complex_lp_on_plane_diff[OF exponent_positive])
      (use first_pair second_pair in
        \<open>auto simp: slp_w1p_pair_on_def slp_complex_lp_on_def\<close>)
  have derivative_one_plane:
      "aim_complex_lp_on_plane p
        (\<lambda>x. slp_restrict_field X (\<lambda>y. Du y $ 1) x -
          slp_restrict_field X (\<lambda>y. Dv y $ 1) x)"
    by (rule aim_complex_lp_on_plane_diff[OF exponent_positive])
      (use first_pair second_pair in
        \<open>auto simp: slp_w1p_pair_on_def slp_complex_lp_on_def\<close>)
  have function_restriction:
      "slp_restrict_field X (\<lambda>x. u x - v x) =
        (\<lambda>x. slp_restrict_field X u x - slp_restrict_field X v x)"
    by (rule ext) (simp add: slp_restrict_field_def)
  have derivative_zero_restriction:
      "slp_restrict_field X (\<lambda>x. (Du x - Dv x) $ 0) =
        (\<lambda>x. slp_restrict_field X (\<lambda>y. Du y $ 0) x -
          slp_restrict_field X (\<lambda>y. Dv y $ 0) x)"
    by (rule ext) (simp add: slp_restrict_field_def)
  have derivative_one_restriction:
      "slp_restrict_field X (\<lambda>x. (Du x - Dv x) $ 1) =
        (\<lambda>x. slp_restrict_field X (\<lambda>y. Du y $ 1) x -
          slp_restrict_field X (\<lambda>y. Dv y $ 1) x)"
    by (rule ext) (simp add: slp_restrict_field_def)
  show "slp_complex_lp_on p X (\<lambda>x. u x - v x)"
    unfolding slp_complex_lp_on_def function_restriction
    by (rule function_plane)
  show "slp_complex_lp_on p X (\<lambda>x. (Du x - Dv x) $ 0)"
    unfolding slp_complex_lp_on_def derivative_zero_restriction
    by (rule derivative_zero_plane)
  show "slp_complex_lp_on p X (\<lambda>x. (Du x - Dv x) $ 1)"
    unfolding slp_complex_lp_on_def derivative_one_restriction
    by (rule derivative_one_plane)
qed

end
