theory Inverse_Schrodinger_Lp_Test_Two_Cauchy_Product_Half_HLS
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Complex_Lp_Product_Closures"
begin

hide_const (open) Commutative_Ring.norm

section \<open>The compactly weighted two-Cauchy product\<close>

context aim_planar_hls_cauchy
begin

theorem slp_test_two_cauchy_product_half_hls_target_lp:
  assumes p_lower: "1 < p"
    and p_upper: "p < 2"
    and left_potential_lp:
      "aim_complex_lp_on_plane p left_potential"
    and right_potential_lp:
      "aim_complex_lp_on_plane p right_potential"
    and phi_test: "slp_test_function_on UNIV phi"
  shows
    "aim_complex_lp_on_plane (aim_hls_target_exponent p / 2)
      (\<lambda>x. phi x *
        (slp_cauchy_transform left_orientation left_potential x *
          slp_cauchy_transform right_orientation right_potential x))"
proof -
  let ?r = "aim_hls_target_exponent p"
  have target_above_two: "2 < ?r"
    by (rule slp_hls_target_exponent_above_two[OF p_lower p_upper])
  have half_target_positive: "0 < ?r / 2"
    using target_above_two by linarith
  have left_cauchy_lp:
      "aim_complex_lp_on_plane ?r
        (slp_cauchy_transform left_orientation left_potential)"
  proof (cases left_orientation)
    case SLP_Partial_Inverse
    then show ?thesis
      using slp_both_cauchy_hls p_lower p_upper left_potential_lp by blast
  next
    case SLP_Dbar_Inverse
    then show ?thesis
      using slp_both_cauchy_hls p_lower p_upper left_potential_lp by blast
  qed
  have right_cauchy_lp:
      "aim_complex_lp_on_plane ?r
        (slp_cauchy_transform right_orientation right_potential)"
  proof (cases right_orientation)
    case SLP_Partial_Inverse
    then show ?thesis
      using slp_both_cauchy_hls p_lower p_upper right_potential_lp by blast
  next
    case SLP_Dbar_Inverse
    then show ?thesis
      using slp_both_cauchy_hls p_lower p_upper right_potential_lp by blast
  qed
  have cauchy_product_lp:
      "aim_complex_lp_on_plane (?r / 2)
        (\<lambda>x.
          slp_cauchy_transform left_orientation left_potential x *
          slp_cauchy_transform right_orientation right_potential x)"
    by (rule slp_aim_complex_lp_on_plane_product[
          where q = ?r and r = ?r, OF half_target_positive])
      (use target_above_two left_cauchy_lp right_cauchy_lp in simp_all)
  have phi_integrable: "integrable lborel phi"
    by (rule slp_test_function_integrable_bounded(1)[OF phi_test])
  have phi_measurable: "phi \<in> borel_measurable lborel"
    using phi_integrable by measurable
  have phi_bounded: "bounded (range phi)"
    by (rule slp_test_function_integrable_bounded(2)[OF phi_test])
  obtain C where phi_bound:
      "\<And>x. norm_class.norm (phi x) \<le> C"
    using phi_bounded unfolding bounded_iff by auto
  have C_nonnegative: "0 \<le> C"
  proof -
    have "0 \<le> norm_class.norm (phi 0)"
      by simp
    then show ?thesis
      using phi_bound[of 0] by linarith
  qed
  show ?thesis
    by (rule slp_aim_complex_lp_on_plane_bounded_multiplier[OF
          half_target_positive phi_measurable phi_bound C_nonnegative
          cauchy_product_lp])
qed

end

end
