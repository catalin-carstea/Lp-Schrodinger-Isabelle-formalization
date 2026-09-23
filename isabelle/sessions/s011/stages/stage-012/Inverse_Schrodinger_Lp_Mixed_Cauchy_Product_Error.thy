theory Inverse_Schrodinger_Lp_Mixed_Cauchy_Product_Error
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Mixed_Product_Error_Limit"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Test_Two_Cauchy_Product_Half_HLS"
begin

hide_const (open) Commutative_Ring.norm

section \<open>The compact-test-weighted Cauchy-product error\<close>

context slp_mixed_center_error_hls_plancherel
begin

theorem slp_mixed_cauchy_product_error_tendsto_zero:
  fixes p :: real and Y :: "slp_point set"
    and cutoff q qt Q phi :: slp_scalar_field
    and left_orientation right_orientation :: slp_cauchy_orientation
  assumes p_lower: "1 < p" and p_upper: "p < 2"
    and target_bounded: "bounded Y" and target_measurable: "Y \<in> sets lborel"
    and cutoff_test: "slp_test_function_on Y cutoff"
    and q_lp: "aim_complex_lp_on_plane p q"
    and qt_lp: "aim_complex_lp_on_plane p qt"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and cutoff_q: "\<forall>x. cutoff x * q x = q x"
    and cutoff_qt: "\<forall>x. cutoff x * qt x = qt x"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> x \<in> Y"
    and phi_test: "slp_test_function_on UNIV phi"
  shows "((\<lambda>tau. integral\<^sup>L lborel
    (\<lambda>x. (slp_center_average tau
        (\<lambda>z. phi z * (slp_cauchy_transform left_orientation q z *
          slp_cauchy_transform right_orientation qt z)) x -
        phi x * (slp_cauchy_transform left_orientation q x *
          slp_cauchy_transform right_orientation qt x)) *
      slp_mixed_center_finite_oscillatory_kernel TYPE('i::finite) TYPE('j::finite)
        tau Q cutoff q cutoff qt x)) \<longlongrightarrow> 0) at_top"
proof -
  let ?F = "\<lambda>x. phi x * (slp_cauchy_transform left_orientation q x *
    slp_cauchy_transform right_orientation qt x)"
  let ?Z = "closure {x. phi x \<noteq> 0}"
  have Z_compact: "compact ?Z"
    using phi_test unfolding slp_test_function_on_def by blast
  have Z_bounded: "bounded ?Z"
    by (rule compact_imp_bounded[OF Z_compact])
  have Z_borel: "?Z \<in> sets borel"
    by (rule borel_closed[OF closed_closure])
  have Z_measurable: "?Z \<in> sets lborel"
    using Z_borel by (simp only: sets_lborel)
  have F_lp: "aim_complex_lp_on_plane (slp_mixed_product_exponent p) ?F"
    using slp_test_two_cauchy_product_half_hls_target_lp[
      where left_orientation=left_orientation and right_orientation=right_orientation,
      OF p_lower p_upper q_lp qt_lp phi_test]
    by (simp only: slp_mixed_product_exponent_def)
  have F_support: "x \<in> ?Z" if "?F x \<noteq> 0" for x
    using that closure_subset[of "{x. phi x \<noteq> 0}"] by auto
  show ?thesis
    by (rule slp_mixed_finite_product_error_tendsto_zero[
        OF p_lower p_upper target_bounded target_measurable cutoff_test
          q_lp qt_lp Q_lp cutoff_q cutoff_qt Q_support Z_bounded Z_measurable
          F_lp F_support])
qed

end

end
