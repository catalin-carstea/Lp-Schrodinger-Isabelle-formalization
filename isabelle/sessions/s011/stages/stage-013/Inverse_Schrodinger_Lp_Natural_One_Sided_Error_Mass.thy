theory Inverse_Schrodinger_Lp_Natural_One_Sided_Error_Mass
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_Mixed_Smooth_Cross_Error_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Root_Positive_Order_L2"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_One_Sided_Root_Lp"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Test_Cauchy_Product_L2"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Independent-root one-sided densities and physical errors\<close>

context aim_planar_riesz_hls
begin

theorem slp_natural_one_sided_unit_density_l2:
  fixes R C p :: real and X :: "slp_point set"
    and cutoff q Q :: slp_scalar_field
  assumes R_nonnegative: "0 \<le> R"
    and p_lower: "1 < p" and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel" and X_bounded: "bounded X"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and q_lp: "aim_complex_lp_on_plane p q"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and Q_outside: "\<And>x. x \<notin> X \<Longrightarrow> Q x = 0"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows "slp_positive_ennreal_lp_on_plane 2
    (slp_positive_root_output_density R cutoff q (\<lambda>_. 1) n Q)"
proof -
  let ?D = "slp_positive_root_output_density R cutoff q (\<lambda>_. 1) n Q"
  have q_measurable: "q \<in> borel_measurable lborel"
    and Q_measurable: "Q \<in> borel_measurable lborel"
    using q_lp Q_lp unfolding aim_complex_lp_on_plane_def by blast+
  have D_measurable: "?D \<in> borel_measurable lborel"
    by (rule slp_positive_root_output_density_measurable[
      OF cutoff_measurable q_measurable _ Q_measurable]) measurable
  have mass: "nn_integral lborel ?D < top_class.top"
    by (rule slp_positive_root_output_density_unweighted_mass_finite_lp_root[
      OF R_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable q_lp Q_lp Q_outside cutoff_bound C_nonnegative])
  have mass_ne: "nn_integral lborel ?D \<noteq> \<infinity>"
    using mass by simp
  have D_finite: "AE x in lborel. ?D x < top_class.top"
    using nn_integral_PInf_AE[OF D_measurable mass_ne] by (simp add: less_top)
  have Q_support: "bounded {x. Q x \<noteq> 0}"
    by (rule bounded_subset[OF X_bounded]) (use Q_outside in blast)
  have real_l2: "aim_real_lp_on_plane 2
      (slp_positive_root_output_density_real R cutoff q (\<lambda>_. 1) n Q)"
  proof (cases n)
    case 0
    have base: "aim_real_lp_on_plane 2
        (slp_positive_root_output_density_real R cutoff Q (\<lambda>_. 1) 0 Q)"
      by (rule slp_positive_root_output_density_real_zero_l2[
        OF R_nonnegative p_lower p_upper cutoff_measurable Q_lp
          Q_support cutoff_bound C_nonnegative])
    have zero_eq:
      "slp_positive_root_output_density_real R cutoff q (\<lambda>_. 1) 0 Q =
       slp_positive_root_output_density_real R cutoff Q (\<lambda>_. 1) 0 Q"
      by (rule ext)
        (simp add: slp_positive_root_output_density_real_def
          slp_positive_root_output_density_def)
    show ?thesis using base 0 zero_eq by simp
  next
    case (Suc k)
    show ?thesis
      using slp_positive_root_output_density_real_positive_order_l2[
        where n=k, OF R_nonnegative p_lower p_upper X_measurable X_bounded
          cutoff_measurable q_lp Q_lp Q_outside cutoff_bound C_nonnegative]
        Suc by simp
  qed
  have power: "integrable lborel (\<lambda>x. enn2real (?D x) powr 2)"
    using real_l2
    unfolding aim_real_lp_on_plane_def slp_positive_root_output_density_real_def
    by simp
  show ?thesis
    unfolding slp_positive_ennreal_lp_on_plane_def
    using D_measurable D_finite power by blast
qed

end

context aim_planar_riesz_hls_cauchy
begin

theorem slp_natural_one_sided_cauchy_error_mass_decay:
  fixes R C p :: real and X :: "slp_point set"
    and cutoff q Q phi :: slp_scalar_field
  assumes R_nonnegative: "0 \<le> R"
    and p_lower: "1 < p" and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel" and X_bounded: "bounded X"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and q_lp: "aim_complex_lp_on_plane p q"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and Q_outside: "\<And>x. x \<notin> X \<Longrightarrow> Q x = 0"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and fourier_plancherel: "hormander_euclidean_l2_fourier_plancherel_claim"
    and phi_test: "slp_test_function_on UNIV phi"
  shows "((\<lambda>tau. nn_integral lborel (\<lambda>u.
    slp_positive_root_output_density R cutoff q (\<lambda>_. 1) n Q u *
      ennreal (norm (slp_center_average tau
        (\<lambda>x. phi x * slp_cauchy_transform orientation q x) u -
        phi u * slp_cauchy_transform orientation q u)))) \<longlongrightarrow> 0) at_top"
proof -
  let ?D = "slp_positive_root_output_density R cutoff q (\<lambda>_. 1) n Q"
  let ?h = "\<lambda>x. phi x * slp_cauchy_transform orientation q x"
  have D_l2: "slp_positive_ennreal_lp_on_plane 2 ?D"
    by (rule slp_natural_one_sided_unit_density_l2[
      OF R_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable q_lp Q_lp Q_outside cutoff_bound C_nonnegative])
  have h_integrable: "integrable lborel ?h"
    by (rule slp_test_cauchy_product_integrable[OF p_lower p_upper q_lp phi_test])
  have h_l2: "aim_complex_lp_on_plane 2 ?h"
    by (rule slp_test_cauchy_product_l2[OF p_lower p_upper q_lp phi_test])
  show ?thesis
    by (rule slp_positive_l2_center_error_mass_decay[
      OF fourier_plancherel D_l2 h_integrable h_l2])
qed

end

end
