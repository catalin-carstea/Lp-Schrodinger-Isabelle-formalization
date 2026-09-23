theory Inverse_Schrodinger_Lp_Mixed_Cauchy_Preaverage
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Mixed_Preaverage_Fubini"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Pre-averaged Fubini from the original coefficients\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_mixed_cauchy_unit_center_amplitudes_integrable:
  fixes left_type :: "'i::finite itself" and right_type :: "'j::finite itself"
    and p tau :: real and Y :: "slp_point set"
    and Q cutoff q qt :: slp_scalar_field
    and lo ro :: slp_cauchy_orientation
  assumes p_lower: "1 < p" and p_upper: "p < 2"
    and Y_bounded: "bounded Y" and Y_measurable: "Y \<in> sets lborel"
    and cutoff_test: "slp_test_function_on Y cutoff"
    and q_lp: "aim_complex_lp_on_plane p q"
    and qt_lp: "aim_complex_lp_on_plane p qt"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and cutoff_q: "\<forall>x. cutoff x * q x = q x"
    and cutoff_qt: "\<forall>x. cutoff x * qt x = qt x"
    and Q_in: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> x \<in> Y"
  shows "integrable lborel (\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_weighted_oscillatory_integrand tau
        Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) (\<lambda>_. 1) (fst y) (snd y))"
    and "integrable lborel (\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_weighted_oscillatory_integrand tau
        Q cutoff q (slp_cauchy_transform lo q) cutoff qt (\<lambda>_. 1) (\<lambda>_. 1) (fst y) (snd y))"
    and "integrable lborel (\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_weighted_oscillatory_integrand tau
        Q cutoff q (\<lambda>_. 1) cutoff qt (slp_cauchy_transform ro qt) (\<lambda>_. 1) (fst y) (snd y))"
    and "integrable lborel (\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_weighted_oscillatory_integrand tau
        Q cutoff q (\<lambda>_. 1) cutoff qt (\<lambda>_. 1) (\<lambda>_. 1) (fst y) (snd y))"
proof -
  obtain R M where R_nonnegative: "0 \<le> (R::real)"
    and M_nonnegative: "0 \<le> (M::real)"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> M"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and q_support: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and qt_support: "\<And>x. qt x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
  proof (rule slp_test_cutoff_bounded_geometry[
      where Y=Y and cutoff=cutoff and q=q and qt=qt and Q=Q,
      OF Y_bounded cutoff_test cutoff_q cutoff_qt Q_in])
    fix R M :: real
    assume R: "0 \<le> R" and M: "0 \<le> M"
      and measurable: "cutoff \<in> borel_measurable lborel"
      and bound: "\<And>x. norm (cutoff x) \<le> M"
      and Q: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
      and cutoff: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
      and q: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
      and qt: "\<And>x. qt x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    show thesis by (rule that[OF R M measurable bound Q cutoff q qt])
  qed
  have Q_outside: "Q x = 0" if "x \<notin> Y" for x using Q_in that by blast
  have Q_measurable: "Q \<in> borel_measurable lborel"
    using Q_lp unfolding aim_complex_lp_on_plane_def by blast
  have q_measurable: "q \<in> borel_measurable lborel"
    using q_lp unfolding aim_complex_lp_on_plane_def by blast
  have qt_measurable: "qt \<in> borel_measurable lborel"
    using qt_lp unfolding aim_complex_lp_on_plane_def by blast
  let ?A = "slp_cauchy_transform lo q"
  let ?B = "slp_cauchy_transform ro qt"
  have A_measurable: "?A \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF p_lower p_upper q_lp])
  have B_measurable: "?B \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF p_lower p_upper qt_lp])
  have unit_measurable: "(\<lambda>_::slp_point. 1::complex) \<in> borel_measurable lborel"
    by measurable
  have unit_bound: "norm ((\<lambda>_::slp_point. 1::complex) x) \<le> 1" for x by simp
  have mass0: "(\<integral>\<^sup>+ center. slp_mixed_center_finite_weighted_absolute_fiber_mass
      TYPE('i) TYPE('j) Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) (\<lambda>_. 1) center \<partial>lborel) < top_class.top"
    by (rule slp_mixed_center_finite_weighted_absolute_mass_cauchy_finite[OF
        R_nonnegative M_nonnegative p_lower p_upper Y_measurable Y_bounded
        cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound unit_bound
        Q_support cutoff_support q_support qt_support])
  note cross = slp_mixed_cauchy_unit_center_cross_masses[
      where 'i='i and 'j='j, OF p_lower p_upper Y_bounded Y_measurable cutoff_test q_lp qt_lp Q_lp
      cutoff_q cutoff_qt Q_in]
  have mass1: "(\<integral>\<^sup>+ center. slp_mixed_center_finite_weighted_absolute_fiber_mass
      TYPE('i) TYPE('j) Q cutoff q (slp_cauchy_transform lo q) cutoff qt (\<lambda>_. 1) (\<lambda>_. 1) center \<partial>lborel) < top_class.top" using cross(1) by blast
  have mass2: "(\<integral>\<^sup>+ center. slp_mixed_center_finite_weighted_absolute_fiber_mass
      TYPE('i) TYPE('j) Q cutoff q (\<lambda>_. 1) cutoff qt (slp_cauchy_transform ro qt) (\<lambda>_. 1) center \<partial>lborel) < top_class.top" using cross(2) by blast
  have mass3: "(\<integral>\<^sup>+ center. slp_mixed_center_finite_weighted_absolute_fiber_mass
      TYPE('i) TYPE('j) Q cutoff q (\<lambda>_. 1) cutoff qt (\<lambda>_. 1) (\<lambda>_. 1) center \<partial>lborel) < top_class.top"
    by (rule slp_mixed_unit_terminal_bounded_mass[OF p_lower p_upper Y_bounded Y_measurable cutoff_test q_lp qt_lp Q_lp
      cutoff_q cutoff_qt Q_in unit_bound])
  show "integrable lborel (\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_weighted_oscillatory_integrand tau
        Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) (\<lambda>_. 1) (fst y) (snd y))"
    by (rule slp_mixed_weighted_joint_integrable_of_global_mass(2)[OF
        Q_measurable cutoff_measurable q_measurable A_measurable cutoff_measurable
        qt_measurable B_measurable unit_measurable mass0])
  show "integrable lborel (\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_weighted_oscillatory_integrand tau
        Q cutoff q (slp_cauchy_transform lo q) cutoff qt (\<lambda>_. 1) (\<lambda>_. 1) (fst y) (snd y))"
    by (rule slp_mixed_weighted_joint_integrable_of_global_mass(2)[OF
        Q_measurable cutoff_measurable q_measurable A_measurable cutoff_measurable
        qt_measurable unit_measurable unit_measurable mass1])
  show "integrable lborel (\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_weighted_oscillatory_integrand tau
        Q cutoff q (\<lambda>_. 1) cutoff qt (slp_cauchy_transform ro qt) (\<lambda>_. 1) (fst y) (snd y))"
    by (rule slp_mixed_weighted_joint_integrable_of_global_mass(2)[OF
        Q_measurable cutoff_measurable q_measurable unit_measurable cutoff_measurable
        qt_measurable B_measurable unit_measurable mass2])
  show "integrable lborel (\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_weighted_oscillatory_integrand tau
        Q cutoff q (\<lambda>_. 1) cutoff qt (\<lambda>_. 1) (\<lambda>_. 1) (fst y) (snd y))"
    by (rule slp_mixed_weighted_joint_integrable_of_global_mass(2)[OF
        Q_measurable cutoff_measurable q_measurable unit_measurable cutoff_measurable
        qt_measurable unit_measurable unit_measurable mass3])
qed

theorem slp_mixed_cauchy_preaverage_bracket:
  fixes left_type :: "'i::finite itself" and right_type :: "'j::finite itself"
    and p tau :: real and Y :: "slp_point set"
    and Q cutoff q qt phi :: slp_scalar_field
    and lo ro :: slp_cauchy_orientation
  assumes p_lower: "1 < p" and p_upper: "p < 2"
    and Y_bounded: "bounded Y" and Y_measurable: "Y \<in> sets lborel"
    and cutoff_test: "slp_test_function_on Y cutoff"
    and q_lp: "aim_complex_lp_on_plane p q"
    and qt_lp: "aim_complex_lp_on_plane p qt"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and cutoff_q: "\<forall>x. cutoff x * q x = q x"
    and cutoff_qt: "\<forall>x. cutoff x * qt x = qt x"
    and Q_in: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> x \<in> Y"
    and phi_test: "slp_test_function_on UNIV phi"
  shows "integrable lborel (\<lambda>z :: slp_point \<times> (slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates).
      slp_mixed_preaverage_integrand tau Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) phi (fst z) (fst (snd z)) (snd (snd z)))"
    and "integrable lborel (\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_bracket_integrand tau Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) phi (fst y) (snd y))"
    and "of_real (tau / pi) * integral\<^sup>L lborel
      (\<lambda>target. integral\<^sup>L lborel
        (\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
          slp_mixed_preaverage_integrand tau Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) phi target (fst y) (snd y))) =
      integral\<^sup>L lborel (slp_mixed_center_finite_bracket_kernel TYPE('i) TYPE('j) tau
      Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) phi)"
proof -
  have phi_integrable: "integrable lborel phi"
    by (rule slp_test_function_integrable_bounded(1)[OF phi_test])
  have phi_B_integrable: "integrable lborel (\<lambda>x. phi x * slp_cauchy_transform ro qt x)"
    by (rule slp_test_cauchy_product_integrable[OF p_lower p_upper qt_lp phi_test])
  have phi_A_integrable: "integrable lborel (\<lambda>x. phi x * slp_cauchy_transform lo q x)"
    by (rule slp_test_cauchy_product_integrable[OF p_lower p_upper q_lp phi_test])
  have phi_AB_integrable: "integrable lborel (\<lambda>x. phi x *
      (slp_cauchy_transform lo q x * slp_cauchy_transform ro qt x))"
    by (rule slp_test_two_cauchy_product_integrable[OF p_lower p_upper q_lp qt_lp phi_test])
  note amplitudes = slp_mixed_cauchy_unit_center_amplitudes_integrable[
      where 'i='i and 'j='j and tau=tau, OF p_lower p_upper Y_bounded Y_measurable cutoff_test q_lp qt_lp Q_lp
      cutoff_q cutoff_qt Q_in]
  have amplitude0: "integrable lborel (\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_weighted_oscillatory_integrand tau
        Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) (\<lambda>_. 1) (fst y) (snd y))" using amplitudes(1) by blast
  have amplitude1: "integrable lborel (\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_weighted_oscillatory_integrand tau
        Q cutoff q (slp_cauchy_transform lo q) cutoff qt (\<lambda>_. 1) (\<lambda>_. 1) (fst y) (snd y))" using amplitudes(2) by blast
  have amplitude2: "integrable lborel (\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_weighted_oscillatory_integrand tau
        Q cutoff q (\<lambda>_. 1) cutoff qt (slp_cauchy_transform ro qt) (\<lambda>_. 1) (fst y) (snd y))" using amplitudes(3) by blast
  have amplitude3: "integrable lborel (\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_weighted_oscillatory_integrand tau
        Q cutoff q (\<lambda>_. 1) cutoff qt (\<lambda>_. 1) (\<lambda>_. 1) (fst y) (snd y))" using amplitudes(4) by blast
  show "integrable lborel (\<lambda>z :: slp_point \<times> (slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates).
      slp_mixed_preaverage_integrand tau Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) phi (fst z) (fst (snd z)) (snd (snd z)))"
    by (rule slp_mixed_preaverage_integrable(1)[OF phi_integrable phi_B_integrable phi_A_integrable phi_AB_integrable
        amplitude0 amplitude1 amplitude2 amplitude3])
  show "integrable lborel (\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_bracket_integrand tau Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) phi (fst y) (snd y))"
    by (rule slp_mixed_preaverage_bracket_fubini(1)[OF phi_integrable phi_B_integrable phi_A_integrable phi_AB_integrable
        amplitude0 amplitude1 amplitude2 amplitude3])
  show "of_real (tau / pi) * integral\<^sup>L lborel
      (\<lambda>target. integral\<^sup>L lborel
        (\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
          slp_mixed_preaverage_integrand tau Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) phi target (fst y) (snd y))) =
      integral\<^sup>L lborel (slp_mixed_center_finite_bracket_kernel TYPE('i) TYPE('j) tau
      Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) phi)"
    by (rule slp_mixed_preaverage_bracket_fubini(2)[OF phi_integrable phi_B_integrable phi_A_integrable phi_AB_integrable
        amplitude0 amplitude1 amplitude2 amplitude3])
qed

end

end
