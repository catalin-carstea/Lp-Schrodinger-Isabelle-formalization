theory Inverse_Schrodinger_Lp_Mixed_Bracket_Absolute_Convergence
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Mixed_Joint_Integrability"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Center_Average_L2"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Absolute convergence of the literal four-average mixed bracket\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_mixed_cauchy_average_masses:
  fixes left_type :: "'i::finite itself" and right_type :: "'j::finite itself"
    and p tau :: real and Y :: "slp_point set"
    and cutoff q qt Q phi :: slp_scalar_field
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
    and plancherel: "hormander_euclidean_l2_fourier_plancherel_claim"
    and frequency: "0 < tau"
  shows "nn_integral lborel (slp_mixed_center_finite_weighted_absolute_fiber_mass
      TYPE('i) TYPE('j) Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) (slp_center_average tau phi)) < top_class.top"
    and "nn_integral lborel (slp_mixed_center_finite_weighted_absolute_fiber_mass
      TYPE('i) TYPE('j) Q cutoff q (slp_cauchy_transform lo q) cutoff qt (\<lambda>_. 1) (slp_center_average tau (\<lambda>x. phi x * (slp_cauchy_transform ro qt) x))) < top_class.top"
    and "nn_integral lborel (slp_mixed_center_finite_weighted_absolute_fiber_mass
      TYPE('i) TYPE('j) Q cutoff q (\<lambda>_. 1) cutoff qt (slp_cauchy_transform ro qt) (slp_center_average tau (\<lambda>x. phi x * (slp_cauchy_transform lo q) x))) < top_class.top"
    and "nn_integral lborel (slp_mixed_center_finite_weighted_absolute_fiber_mass
      TYPE('i) TYPE('j) Q cutoff q (\<lambda>_. 1) cutoff qt (\<lambda>_. 1) (slp_center_average tau (\<lambda>x. phi x * ((slp_cauchy_transform lo q) x * (slp_cauchy_transform ro qt) x)))) < top_class.top"
proof -
  interpret hf: hormander_euclidean_l2_fourier_plancherel
    by unfold_locales (rule plancherel)
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
  have smooth_bound: "norm (slp_center_average tau phi x) \<le>
      norm (of_real (tau / pi)::complex) * integral\<^sup>L lborel (\<lambda>z. norm (phi z))" for x
    by (rule slp_center_average_fixed_tau_bound)
  show "nn_integral lborel (slp_mixed_center_finite_weighted_absolute_fiber_mass
      TYPE('i) TYPE('j) Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) (slp_center_average tau phi)) < top_class.top"
    by (rule slp_mixed_center_finite_weighted_absolute_mass_cauchy_finite[OF
        R_nonnegative M_nonnegative p_lower p_upper Y_measurable Y_bounded
        cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound smooth_bound
        Q_support cutoff_support q_support qt_support])
  have left_source_l1: "integrable lborel (\<lambda>x. phi x * ?B x)"
    by (rule slp_test_cauchy_product_integrable[OF p_lower p_upper qt_lp phi_test])
  have left_source_l2: "aim_complex_lp_on_plane 2 (\<lambda>x. phi x * ?B x)"
    by (rule slp_test_cauchy_product_l2[OF p_lower p_upper qt_lp phi_test])
  have left_average_l2:
    "aim_complex_lp_on_plane 2 (slp_center_average tau (\<lambda>x. phi x * ?B x))"
    by (rule hf.slp_center_average_l2_l1_l2[OF frequency left_source_l1 left_source_l2])
  show "nn_integral lborel (slp_mixed_center_finite_weighted_absolute_fiber_mass
      TYPE('i) TYPE('j) Q cutoff q (slp_cauchy_transform lo q) cutoff qt (\<lambda>_. 1) (slp_center_average tau (\<lambda>x. phi x * (slp_cauchy_transform ro qt) x))) < top_class.top"
    by (rule slp_mixed_center_finite_weighted_absolute_mass_left_cauchy_unit_finite[OF
        R_nonnegative M_nonnegative p_lower p_upper Y_measurable Y_bounded
        cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound
        Q_support cutoff_support q_support qt_support left_average_l2])
  have right_source_l1: "integrable lborel (\<lambda>x. phi x * ?A x)"
    by (rule slp_test_cauchy_product_integrable[OF p_lower p_upper q_lp phi_test])
  have right_source_l2: "aim_complex_lp_on_plane 2 (\<lambda>x. phi x * ?A x)"
    by (rule slp_test_cauchy_product_l2[OF p_lower p_upper q_lp phi_test])
  have right_average_l2:
    "aim_complex_lp_on_plane 2 (slp_center_average tau (\<lambda>x. phi x * ?A x))"
    by (rule hf.slp_center_average_l2_l1_l2[OF frequency right_source_l1 right_source_l2])
  show "nn_integral lborel (slp_mixed_center_finite_weighted_absolute_fiber_mass
      TYPE('i) TYPE('j) Q cutoff q (\<lambda>_. 1) cutoff qt (slp_cauchy_transform ro qt) (slp_center_average tau (\<lambda>x. phi x * (slp_cauchy_transform lo q) x))) < top_class.top"
    by (rule slp_mixed_center_finite_weighted_absolute_mass_unit_right_cauchy_finite[OF
        R_nonnegative M_nonnegative p_lower p_upper Y_measurable Y_bounded
        cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound
        Q_support cutoff_support q_support qt_support right_average_l2])
  have product_bound:
    "norm (slp_center_average tau (\<lambda>z. phi z * (?A z * ?B z)) x) \<le>
      norm (of_real (tau / pi)::complex) *
        integral\<^sup>L lborel (\<lambda>z. norm (phi z * (?A z * ?B z)))" for x
    by (rule slp_center_average_fixed_tau_bound)
  show "nn_integral lborel (slp_mixed_center_finite_weighted_absolute_fiber_mass
      TYPE('i) TYPE('j) Q cutoff q (\<lambda>_. 1) cutoff qt (\<lambda>_. 1) (slp_center_average tau (\<lambda>x. phi x * ((slp_cauchy_transform lo q) x * (slp_cauchy_transform ro qt) x)))) < top_class.top"
    by (rule slp_mixed_unit_terminal_bounded_mass[OF p_lower p_upper Y_bounded
        Y_measurable cutoff_test q_lp qt_lp Q_lp cutoff_q cutoff_qt Q_in product_bound])
qed

end

theorem slp_mixed_finite_bracket_joint_integrable_from_masses:
  fixes left_type :: "'i::finite itself" and right_type :: "'j::finite itself"
    and tau :: real
    and Q left_cutoff q A right_cutoff qt B phi :: slp_scalar_field
  assumes Q_measurable: "Q \<in> borel_measurable lborel"
    and left_cutoff_measurable: "left_cutoff \<in> borel_measurable lborel"
    and q_measurable: "q \<in> borel_measurable lborel"
    and A_measurable: "A \<in> borel_measurable lborel"
    and right_cutoff_measurable: "right_cutoff \<in> borel_measurable lborel"
    and qt_measurable: "qt \<in> borel_measurable lborel"
    and B_measurable: "B \<in> borel_measurable lborel"
    and phi_l1: "integrable lborel phi"
    and left_source_l1: "integrable lborel (\<lambda>x. phi x * B x)"
    and right_source_l1: "integrable lborel (\<lambda>x. phi x * A x)"
    and product_source_l1: "integrable lborel (\<lambda>x. phi x * (A x * B x))"
    and mass1: "nn_integral lborel (slp_mixed_center_finite_weighted_absolute_fiber_mass
      TYPE('i) TYPE('j) Q left_cutoff q A right_cutoff qt B (slp_center_average tau phi)) < top_class.top"
    and mass2: "nn_integral lborel (slp_mixed_center_finite_weighted_absolute_fiber_mass
      TYPE('i) TYPE('j) Q left_cutoff q A right_cutoff qt (\<lambda>_. 1) (slp_center_average tau (\<lambda>x. phi x * B x))) < top_class.top"
    and mass3: "nn_integral lborel (slp_mixed_center_finite_weighted_absolute_fiber_mass
      TYPE('i) TYPE('j) Q left_cutoff q (\<lambda>_. 1) right_cutoff qt B (slp_center_average tau (\<lambda>x. phi x * A x))) < top_class.top"
    and mass4: "nn_integral lborel (slp_mixed_center_finite_weighted_absolute_fiber_mass
      TYPE('i) TYPE('j) Q left_cutoff q (\<lambda>_. 1) right_cutoff qt (\<lambda>_. 1) (slp_center_average tau (\<lambda>x. phi x * (A x * B x)))) < top_class.top"
  shows "integrable lborel (\<lambda>z :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_complex_amplitude Q left_cutoff q right_cutoff qt
        (fst z) (snd z) * slp_mixed_center_average_bracket tau phi A B (fst z)
        (snd (fst (snd (snd z))))
        (slp_mixed_center_finite_right_terminal (fst z) (snd z)))"
    and "integrable lborel (\<lambda>z :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_bracket_integrand tau Q left_cutoff q A
        right_cutoff qt B phi (fst z) (snd z))"
proof -
  have average1_measurable: "(slp_center_average tau phi) \<in> borel_measurable lborel"
    by (rule slp_center_average_measurable[OF phi_l1])
  have average2_measurable: "(slp_center_average tau (\<lambda>x. phi x * B x)) \<in> borel_measurable lborel"
    by (rule slp_center_average_measurable[OF left_source_l1])
  have average3_measurable: "(slp_center_average tau (\<lambda>x. phi x * A x)) \<in> borel_measurable lborel"
    by (rule slp_center_average_measurable[OF right_source_l1])
  have average4_measurable: "(slp_center_average tau (\<lambda>x. phi x * (A x * B x))) \<in> borel_measurable lborel"
    by (rule slp_center_average_measurable[OF product_source_l1])
  let ?phased = "\<lambda>(sigma::real) (z :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates).
    slp_parameterized_real_phase_integrand sigma slp_mixed_center_finite_residual
      (slp_mixed_center_finite_complex_amplitude Q left_cutoff q right_cutoff qt)
      (fst z) (snd z) * slp_mixed_center_average_bracket tau phi A B (fst z)
        (snd (fst (snd (snd z))))
        (slp_mixed_center_finite_right_terminal (fst z) (snd z))"
  have unit_measurable: "(\<lambda>_::slp_point. 1::complex) \<in> borel_measurable lborel"
    by measurable
  have phase_integrable: "integrable lborel (?phased sigma)" for sigma
  proof -
    let ?F1 = "(\<lambda>z :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
    slp_mixed_center_finite_weighted_oscillatory_integrand sigma
      Q left_cutoff q A right_cutoff qt B (slp_center_average tau phi) (fst z) (snd z))"
    let ?F2 = "(\<lambda>z :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
    slp_mixed_center_finite_weighted_oscillatory_integrand sigma
      Q left_cutoff q A right_cutoff qt (\<lambda>_. 1) (slp_center_average tau (\<lambda>x. phi x * B x)) (fst z) (snd z))"
    let ?F3 = "(\<lambda>z :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
    slp_mixed_center_finite_weighted_oscillatory_integrand sigma
      Q left_cutoff q (\<lambda>_. 1) right_cutoff qt B (slp_center_average tau (\<lambda>x. phi x * A x)) (fst z) (snd z))"
    let ?F4 = "(\<lambda>z :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
    slp_mixed_center_finite_weighted_oscillatory_integrand sigma
      Q left_cutoff q (\<lambda>_. 1) right_cutoff qt (\<lambda>_. 1) (slp_center_average tau (\<lambda>x. phi x * (A x * B x))) (fst z) (snd z))"
    have term1: "integrable lborel ?F1"
      by (rule slp_mixed_weighted_joint_integrable_of_global_mass(2)[OF
          Q_measurable left_cutoff_measurable q_measurable A_measurable
          right_cutoff_measurable qt_measurable B_measurable
          average1_measurable mass1])
    have term2: "integrable lborel ?F2"
      by (rule slp_mixed_weighted_joint_integrable_of_global_mass(2)[OF
          Q_measurable left_cutoff_measurable q_measurable A_measurable
          right_cutoff_measurable qt_measurable unit_measurable
          average2_measurable mass2])
    have term3: "integrable lborel ?F3"
      by (rule slp_mixed_weighted_joint_integrable_of_global_mass(2)[OF
          Q_measurable left_cutoff_measurable q_measurable unit_measurable
          right_cutoff_measurable qt_measurable B_measurable
          average3_measurable mass3])
    have term4: "integrable lborel ?F4"
      by (rule slp_mixed_weighted_joint_integrable_of_global_mass(2)[OF
          Q_measurable left_cutoff_measurable q_measurable unit_measurable
          right_cutoff_measurable qt_measurable unit_measurable
          average4_measurable mass4])
    have first_difference: "integrable lborel (\<lambda>z. ?F1 z - ?F2 z)"
      by (rule Bochner_Integration.integrable_diff[OF term1 term2])
    have second_difference: "integrable lborel (\<lambda>z. ?F1 z - ?F2 z - ?F3 z)"
      by (rule Bochner_Integration.integrable_diff[OF first_difference term3])
    have sum_integrable: "integrable lborel (\<lambda>z. ?F1 z - ?F2 z - ?F3 z + ?F4 z)"
      by (rule Bochner_Integration.integrable_add[OF second_difference term4])
    have expansion: "?phased sigma z = ?F1 z - ?F2 z - ?F3 z + ?F4 z" for z
      by (simp add: slp_mixed_weighted_integrand_terminal_factor
          slp_mixed_center_average_bracket_def algebra_simps)
    show ?thesis using sum_integrable by (simp only: expansion)
  qed
  show "integrable lborel (\<lambda>z :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_complex_amplitude Q left_cutoff q right_cutoff qt
        (fst z) (snd z) * slp_mixed_center_average_bracket tau phi A B (fst z)
        (snd (fst (snd (snd z))))
        (slp_mixed_center_finite_right_terminal (fst z) (snd z)))"
    using phase_integrable[of 0]
    unfolding slp_parameterized_real_phase_integrand_def by simp
  show "integrable lborel (\<lambda>z :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_bracket_integrand tau Q left_cutoff q A
        right_cutoff qt B phi (fst z) (snd z))"
    using phase_integrable[of tau]
    by (simp only: slp_mixed_center_finite_bracket_integrand_def)
qed

context aim_planar_riesz_hls_cauchy
begin

theorem slp_mixed_cauchy_bracket_joint_integrable:
  fixes left_type :: "'i::finite itself" and right_type :: "'j::finite itself"
    and p tau :: real and Y :: "slp_point set"
    and cutoff q qt Q phi :: slp_scalar_field
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
    and plancherel: "hormander_euclidean_l2_fourier_plancherel_claim"
    and frequency: "0 < tau"
  shows "integrable lborel (\<lambda>z :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_complex_amplitude Q cutoff q cutoff qt
        (fst z) (snd z) * slp_mixed_center_average_bracket tau phi (slp_cauchy_transform lo q) (slp_cauchy_transform ro qt) (fst z)
        (snd (fst (snd (snd z))))
        (slp_mixed_center_finite_right_terminal (fst z) (snd z)))"
    and "integrable lborel (\<lambda>z :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_bracket_integrand tau Q cutoff q (slp_cauchy_transform lo q)
        cutoff qt (slp_cauchy_transform ro qt) phi (fst z) (snd z))"
    and "integrable lborel (slp_mixed_center_finite_bracket_kernel TYPE('i) TYPE('j) tau
      Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) phi)"
    and "integral\<^sup>L lborel (slp_mixed_center_finite_bracket_kernel TYPE('i) TYPE('j) tau
      Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) phi) = integral\<^sup>L lborel (\<lambda>z :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_bracket_integrand tau Q cutoff q (slp_cauchy_transform lo q)
        cutoff qt (slp_cauchy_transform ro qt) phi (fst z) (snd z))"
    and "integral\<^sup>L lborel (slp_mixed_center_finite_bracket_kernel TYPE('i) TYPE('j) tau
      Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) phi) = (\<integral>(coordinates::('i, 'j) slp_mixed_center_finite_coordinates).
      \<integral>center. slp_mixed_center_finite_bracket_integrand tau Q cutoff q (slp_cauchy_transform lo q)
      cutoff qt (slp_cauchy_transform ro qt) phi center coordinates \<partial>lborel \<partial>lborel)"
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
  have phi_l1: "integrable lborel phi"
    by (rule slp_test_function_integrable_bounded(1)[OF phi_test])
  have left_source_l1: "integrable lborel (\<lambda>x. phi x * ?B x)"
    by (rule slp_test_cauchy_product_integrable[OF p_lower p_upper qt_lp phi_test])
  have right_source_l1: "integrable lborel (\<lambda>x. phi x * ?A x)"
    by (rule slp_test_cauchy_product_integrable[OF p_lower p_upper q_lp phi_test])
  have product_source_l1: "integrable lborel (\<lambda>x. phi x * (?A x * ?B x))"
    by (rule slp_test_two_cauchy_product_integrable[OF p_lower p_upper q_lp qt_lp phi_test])
  note masses = slp_mixed_cauchy_average_masses[OF p_lower p_upper Y_bounded
    Y_measurable cutoff_test q_lp qt_lp Q_lp cutoff_q cutoff_qt Q_in phi_test
    plancherel frequency, where lo=lo and ro=ro and 'i='i and 'j='j]
  have mass1: "nn_integral lborel (slp_mixed_center_finite_weighted_absolute_fiber_mass
      TYPE('i) TYPE('j) Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) (slp_center_average tau phi)) < top_class.top" using masses(1) by blast
  have mass2: "nn_integral lborel (slp_mixed_center_finite_weighted_absolute_fiber_mass
      TYPE('i) TYPE('j) Q cutoff q (slp_cauchy_transform lo q) cutoff qt (\<lambda>_. 1) (slp_center_average tau (\<lambda>x. phi x * (slp_cauchy_transform ro qt) x))) < top_class.top" using masses(2) by blast
  have mass3: "nn_integral lborel (slp_mixed_center_finite_weighted_absolute_fiber_mass
      TYPE('i) TYPE('j) Q cutoff q (\<lambda>_. 1) cutoff qt (slp_cauchy_transform ro qt) (slp_center_average tau (\<lambda>x. phi x * (slp_cauchy_transform lo q) x))) < top_class.top" using masses(3) by blast
  have mass4: "nn_integral lborel (slp_mixed_center_finite_weighted_absolute_fiber_mass
      TYPE('i) TYPE('j) Q cutoff q (\<lambda>_. 1) cutoff qt (\<lambda>_. 1) (slp_center_average tau (\<lambda>x. phi x * ((slp_cauchy_transform lo q) x * (slp_cauchy_transform ro qt) x)))) < top_class.top" using masses(4) by blast
  note joints = slp_mixed_finite_bracket_joint_integrable_from_masses[OF
    Q_measurable cutoff_measurable q_measurable A_measurable
    cutoff_measurable qt_measurable B_measurable phi_l1 left_source_l1
    right_source_l1 product_source_l1 mass1 mass2 mass3 mass4]
  show "integrable lborel (\<lambda>z :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_complex_amplitude Q cutoff q cutoff qt
        (fst z) (snd z) * slp_mixed_center_average_bracket tau phi (slp_cauchy_transform lo q) (slp_cauchy_transform ro qt) (fst z)
        (snd (fst (snd (snd z))))
        (slp_mixed_center_finite_right_terminal (fst z) (snd z)))" by (rule joints(1))
  have joint_integrable: "integrable lborel (\<lambda>z :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_bracket_integrand tau Q cutoff q (slp_cauchy_transform lo q)
        cutoff qt (slp_cauchy_transform ro qt) phi (fst z) (snd z))" by (rule joints(2))
  show "integrable lborel (\<lambda>z :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_bracket_integrand tau Q cutoff q (slp_cauchy_transform lo q)
        cutoff qt (slp_cauchy_transform ro qt) phi (fst z) (snd z))" by (rule joint_integrable)
  let ?F = "slp_mixed_center_finite_bracket_integrand tau Q cutoff q (slp_cauchy_transform lo q)
      cutoff qt (slp_cauchy_transform ro qt) phi ::
    slp_point \<Rightarrow> ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex"
  have product_integrable:
    "integrable (lborel \<Otimes>\<^sub>M lborel) (case_prod ?F)"
    using joint_integrable by (simp only: lborel_prod split_beta')
  have kernel_identity:
    "(slp_mixed_center_finite_bracket_kernel TYPE('i) TYPE('j) tau
      Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) phi) = (\<lambda>center. integral\<^sup>L lborel (?F center))"
    by (rule ext) (simp only: slp_mixed_center_finite_bracket_kernel_def)
  show "integrable lborel (slp_mixed_center_finite_bracket_kernel TYPE('i) TYPE('j) tau
      Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) phi)"
    using lborel_pair.integrable_fst[OF product_integrable]
    by (simp only: kernel_identity)
  show "integral\<^sup>L lborel (slp_mixed_center_finite_bracket_kernel TYPE('i) TYPE('j) tau
      Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) phi) = integral\<^sup>L lborel (\<lambda>z :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_bracket_integrand tau Q cutoff q (slp_cauchy_transform lo q)
        cutoff qt (slp_cauchy_transform ro qt) phi (fst z) (snd z))"
    using lborel_pair.integral_fst[OF product_integrable]
    by (simp only: kernel_identity lborel_prod split_beta')
  have swap: "(\<integral>(coordinates::('i, 'j) slp_mixed_center_finite_coordinates).
      \<integral>center. slp_mixed_center_finite_bracket_integrand tau Q cutoff q (slp_cauchy_transform lo q)
      cutoff qt (slp_cauchy_transform ro qt) phi center coordinates \<partial>lborel \<partial>lborel) = integral\<^sup>L lborel (slp_mixed_center_finite_bracket_kernel TYPE('i) TYPE('j) tau
      Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) phi)"
    using lborel_pair.Fubini_integral[OF product_integrable]
    by (simp only: kernel_identity)
  show "integral\<^sup>L lborel (slp_mixed_center_finite_bracket_kernel TYPE('i) TYPE('j) tau
      Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) phi) = (\<integral>(coordinates::('i, 'j) slp_mixed_center_finite_coordinates).
      \<integral>center. slp_mixed_center_finite_bracket_integrand tau Q cutoff q (slp_cauchy_transform lo q)
      cutoff qt (slp_cauchy_transform ro qt) phi center coordinates \<partial>lborel \<partial>lborel)"
    by (rule sym[OF swap])
qed

end

end
