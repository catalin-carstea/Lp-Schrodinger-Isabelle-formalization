theory Inverse_Schrodinger_Lp_Mixed_Smooth_Cross_Error_Integrability
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Mixed_Product_Error_Integration_Data"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Mixed_Center_Left_Cauchy_Right_Unit_Error_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Mixed_Center_Left_Unit_Right_Cauchy_Error_Decay"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Integration data for the smooth and one-primitive errors\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_mixed_smooth_error_integrable:
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
  shows "AE center in lborel. integrable lborel
      (slp_mixed_center_finite_weighted_oscillatory_integrand tau Q cutoff q
        (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt)
        (\<lambda>x. slp_center_average tau phi x - phi x) center ::
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    and "integrable lborel
      (slp_mixed_center_finite_weighted_oscillatory_kernel TYPE('i) TYPE('j)
        tau Q cutoff q (slp_cauchy_transform lo q) cutoff qt
        (slp_cauchy_transform ro qt) (\<lambda>x. slp_center_average tau phi x - phi x))"
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
  let ?H = "\<lambda>x. slp_center_average tau phi x - phi x"
  have phi_integrable: "integrable lborel phi"
    by (rule slp_test_function_integrable_bounded(1)[OF phi_test])
  have phi_measurable: "phi \<in> borel_measurable lborel" using phi_integrable by measurable
  have phi_bounded: "bounded (range phi)"
    by (rule slp_test_function_integrable_bounded(2)[OF phi_test])
  obtain D where phi_bound: "\<And>x. norm (phi x) \<le> D"
    using phi_bounded unfolding bounded_iff by blast
  have H_measurable: "?H \<in> borel_measurable lborel"
    using slp_center_average_measurable[OF phi_integrable] phi_measurable by measurable
  have H_bound: "norm (?H x) \<le> norm (of_real (tau / pi)::complex) *
      integral\<^sup>L lborel (\<lambda>z. norm (phi z)) + D" for x
  proof -
    have average_bound: "norm (slp_center_average tau phi x) \<le>
        norm (of_real (tau / pi)::complex) *
          integral\<^sup>L lborel (\<lambda>z. norm (phi z))"
      by (rule slp_center_average_fixed_tau_bound)
    show ?thesis
      by (rule order_trans[OF norm_triangle_ineq4])
        (rule add_mono[OF average_bound phi_bound])
  qed
  have mass: "nn_integral lborel
      (slp_mixed_center_finite_weighted_absolute_fiber_mass TYPE('i) TYPE('j)
        Q cutoff q ?A cutoff qt ?B ?H) < top_class.top"
    by (rule slp_mixed_center_finite_weighted_absolute_mass_cauchy_finite[OF
        R_nonnegative M_nonnegative p_lower p_upper Y_measurable Y_bounded
        cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound H_bound
        Q_support cutoff_support q_support qt_support])
  have amplitude: "AE center in lborel. integrable lborel
      (slp_mixed_center_finite_weighted_complex_amplitude Q cutoff q ?A
        cutoff qt ?B ?H center ::
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    by (rule slp_mixed_center_finite_weighted_amplitude_fiber_integrable_from_mass[OF
        Q_measurable cutoff_measurable q_measurable A_measurable
        cutoff_measurable qt_measurable B_measurable H_measurable mass])
  show "AE center in lborel. integrable lborel
      (slp_mixed_center_finite_weighted_oscillatory_integrand tau Q cutoff q ?A
        cutoff qt ?B ?H center ::
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    unfolding slp_mixed_center_finite_weighted_oscillatory_integrand_def
    by (rule slp_mixed_center_finite_weighted_oscillatory_fiber_integrable[OF
        slp_mixed_center_finite_residual_measurable amplitude])
  show "integrable lborel
      (slp_mixed_center_finite_weighted_oscillatory_kernel TYPE('i) TYPE('j)
        tau Q cutoff q ?A cutoff qt ?B ?H)"
    by (rule slp_mixed_weighted_kernel_integrable_of_global_mass[OF
        Q_measurable cutoff_measurable q_measurable A_measurable
        cutoff_measurable qt_measurable B_measurable H_measurable mass])
qed

theorem slp_mixed_cross_errors_integrable:
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
    and fourier_plancherel: "hormander_euclidean_l2_fourier_plancherel_claim"
    and tau_positive: "0 < tau"
    shows "AE center in lborel. integrable lborel
      (slp_mixed_center_finite_weighted_oscillatory_integrand tau Q cutoff q
        (slp_cauchy_transform lo q) cutoff qt (\<lambda>_. 1)
        (\<lambda>c. slp_center_average tau (\<lambda>x. phi x * slp_cauchy_transform ro qt x) c -
          phi c * slp_cauchy_transform ro qt c) center ::
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    and "integrable lborel
      (slp_mixed_center_finite_weighted_oscillatory_kernel TYPE('i) TYPE('j)
        tau Q cutoff q (slp_cauchy_transform lo q) cutoff qt (\<lambda>_. 1)
        (\<lambda>c. slp_center_average tau (\<lambda>x. phi x * slp_cauchy_transform ro qt x) c -
          phi c * slp_cauchy_transform ro qt c))"
    and "AE center in lborel. integrable lborel
      (slp_mixed_center_finite_weighted_oscillatory_integrand tau Q cutoff q
        (\<lambda>_. 1) cutoff qt (slp_cauchy_transform ro qt)
        (\<lambda>c. slp_center_average tau (\<lambda>x. phi x * slp_cauchy_transform lo q x) c -
          phi c * slp_cauchy_transform lo q c) center ::
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    and "integrable lborel
      (slp_mixed_center_finite_weighted_oscillatory_kernel TYPE('i) TYPE('j)
        tau Q cutoff q (\<lambda>_. 1) cutoff qt (slp_cauchy_transform ro qt)
        (\<lambda>c. slp_center_average tau (\<lambda>x. phi x * slp_cauchy_transform lo q x) c -
          phi c * slp_cauchy_transform lo q c))"
proof -
  interpret hf: hormander_euclidean_l2_fourier_plancherel
    by standard (rule fourier_plancherel)
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
  let ?unit = "\<lambda>_::slp_point. (1::complex)"
  let ?left_source = "\<lambda>x. phi x * ?B x"
  let ?right_source = "\<lambda>x. phi x * ?A x"
  let ?left_error = "\<lambda>c. slp_center_average tau ?left_source c - ?left_source c"
  let ?right_error = "\<lambda>c. slp_center_average tau ?right_source c - ?right_source c"
  have left_source_integrable: "integrable lborel ?left_source"
    by (rule slp_test_cauchy_product_integrable[OF p_lower p_upper qt_lp phi_test])
  have right_source_integrable: "integrable lborel ?right_source"
    by (rule slp_test_cauchy_product_integrable[OF p_lower p_upper q_lp phi_test])
  have left_source_l2: "aim_complex_lp_on_plane 2 ?left_source"
    by (rule slp_test_cauchy_product_l2[OF p_lower p_upper qt_lp phi_test])
  have right_source_l2: "aim_complex_lp_on_plane 2 ?right_source"
    by (rule slp_test_cauchy_product_l2[OF p_lower p_upper q_lp phi_test])
  have left_error_l2: "aim_complex_lp_on_plane 2 ?left_error"
    by (rule hf.slp_center_average_error_l2_l1_l2[OF
        tau_positive left_source_integrable left_source_l2])
  have right_error_l2: "aim_complex_lp_on_plane 2 ?right_error"
    by (rule hf.slp_center_average_error_l2_l1_l2[OF
        tau_positive right_source_integrable right_source_l2])
  have left_error_measurable: "?left_error \<in> borel_measurable lborel"
    using left_error_l2 unfolding aim_complex_lp_on_plane_def by blast
  have right_error_measurable: "?right_error \<in> borel_measurable lborel"
    using right_error_l2 unfolding aim_complex_lp_on_plane_def by blast
  have unit_measurable: "?unit \<in> borel_measurable lborel" by measurable
  let ?mass = "\<lambda>T U H. slp_mixed_center_finite_weighted_absolute_fiber_mass
    TYPE('i) TYPE('j) Q cutoff q T cutoff qt U H"
  have left_mass: "nn_integral lborel (?mass ?A ?unit ?left_error) < top_class.top"
    by (rule slp_mixed_center_finite_weighted_absolute_mass_left_cauchy_unit_finite[OF
        R_nonnegative M_nonnegative p_lower p_upper Y_measurable Y_bounded
        cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound
        Q_support cutoff_support q_support qt_support left_error_l2])
  have right_mass: "nn_integral lborel (?mass ?unit ?B ?right_error) < top_class.top"
    by (rule slp_mixed_center_finite_weighted_absolute_mass_unit_right_cauchy_finite[OF
        R_nonnegative M_nonnegative p_lower p_upper Y_measurable Y_bounded
        cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound
        Q_support cutoff_support q_support qt_support right_error_l2])
  let ?W = "\<lambda>T U H. slp_mixed_center_finite_weighted_oscillatory_integrand tau
    Q cutoff q T cutoff qt U H ::
      slp_point \<Rightarrow> ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex"
  let ?K = "\<lambda>T U H. slp_mixed_center_finite_weighted_oscillatory_kernel
    TYPE('i) TYPE('j) tau Q cutoff q T cutoff qt U H"
  have data: "(AE center in lborel. integrable lborel (?W T U H center)) \<and>
      integrable lborel (?K T U H)"
    if T: "T \<in> borel_measurable lborel"
      and U: "U \<in> borel_measurable lborel"
      and H: "H \<in> borel_measurable lborel"
      and mass: "nn_integral lborel
        (slp_mixed_center_finite_weighted_absolute_fiber_mass TYPE('i) TYPE('j)
          Q cutoff q T cutoff qt U H) < top_class.top"
    for T U H :: slp_scalar_field
  proof
    have amplitude: "AE center in lborel. integrable lborel
        (slp_mixed_center_finite_weighted_complex_amplitude
          Q cutoff q T cutoff qt U H center ::
          ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
      by (rule slp_mixed_center_finite_weighted_amplitude_fiber_integrable_from_mass[OF
          Q_measurable cutoff_measurable q_measurable T
          cutoff_measurable qt_measurable U H mass])
    show "AE center in lborel. integrable lborel (?W T U H center)"
      unfolding slp_mixed_center_finite_weighted_oscillatory_integrand_def
      by (rule slp_mixed_center_finite_weighted_oscillatory_fiber_integrable[OF
          slp_mixed_center_finite_residual_measurable amplitude])
    show "integrable lborel (?K T U H)"
      by (rule slp_mixed_weighted_kernel_integrable_of_global_mass[OF
          Q_measurable cutoff_measurable q_measurable T
          cutoff_measurable qt_measurable U H mass])
  qed
  note left_data = data[OF A_measurable unit_measurable left_error_measurable left_mass]
  note right_data = data[OF unit_measurable B_measurable right_error_measurable right_mass]
  show "AE center in lborel. integrable lborel (?W ?A ?unit ?left_error center)"
    by (rule left_data[THEN conjunct1])
  show "integrable lborel (?K ?A ?unit ?left_error)"
    by (rule left_data[THEN conjunct2])
  show "AE center in lborel. integrable lborel (?W ?unit ?B ?right_error center)"
    by (rule right_data[THEN conjunct1])
  show "integrable lborel (?K ?unit ?B ?right_error)"
    by (rule right_data[THEN conjunct2])
qed

end

end
