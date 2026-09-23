theory Inverse_Schrodinger_Lp_Mixed_Principal_Difference_Integrability
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Mixed_Bracket_Integration"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Finite_Kernel_L2_Dominator"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Integrability of the principal primitive differences\<close>

theorem slp_mixed_primitive_difference_integrable_from_masses:
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
    and phi_measurable: "phi \<in> borel_measurable lborel"
    and tt_mass: "nn_integral lborel
      (slp_mixed_center_finite_weighted_absolute_fiber_mass TYPE('i) TYPE('j)
        Q left_cutoff q A right_cutoff qt B phi) < top_class.top"
    and lc_mass: "nn_integral lborel
      (slp_mixed_center_finite_weighted_absolute_fiber_mass TYPE('i) TYPE('j)
        Q left_cutoff q A right_cutoff qt (\<lambda>_. 1)
          (\<lambda>x. -(phi x * B x))) < top_class.top"
    and rc_mass: "nn_integral lborel
      (slp_mixed_center_finite_weighted_absolute_fiber_mass TYPE('i) TYPE('j)
        Q left_cutoff q (\<lambda>_. 1) right_cutoff qt B
          (\<lambda>x. -(phi x * A x))) < top_class.top"
    and uu_mass: "nn_integral lborel
      (slp_mixed_center_finite_weighted_absolute_fiber_mass TYPE('i) TYPE('j)
        Q left_cutoff q (\<lambda>_. 1) right_cutoff qt (\<lambda>_. 1)
          (\<lambda>x. phi x * (A x * B x))) < top_class.top"
  shows "AE center in lborel. integrable lborel
      (slp_mixed_center_finite_weighted_oscillatory_integrand tau
        Q left_cutoff q (\<lambda>x. A x - A center) right_cutoff qt
        (\<lambda>x. B x - B center) phi center ::
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    and "integrable lborel
      (slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_kernel
        TYPE('i) TYPE('j) tau Q left_cutoff q A right_cutoff qt B phi)"
proof -
  let ?W = "\<lambda>T U H. slp_mixed_center_finite_weighted_oscillatory_integrand tau
    Q left_cutoff q T right_cutoff qt U H ::
      slp_point \<Rightarrow> ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex"
  let ?K = "\<lambda>T U H. slp_mixed_center_finite_weighted_oscillatory_kernel
    TYPE('i) TYPE('j) tau Q left_cutoff q T right_cutoff qt U H"
  let ?unit = "\<lambda>_::slp_point. (1::complex)"
  let ?lc = "\<lambda>x. -(phi x * B x)"
  let ?rc = "\<lambda>x. -(phi x * A x)"
  let ?uu = "\<lambda>x. phi x * (A x * B x)"
  let ?principal = "slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_kernel
    TYPE('i) TYPE('j) tau Q left_cutoff q A right_cutoff qt B phi"
  have data: "(AE center in lborel. integrable lborel (?W T U H center)) \<and>
      integrable lborel (?K T U H)"
    if T: "T \<in> borel_measurable lborel"
      and U: "U \<in> borel_measurable lborel"
      and H: "H \<in> borel_measurable lborel"
      and mass: "nn_integral lborel
        (slp_mixed_center_finite_weighted_absolute_fiber_mass TYPE('i) TYPE('j)
          Q left_cutoff q T right_cutoff qt U H) < top_class.top"
    for T U H :: slp_scalar_field
  proof
    have amplitude: "AE center in lborel. integrable lborel
        (slp_mixed_center_finite_weighted_complex_amplitude
          Q left_cutoff q T right_cutoff qt U H center ::
          ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
      by (rule slp_mixed_center_finite_weighted_amplitude_fiber_integrable_from_mass[OF
          Q_measurable left_cutoff_measurable q_measurable T
          right_cutoff_measurable qt_measurable U H mass])
    show "AE center in lborel. integrable lborel (?W T U H center)"
      unfolding slp_mixed_center_finite_weighted_oscillatory_integrand_def
      by (rule slp_mixed_center_finite_weighted_oscillatory_fiber_integrable[OF
          slp_mixed_center_finite_residual_measurable amplitude])
    show "integrable lborel (?K T U H)"
      by (rule slp_mixed_weighted_kernel_integrable_of_global_mass[OF
          Q_measurable left_cutoff_measurable q_measurable T
          right_cutoff_measurable qt_measurable U H mass])
  qed
  have unit_measurable: "?unit \<in> borel_measurable lborel" by measurable
  have lc_measurable: "?lc \<in> borel_measurable lborel"
    using phi_measurable B_measurable by measurable
  have rc_measurable: "?rc \<in> borel_measurable lborel"
    using phi_measurable A_measurable by measurable
  have uu_measurable: "?uu \<in> borel_measurable lborel"
    using phi_measurable A_measurable B_measurable by measurable
  note tt = data[OF A_measurable B_measurable phi_measurable tt_mass]
  note lc = data[OF A_measurable unit_measurable lc_measurable lc_mass]
  note rc = data[OF unit_measurable B_measurable rc_measurable rc_mass]
  note uu = data[OF unit_measurable unit_measurable uu_measurable uu_mass]
  have fiber_sum: "?W (\<lambda>x. A x - A center) (\<lambda>x. B x - B center) phi center =
      (\<lambda>z. ?W A B phi center z + ?W A ?unit ?lc center z +
        ?W ?unit B ?rc center z + ?W ?unit ?unit ?uu center z)" for center
    by (rule ext, rule
        slp_mixed_center_finite_weighted_oscillatory_integrand_cauchy_center_diff_expansion)
  show "AE center in lborel. integrable lborel
      (?W (\<lambda>x. A x - A center) (\<lambda>x. B x - B center) phi center)"
    using tt[THEN conjunct1] lc[THEN conjunct1] rc[THEN conjunct1] uu[THEN conjunct1]
  proof eventually_elim
    fix center
    assume tt_fiber: "integrable lborel (?W A B phi center)"
      and lc_fiber: "integrable lborel (?W A ?unit ?lc center)"
      and rc_fiber: "integrable lborel (?W ?unit B ?rc center)"
      and uu_fiber: "integrable lborel (?W ?unit ?unit ?uu center)"
    show "integrable lborel
        (?W (\<lambda>x. A x - A center) (\<lambda>x. B x - B center) phi center)"
      unfolding fiber_sum
      by (rule Bochner_Integration.integrable_add,
          rule Bochner_Integration.integrable_add,
          rule Bochner_Integration.integrable_add[OF tt_fiber lc_fiber],
          rule rc_fiber, rule uu_fiber)
  qed
  have kernel_sum: "AE center in lborel. ?principal center =
      ?K A B phi center + ?K A ?unit ?lc center +
        ?K ?unit B ?rc center + ?K ?unit ?unit ?uu center"
    using tt[THEN conjunct1] lc[THEN conjunct1] rc[THEN conjunct1] uu[THEN conjunct1]
  proof eventually_elim
    fix center
    assume tt_fiber: "integrable lborel (?W A B phi center)"
      and lc_fiber: "integrable lborel (?W A ?unit ?lc center)"
      and rc_fiber: "integrable lborel (?W ?unit B ?rc center)"
      and uu_fiber: "integrable lborel (?W ?unit ?unit ?uu center)"
    show "?principal center = ?K A B phi center + ?K A ?unit ?lc center +
        ?K ?unit B ?rc center + ?K ?unit ?unit ?uu center"
      by (rule
          slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_kernel_expansion[OF
            tt_fiber lc_fiber rc_fiber uu_fiber])
  qed
  have sum_integrable: "integrable lborel (\<lambda>center.
      ?K A B phi center + ?K A ?unit ?lc center +
        ?K ?unit B ?rc center + ?K ?unit ?unit ?uu center)"
    by (rule Bochner_Integration.integrable_add,
        rule Bochner_Integration.integrable_add,
        rule Bochner_Integration.integrable_add[OF tt[THEN conjunct2] lc[THEN conjunct2]],
        rule rc[THEN conjunct2], rule uu[THEN conjunct2])
  have principal_measurable: "?principal \<in> borel_measurable lborel"
    by (rule
        slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_kernel_measurable[OF
          Q_measurable left_cutoff_measurable q_measurable A_measurable
          right_cutoff_measurable qt_measurable B_measurable phi_measurable])
  have reverse: "AE center in lborel.
      ?K A B phi center + ?K A ?unit ?lc center +
        ?K ?unit B ?rc center + ?K ?unit ?unit ?uu center = ?principal center"
    using kernel_sum by eventually_elim simp
  show "integrable lborel ?principal"
    by (rule integrable_cong_AE_imp[OF sum_integrable principal_measurable reverse])
qed

context aim_planar_riesz_hls_cauchy
begin

theorem slp_mixed_cauchy_difference_integrable:
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
        (\<lambda>x. slp_cauchy_transform lo q x - slp_cauchy_transform lo q center)
        cutoff qt
        (\<lambda>x. slp_cauchy_transform ro qt x - slp_cauchy_transform ro qt center)
        phi center :: ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    and "integrable lborel
      (slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_kernel
        TYPE('i) TYPE('j) tau Q cutoff q (slp_cauchy_transform lo q)
        cutoff qt (slp_cauchy_transform ro qt) phi)"
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
  have phi_integrable: "integrable lborel phi"
    by (rule slp_test_function_integrable_bounded(1)[OF phi_test])
  have phi_measurable: "phi \<in> borel_measurable lborel"
    using phi_integrable unfolding integrable_iff_bounded by blast
  have phi_bounded: "bounded (range phi)"
    by (rule slp_test_function_integrable_bounded(2)[OF phi_test])
  obtain D where phi_bound: "\<And>x. norm (phi x) \<le> D"
    using phi_bounded unfolding bounded_iff by blast
  let ?mass = "\<lambda>T U H. slp_mixed_center_finite_weighted_absolute_fiber_mass
    TYPE('i) TYPE('j) Q cutoff q T cutoff qt U H"
  have tt: "nn_integral lborel (?mass ?A ?B phi) < top_class.top"
    by (rule slp_mixed_center_finite_weighted_absolute_mass_cauchy_finite[OF
        R_nonnegative M_nonnegative p_lower p_upper Y_measurable Y_bounded
        cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound phi_bound
        Q_support cutoff_support q_support qt_support])
  have lc: "nn_integral lborel (?mass ?A (\<lambda>_. 1)
      (\<lambda>x. -(phi x * ?B x))) < top_class.top"
    by (rule slp_mixed_center_finite_weighted_absolute_mass_left_cross_finite[OF
        R_nonnegative M_nonnegative p_lower p_upper Y_measurable Y_bounded
        phi_test cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound
        Q_support cutoff_support q_support qt_support])
  have rc: "nn_integral lborel (?mass (\<lambda>_. 1) ?B
      (\<lambda>x. -(phi x * ?A x))) < top_class.top"
    by (rule slp_mixed_center_finite_weighted_absolute_mass_right_cross_finite[OF
        R_nonnegative M_nonnegative p_lower p_upper Y_measurable Y_bounded
        phi_test cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound
        Q_support cutoff_support q_support qt_support])
  have uu: "nn_integral lborel (?mass (\<lambda>_. 1) (\<lambda>_. 1)
      (\<lambda>x. phi x * (?A x * ?B x))) < top_class.top"
    by (rule slp_mixed_center_finite_weighted_absolute_mass_unit_unit_two_cauchy_finite[OF
        R_nonnegative M_nonnegative p_lower p_upper Y_measurable Y_bounded
        phi_test cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound
        Q_support cutoff_support q_support qt_support])
  note result = slp_mixed_primitive_difference_integrable_from_masses[OF
    Q_measurable cutoff_measurable q_measurable A_measurable
    cutoff_measurable qt_measurable B_measurable phi_measurable tt lc rc uu]
  show "AE center in lborel. integrable lborel
      (slp_mixed_center_finite_weighted_oscillatory_integrand tau Q cutoff q
        (\<lambda>x. ?A x - ?A center) cutoff qt (\<lambda>x. ?B x - ?B center)
        phi center :: ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    by (rule result(1))
  show "integrable lborel
      (slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_kernel
        TYPE('i) TYPE('j) tau Q cutoff q ?A cutoff qt ?B phi)"
    by (rule result(2))
qed

end

end
