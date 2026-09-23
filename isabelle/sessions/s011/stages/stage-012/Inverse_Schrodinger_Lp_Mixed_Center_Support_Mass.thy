theory Inverse_Schrodinger_Lp_Mixed_Center_Support_Mass
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Mixed_Born_Functional"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Bounded propagation and unit-center weighted mass\<close>

theorem slp_mixed_center_density_outside:
  fixes R B :: real and center :: slp_point
    and cutoff q qt Q :: slp_scalar_field
    and A Bterm :: "slp_point \<Rightarrow> ennreal"
    and n m :: nat
  assumes radius_nonnegative: "0 \<le> R"
    and root_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and outside: "B + (real (Suc n) + real (Suc m)) * R < norm center"
  shows "slp_mixed_center_density R cutoff q qt A Bterm n m Q center = 0"
proof -
  have zero: "ennreal (norm (Q root)) *
      slp_left_positive_output_density R cutoff q A n root left_output *
      slp_right_positive_output_density R cutoff qt Bterm m root
        (center + root - left_output) = 0" for root left_output
  proof (cases "Q root = 0")
    case True
    then show ?thesis by simp
  next
    case False
    have root_bound: "norm root \<le> B" by (rule root_support[OF False])
    show ?thesis
    proof (cases "slp_left_positive_output_density R cutoff q A n root left_output = 0")
      case True
      then show ?thesis by simp
    next
      case False
      have left_bound: "norm (left_output - root) \<le> real (Suc n) * R"
      proof (rule ccontr)
        assume "\<not> norm (left_output - root) \<le> real (Suc n) * R"
        then have left_outside: "real (Suc n) * R < norm (left_output - root)"
          by simp
        have "slp_positive_output_density R cutoff q A n root left_output = 0"
          by (rule slp_positive_output_density_outside[OF
              radius_nonnegative left_outside])
        then show False using False
          by (simp only: slp_left_positive_output_density_def)
      qed
      have triangle:
          "norm center \<le> norm root + norm (left_output - root) +
            norm (center - left_output)"
      proof -
        have "norm center = norm (root + (left_output - root) + (center - left_output))"
          by (simp add: algebra_simps)
        also have "... \<le> norm (root + (left_output - root)) +
            norm (center - left_output)"
          by (rule norm_triangle_ineq)
        also have "... \<le> norm root + norm (left_output - root) +
            norm (center - left_output)"
          by (rule add_right_mono[OF norm_triangle_ineq])
        finally show ?thesis .
      qed
      have right_outside:
          "real (Suc m) * R < norm ((center + root - left_output) - root)"
        using outside triangle root_bound left_bound
        by (simp add: algebra_simps; linarith)
      have right_zero:
          "slp_right_positive_output_density R cutoff qt Bterm m root
            (center + root - left_output) = 0"
        unfolding slp_right_positive_output_density_def
        by (rule slp_positive_output_density_outside[OF
            radius_nonnegative right_outside])
      show ?thesis by (simp add: right_zero)
    qed
  qed
  show ?thesis unfolding slp_mixed_center_density_def
    by (simp add: zero)
qed

theorem slp_mixed_unit_center_mass_restriction:
  fixes left_type :: "'i::finite itself" and right_type :: "'j::finite itself"
    and B :: real and center :: slp_point
    and Q cutoff q A qt Bterm :: slp_scalar_field
  assumes B_nonnegative: "0 \<le> B"
    and Q_measurable: "Q \<in> borel_measurable lborel"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and q_measurable: "q \<in> borel_measurable lborel"
    and A_measurable: "A \<in> borel_measurable lborel"
    and qt_measurable: "qt \<in> borel_measurable lborel"
    and Bterm_measurable: "Bterm \<in> borel_measurable lborel"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and q_support: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and qt_support: "\<And>x. qt x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
  shows "slp_mixed_center_finite_weighted_absolute_fiber_mass TYPE('i) TYPE('j)
      Q cutoff q A cutoff qt Bterm (\<lambda>_. 1) center =
    slp_mixed_center_finite_weighted_absolute_fiber_mass TYPE('i) TYPE('j)
      Q cutoff q A cutoff qt Bterm (slp_restrict_field (cball 0 (B + (real (Suc CARD('i)) + real (Suc CARD('j))) * (2 * B))) (\<lambda>_. 1)) center"
proof -
  let ?S = "cball 0 (B + (real (Suc CARD('i)) + real (Suc CARD('j))) * (2 * B))"
  let ?D = "slp_mixed_center_density (2 * B) cutoff q qt
    (\<lambda>x. ennreal (norm (A x))) (\<lambda>x. ennreal (norm (Bterm x)))
    CARD('i) CARD('j) Q"
  show ?thesis
  proof (cases "center \<in> ?S")
    case True
    then show ?thesis
      by (simp add: slp_mixed_center_finite_weighted_absolute_fiber_mass_def
          slp_mixed_center_finite_weighted_complex_amplitude_def slp_restrict_field_def)
  next
    case False
    have radius_nonnegative: "0 \<le> 2 * B" using B_nonnegative by simp
    have outside: "B + (real (Suc CARD('i)) + real (Suc CARD('j))) * (2 * B) < norm center"
      using False by (simp add: dist_norm)
    have density_zero: "?D center = 0"
      by (rule slp_mixed_center_density_outside[OF
          radius_nonnegative Q_support outside])
    have mass_bound: "slp_mixed_center_finite_weighted_absolute_fiber_mass TYPE('i) TYPE('j)
      Q cutoff q A cutoff qt Bterm (\<lambda>_. 1) center \<le>
        ennreal (norm (1::complex)) * ?D center"
      by (rule slp_mixed_center_finite_weighted_absolute_fiber_mass_density_bound[OF
          B_nonnegative Q_measurable cutoff_measurable q_measurable
          A_measurable qt_measurable Bterm_measurable Q_support cutoff_support
          q_support qt_support])
    have mass_zero: "slp_mixed_center_finite_weighted_absolute_fiber_mass TYPE('i) TYPE('j)
      Q cutoff q A cutoff qt Bterm (\<lambda>_. 1) center = 0"
      using mass_bound density_zero by simp
    have restricted_zero: "slp_mixed_center_finite_weighted_absolute_fiber_mass TYPE('i) TYPE('j)
      Q cutoff q A cutoff qt Bterm (slp_restrict_field (cball 0 (B + (real (Suc CARD('i)) + real (Suc CARD('j))) * (2 * B))) (\<lambda>_. 1)) center = 0"
      using False
      by (simp add: slp_mixed_center_finite_weighted_absolute_fiber_mass_def
          slp_mixed_center_finite_weighted_complex_amplitude_def slp_restrict_field_def)
    show ?thesis by (simp only: mass_zero restricted_zero)
  qed
qed

context aim_planar_riesz_hls_cauchy
begin

theorem slp_mixed_cauchy_unit_center_cross_masses:
  fixes left_type :: "'i::finite itself" and right_type :: "'j::finite itself"
    and p :: real and Y :: "slp_point set"
    and cutoff q qt Q :: slp_scalar_field
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
  shows "(\<integral>\<^sup>+ center. slp_mixed_center_finite_weighted_absolute_fiber_mass TYPE('i) TYPE('j)
        Q cutoff q (slp_cauchy_transform lo q) cutoff qt (\<lambda>_. 1) (\<lambda>_. 1) center \<partial>lborel) < top_class.top"
    and "(\<integral>\<^sup>+ center. slp_mixed_center_finite_weighted_absolute_fiber_mass TYPE('i) TYPE('j)
        Q cutoff q (\<lambda>_. 1) cutoff qt (slp_cauchy_transform ro qt) (\<lambda>_. 1) center \<partial>lborel) < top_class.top"
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
  let ?mask = "slp_restrict_field (cball 0 (R + (real (Suc CARD('i)) + real (Suc CARD('j))) * (2 * R))) (\<lambda>_. 1)"
  have mask_lp: "aim_complex_lp_on_plane 2 ?mask"
    by (rule slp_complex_indicator_lp_norm(1)) simp_all
  have left_restriction: "slp_mixed_center_finite_weighted_absolute_fiber_mass TYPE('i) TYPE('j)
        Q cutoff q (slp_cauchy_transform lo q) cutoff qt (\<lambda>_. 1) (\<lambda>_. 1) center = slp_mixed_center_finite_weighted_absolute_fiber_mass TYPE('i) TYPE('j)
        Q cutoff q (slp_cauchy_transform lo q) cutoff qt (\<lambda>_. 1) ?mask center"
    for center
    by (rule slp_mixed_unit_center_mass_restriction[OF R_nonnegative
        Q_measurable cutoff_measurable q_measurable A_measurable qt_measurable
        unit_measurable Q_support cutoff_support q_support qt_support])
  have right_restriction: "slp_mixed_center_finite_weighted_absolute_fiber_mass TYPE('i) TYPE('j)
        Q cutoff q (\<lambda>_. 1) cutoff qt (slp_cauchy_transform ro qt) (\<lambda>_. 1) center = slp_mixed_center_finite_weighted_absolute_fiber_mass TYPE('i) TYPE('j)
        Q cutoff q (\<lambda>_. 1) cutoff qt (slp_cauchy_transform ro qt) ?mask center"
    for center
    by (rule slp_mixed_unit_center_mass_restriction[OF R_nonnegative
        Q_measurable cutoff_measurable q_measurable unit_measurable qt_measurable
        B_measurable Q_support cutoff_support q_support qt_support])
  have left_finite: "(\<integral>\<^sup>+ center. slp_mixed_center_finite_weighted_absolute_fiber_mass TYPE('i) TYPE('j)
        Q cutoff q (slp_cauchy_transform lo q) cutoff qt (\<lambda>_. 1) ?mask center \<partial>lborel) < top_class.top"
    by (rule slp_mixed_center_finite_weighted_absolute_mass_left_cauchy_unit_finite[OF
        R_nonnegative M_nonnegative p_lower p_upper Y_measurable Y_bounded
        cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound Q_support
        cutoff_support q_support qt_support mask_lp])
  have right_finite: "(\<integral>\<^sup>+ center. slp_mixed_center_finite_weighted_absolute_fiber_mass TYPE('i) TYPE('j)
        Q cutoff q (\<lambda>_. 1) cutoff qt (slp_cauchy_transform ro qt) ?mask center \<partial>lborel) < top_class.top"
    by (rule slp_mixed_center_finite_weighted_absolute_mass_unit_right_cauchy_finite[OF
        R_nonnegative M_nonnegative p_lower p_upper Y_measurable Y_bounded
        cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound Q_support
        cutoff_support q_support qt_support mask_lp])
  show "(\<integral>\<^sup>+ center. slp_mixed_center_finite_weighted_absolute_fiber_mass TYPE('i) TYPE('j)
        Q cutoff q (slp_cauchy_transform lo q) cutoff qt (\<lambda>_. 1) (\<lambda>_. 1) center \<partial>lborel) < top_class.top"
    using left_finite by (simp only: left_restriction)
  show "(\<integral>\<^sup>+ center. slp_mixed_center_finite_weighted_absolute_fiber_mass TYPE('i) TYPE('j)
        Q cutoff q (\<lambda>_. 1) cutoff qt (slp_cauchy_transform ro qt) (\<lambda>_. 1) center \<partial>lborel) < top_class.top"
    using right_finite by (simp only: right_restriction)
qed

end

end
