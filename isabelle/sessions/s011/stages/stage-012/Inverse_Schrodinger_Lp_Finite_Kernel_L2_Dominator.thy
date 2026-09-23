theory Inverse_Schrodinger_Lp_Finite_Kernel_L2_Dominator
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Mixed_Product_Error_Uniform_Bound"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Common geometry from a fixed test cutoff\<close>

lemma slp_test_cutoff_bounded_geometry:
  fixes Y :: "slp_point set" and cutoff q qt Q :: slp_scalar_field
  assumes target_bounded: "bounded Y"
    and cutoff_test: "slp_test_function_on Y cutoff"
    and cutoff_q: "\<forall>x. cutoff x * q x = q x"
    and cutoff_qt: "\<forall>x. cutoff x * qt x = qt x"
    and Q_in: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> x \<in> Y"
  obtains B M where "0 \<le> (B::real)"
    "0 \<le> (M::real)"
    "cutoff \<in> borel_measurable lborel"
    "\<And>x. norm (cutoff x) \<le> M"
    "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    "\<And>x. qt x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
proof -
  obtain B::real where B_positive: "0 < B"
    and Y_bound: "\<And>x. x \<in> Y \<Longrightarrow> norm x \<le> B"
    by (rule bounded_normE[OF target_bounded]) blast
  have B_nonnegative: "0 \<le> B" using B_positive by simp
  have cutoff_plane: "slp_test_function_on UNIV cutoff"
    using cutoff_test unfolding slp_test_function_on_def by auto
  have cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    by (rule borel_measurable_integrable,
        rule slp_test_function_integrable_bounded(1)[OF cutoff_plane])
  have cutoff_range_bounded: "bounded (range cutoff)"
    by (rule slp_test_function_integrable_bounded(2)[OF cutoff_plane])
  obtain M::real where M_positive: "0 < M"
    and M_bound: "\<And>x. norm (cutoff x) \<le> M"
    using cutoff_range_bounded unfolding bounded_pos by blast
  have M_nonnegative: "0 \<le> M" using M_positive by simp
  have cutoff_in: "x \<in> Y" if "cutoff x \<noteq> 0" for x
    using cutoff_test closure_subset[of "{x. cutoff x \<noteq> 0}"] that
    unfolding slp_test_function_on_def by blast
  have cutoff_support: "norm x \<le> B" if "cutoff x \<noteq> 0" for x
    by (rule Y_bound[OF cutoff_in[OF that]])
  have potential_support: "norm x \<le> B"
    if nonzero: "f x \<noteq> 0" and identity: "\<forall>x. cutoff x * f x = f x"
    for f :: slp_scalar_field and x :: slp_point
  proof -
    have cutoff_nonzero: "cutoff x \<noteq> 0"
      using nonzero identity[rule_format, of x] by auto
    show ?thesis by (rule cutoff_support[OF cutoff_nonzero])
  qed
  have q_support: "norm x \<le> B" if "q x \<noteq> 0" for x
    by (rule potential_support[OF that cutoff_q])
  have qt_support: "norm x \<le> B" if "qt x \<noteq> 0" for x
    by (rule potential_support[OF that cutoff_qt])
  have Q_support: "norm x \<le> B" if "Q x \<noteq> 0" for x
    by (rule Y_bound[OF Q_in[OF that]])
  show ?thesis by (rule that[OF B_nonnegative M_nonnegative
      cutoff_measurable M_bound Q_support cutoff_support q_support qt_support])
qed

section \<open>The exact positive L2 density for the literal finite kernel\<close>

context aim_planar_riesz_hls
begin

theorem slp_finite_kernel_common_l2_density:
  fixes tau B M p :: real and Y :: "slp_point set"
    and cutoff q qt Q :: slp_scalar_field
  assumes B_nonnegative: "0 \<le> B"
    and p_lower: "1 < p" and p_upper: "p < 2"
    and target_measurable: "Y \<in> sets lborel"
    and target_bounded: "bounded Y"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and q_lp: "aim_complex_lp_on_plane p q"
    and qt_lp: "aim_complex_lp_on_plane p qt"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and Q_outside: "\<And>x. x \<notin> Y \<Longrightarrow> Q x = 0"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> M"
    and M_nonnegative: "0 \<le> M"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and q_support: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and qt_support: "\<And>x. qt x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
  shows "slp_positive_ennreal_lp_on_plane 2
      (slp_mixed_center_density (2 * B) cutoff q qt (\<lambda>_. 1) (\<lambda>_. 1)
        CARD('i::finite) CARD('j::finite) Q)"
    "slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j)
      tau Q cutoff q cutoff qt \<in> borel_measurable lborel"
    "AE x in lborel. ennreal (norm
      (slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j)
        tau Q cutoff q cutoff qt x)) \<le>
      slp_mixed_center_density (2 * B) cutoff q qt (\<lambda>_. 1) (\<lambda>_. 1)
        CARD('i) CARD('j) Q x"
proof -
  let ?d = "slp_mixed_center_density (2 * B) cutoff q qt
    (\<lambda>_. 1) (\<lambda>_. 1) CARD('i) CARD('j) Q"
  let ?G = "slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j)
    tau Q cutoff q cutoff qt"
  let ?m = "slp_mixed_center_finite_positive_fiber_mass TYPE('i) TYPE('j)
    (2 * B) Q cutoff q cutoff qt"
  have radius_nonnegative: "0 \<le> 2 * B" using B_nonnegative by simp
  show "slp_positive_ennreal_lp_on_plane 2 ?d"
    by (rule slp_mixed_center_density_unit_terminal_all_orders_finite_target[
        OF radius_nonnegative p_lower p_upper _ target_measurable target_bounded
          cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound M_nonnegative])
      simp
  have Q_integrable: "integrable lborel Q"
    by (rule aim_complex_lp_on_plane_integrable_bounded_support[OF
        _ target_measurable target_bounded Q_lp Q_outside])
      (use p_lower in simp)
  show "?G \<in> borel_measurable lborel"
    by (rule slp_mixed_center_finite_oscillatory_kernel_properties(1)[OF
        B_nonnegative p_lower p_upper cutoff_measurable q_lp qt_lp cutoff_bound
        M_nonnegative Q_integrable Q_support cutoff_support q_support qt_support])
  have kernel_positive_bound: "AE x in lborel. ennreal (norm (?G x)) \<le> ?m x"
    by (rule slp_mixed_center_finite_oscillatory_kernel_properties(2)[OF
        B_nonnegative p_lower p_upper cutoff_measurable q_lp qt_lp cutoff_bound
        M_nonnegative Q_integrable Q_support cutoff_support q_support qt_support])
  have q_measurable: "q \<in> borel_measurable lborel"
    and qt_measurable: "qt \<in> borel_measurable lborel"
    and Q_measurable: "Q \<in> borel_measurable lborel"
    using q_lp qt_lp Q_lp unfolding aim_complex_lp_on_plane_def by blast+
  have unit_measurable:
      "(\<lambda>_::slp_point. (1::complex)) \<in> borel_measurable lborel"
    by measurable
  have mass_density: "?m x = ?d x" for x
  proof -
    have unit:
        "slp_mixed_center_finite_weighted_positive_fiber_mass TYPE('i) TYPE('j)
          (2 * B) Q cutoff q (\<lambda>_. 1) cutoff qt (\<lambda>_. 1) (\<lambda>_. 1) x = ?m x"
      by (rule slp_mixed_center_finite_weighted_positive_fiber_mass_unit)
    have weighted_density:
        "slp_mixed_center_finite_weighted_positive_fiber_mass TYPE('i) TYPE('j)
          (2 * B) Q cutoff q (\<lambda>_. 1) cutoff qt (\<lambda>_. 1) (\<lambda>_. 1) x = ?d x"
      using slp_mixed_center_finite_weighted_positive_fiber_mass_density[
        where R="2 * B" and center=x and center_factor="\<lambda>_::slp_point. (1::complex)"
          and 'i='i and 'j='j, OF Q_measurable cutoff_measurable q_measurable
          unit_measurable qt_measurable unit_measurable] by simp
    show ?thesis using unit weighted_density by simp
  qed
  show "AE x in lborel. ennreal (norm (?G x)) \<le> ?d x"
    using kernel_positive_bound by (simp only: mass_density)
qed

theorem slp_test_cutoff_finite_kernel_l2_dominator:
  fixes p :: real and Y :: "slp_point set"
    and cutoff q qt Q :: slp_scalar_field
  assumes p_lower: "1 < p" and p_upper: "p < 2"
    and target_bounded: "bounded Y" and target_measurable: "Y \<in> sets lborel"
    and cutoff_test: "slp_test_function_on Y cutoff"
    and q_lp: "aim_complex_lp_on_plane p q"
    and qt_lp: "aim_complex_lp_on_plane p qt"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and cutoff_q: "\<forall>x. cutoff x * q x = q x"
    and cutoff_qt: "\<forall>x. cutoff x * qt x = qt x"
    and Q_in: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> x \<in> Y"
  shows "\<exists>d::slp_point \<Rightarrow> ennreal. slp_positive_ennreal_lp_on_plane 2 d \<and>
    (\<forall>tau. slp_mixed_center_finite_oscillatory_kernel TYPE('i::finite) TYPE('j::finite)
        tau Q cutoff q cutoff qt \<in> borel_measurable lborel \<and>
      (AE x in lborel. ennreal (norm
        (slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j)
          tau Q cutoff q cutoff qt x)) \<le> d x))"
proof -
  obtain B M where B_nonnegative: "0 \<le> (B::real)"
    and M_nonnegative: "0 \<le> (M::real)"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> M"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and q_support: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and qt_support: "\<And>x. qt x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
  proof (rule slp_test_cutoff_bounded_geometry[
      where Y=Y and cutoff=cutoff and q=q and qt=qt and Q=Q,
      OF target_bounded cutoff_test cutoff_q cutoff_qt Q_in])
    fix B M :: real
    assume B: "0 \<le> B" and M: "0 \<le> M"
      and measurable: "cutoff \<in> borel_measurable lborel"
      and bound: "\<And>x. norm (cutoff x) \<le> M"
      and Q: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
      and cutoff: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
      and q: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
      and qt: "\<And>x. qt x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    show thesis by (rule that[OF B M measurable bound Q cutoff q qt])
  qed
  have Q_outside: "Q x = 0" if "x \<notin> Y" for x
    using Q_in that by blast
  let ?d = "slp_mixed_center_density (2 * B) cutoff q qt
    (\<lambda>_. 1) (\<lambda>_. 1) CARD('i) CARD('j) Q"
  note common = slp_finite_kernel_common_l2_density[
    where 'i='i and 'j='j, OF B_nonnegative p_lower p_upper
      target_measurable target_bounded cutoff_measurable q_lp qt_lp Q_lp
      Q_outside cutoff_bound M_nonnegative Q_support cutoff_support
      q_support qt_support]
  show ?thesis
  proof (rule exI[of _ ?d], intro conjI allI)
    show "slp_positive_ennreal_lp_on_plane 2 ?d" by (rule common(1))
    fix tau::real
    show "slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j)
        tau Q cutoff q cutoff qt \<in> borel_measurable lborel"
      by (rule common(2))
    show "AE x in lborel. ennreal (norm
        (slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j)
          tau Q cutoff q cutoff qt x)) \<le> ?d x"
      by (rule common(3))
  qed
qed

end

end
