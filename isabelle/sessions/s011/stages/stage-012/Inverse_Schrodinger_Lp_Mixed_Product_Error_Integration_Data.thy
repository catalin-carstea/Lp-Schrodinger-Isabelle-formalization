theory Inverse_Schrodinger_Lp_Mixed_Product_Error_Integration_Data
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Mixed_Principal_Difference_Integrability"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Mixed_Weighted_Product_Error"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Fiber and source data for the two-primitive product error\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_mixed_unit_terminal_fibers_integrable:
  fixes p tau :: real and Y :: "slp_point set"
    and cutoff q qt Q H :: slp_scalar_field
  assumes p_lower: "1 < p" and p_upper: "p < 2"
    and Y_bounded: "bounded Y" and Y_measurable: "Y \<in> sets lborel"
    and cutoff_test: "slp_test_function_on Y cutoff"
    and q_lp: "aim_complex_lp_on_plane p q"
    and qt_lp: "aim_complex_lp_on_plane p qt"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and cutoff_q: "\<forall>x. cutoff x * q x = q x"
    and cutoff_qt: "\<forall>x. cutoff x * qt x = qt x"
    and Q_in: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> x \<in> Y"
  shows "AE center in lborel. integrable lborel
    (slp_mixed_center_finite_weighted_oscillatory_integrand tau Q cutoff q
      (\<lambda>_. 1) cutoff qt (\<lambda>_. 1) H center ::
      ('i::finite, 'j::finite) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
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
  have p_at_least_one: "1 \<le> p" using p_lower by linarith
  have Q_integrable: "integrable lborel Q"
    by (rule slp_bounded_supported_lp_integrable[OF
        p_at_least_one Y_measurable Y_bounded Q_lp Q_in])
  let ?amplitude = "slp_mixed_center_finite_complex_amplitude Q cutoff q cutoff qt ::
    slp_point \<Rightarrow> ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex"
  have amplitude: "AE center in lborel. integrable lborel (?amplitude center)"
    by (rule slp_mixed_center_finite_complex_amplitude_fiber_integrable[OF
        R_nonnegative p_lower p_upper cutoff_measurable q_lp qt_lp
        cutoff_bound M_nonnegative Q_integrable Q_support cutoff_support
        q_support qt_support])
  let ?unit = "\<lambda>_::slp_point. (1::complex)"
  have weighted_amplitude:
      "(slp_mixed_center_finite_weighted_complex_amplitude Q cutoff q ?unit
        cutoff qt ?unit ?unit ::
        slp_point \<Rightarrow> ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex) =
      ?amplitude"
    by (rule ext, rule ext, rule slp_mixed_center_finite_weighted_complex_amplitude_unit)
  have weighted_fibers: "AE center in lborel. integrable lborel
      (slp_mixed_center_finite_weighted_complex_amplitude Q cutoff q ?unit
        cutoff qt ?unit ?unit center ::
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    using amplitude by (simp only: weighted_amplitude)
  have oscillatory: "AE center in lborel. integrable lborel
      (slp_mixed_center_finite_weighted_oscillatory_integrand tau Q cutoff q ?unit
        cutoff qt ?unit ?unit center ::
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    unfolding slp_mixed_center_finite_weighted_oscillatory_integrand_def
    by (rule slp_mixed_center_finite_weighted_oscillatory_fiber_integrable[OF
        slp_mixed_center_finite_residual_measurable weighted_fibers])
  from oscillatory show ?thesis
  proof eventually_elim
    fix center
    assume base: "integrable lborel
      (slp_mixed_center_finite_weighted_oscillatory_integrand tau Q cutoff q ?unit
        cutoff qt ?unit ?unit center ::
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    show "integrable lborel
      (slp_mixed_center_finite_weighted_oscillatory_integrand tau Q cutoff q ?unit
        cutoff qt ?unit H center ::
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
      by (rule slp_mixed_weighted_center_factor_integrable[OF base])
  qed
qed

end

context aim_planar_hls_cauchy
begin

theorem slp_test_two_cauchy_product_integrable:
  fixes p :: real and q qt phi :: slp_scalar_field
    and lo ro :: slp_cauchy_orientation
  assumes p_lower: "1 < p" and p_upper: "p < 2"
    and q_lp: "aim_complex_lp_on_plane p q"
    and qt_lp: "aim_complex_lp_on_plane p qt"
    and phi_test: "slp_test_function_on UNIV phi"
  shows "integrable lborel
    (\<lambda>x. phi x * (slp_cauchy_transform lo q x * slp_cauchy_transform ro qt x))"
proof -
  let ?F = "\<lambda>x. phi x * (slp_cauchy_transform lo q x * slp_cauchy_transform ro qt x)"
  let ?Z = "closure {x. phi x \<noteq> 0}"
  let ?a = "aim_hls_target_exponent p / 2"
  have a_lower: "1 \<le> ?a"
    using slp_hls_target_exponent_above_two[OF p_lower p_upper] by linarith
  have Z_compact: "compact ?Z"
    using phi_test unfolding slp_test_function_on_def by blast
  have Z_bounded: "bounded ?Z" by (rule compact_imp_bounded[OF Z_compact])
  have Z_borel: "?Z \<in> sets borel" by (rule borel_closed[OF closed_closure])
  have Z_measurable: "?Z \<in> sets lborel" using Z_borel by (simp only: sets_lborel)
  have F_lp: "aim_complex_lp_on_plane ?a ?F"
    by (rule slp_test_two_cauchy_product_half_hls_target_lp[OF
        p_lower p_upper q_lp qt_lp phi_test])
  have F_support: "x \<in> ?Z" if "?F x \<noteq> 0" for x
    using that closure_subset[of "{x. phi x \<noteq> 0}"] by auto
  show ?thesis
    by (rule slp_bounded_supported_lp_integrable[OF
        a_lower Z_measurable Z_bounded F_lp F_support])
qed

end

end
