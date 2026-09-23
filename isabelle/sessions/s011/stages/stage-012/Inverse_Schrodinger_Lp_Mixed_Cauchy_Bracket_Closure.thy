theory Inverse_Schrodinger_Lp_Mixed_Cauchy_Bracket_Closure
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Mixed_Smooth_Cross_Error_Integrability"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Mixed_Center_Cauchy_Terminal_Smooth_Error_Integral_Decay"
begin

hide_const (open) Commutative_Ring.norm

section \<open>The finite positive-order mixed bracket with actual Cauchy terminals\<close>

context slp_mixed_center_error_hls_plancherel
begin

theorem slp_mixed_cauchy_bracket_integrable_expansion:
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
    and frequency: "2 \<le> tau"
  shows "AE center in lborel. integrable lborel
    (slp_mixed_center_finite_bracket_integrand tau Q cutoff q (slp_cauchy_transform lo q)
      cutoff qt (slp_cauchy_transform ro qt) phi center :: ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    and "integrable lborel (slp_mixed_center_finite_bracket_kernel TYPE('i) TYPE('j) tau
      Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) phi)"
    and "integral\<^sup>L lborel (slp_mixed_center_finite_bracket_kernel TYPE('i) TYPE('j) tau
      Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) phi) =
    integral\<^sup>L lborel (slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_kernel
      TYPE('i) TYPE('j) tau Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) phi)
    + integral\<^sup>L lborel (slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) tau
      Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt)
      (\<lambda>x. slp_center_average tau phi x - phi x))
    - integral\<^sup>L lborel (slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) tau
      Q cutoff q (slp_cauchy_transform lo q) cutoff qt (\<lambda>_. 1)
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * (slp_cauchy_transform ro qt) z) x -
        phi x * (slp_cauchy_transform ro qt) x))
    - integral\<^sup>L lborel (slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) tau
      Q cutoff q (\<lambda>_. 1) cutoff qt (slp_cauchy_transform ro qt)
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * (slp_cauchy_transform lo q) z) x -
        phi x * (slp_cauchy_transform lo q) x))
    + integral\<^sup>L lborel (slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) tau
      Q cutoff q (\<lambda>_. 1) cutoff qt (\<lambda>_. 1)
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * ((slp_cauchy_transform lo q) z * (slp_cauchy_transform ro qt) z)) x -
        phi x * ((slp_cauchy_transform lo q) x * (slp_cauchy_transform ro qt) x)))"
proof -
  interpret mixed_hls: aim_planar_riesz_hls_cauchy by unfold_locales
  let ?A = "slp_cauchy_transform lo q"
  let ?B = "slp_cauchy_transform ro qt"
  let ?full = "slp_mixed_center_finite_bracket_kernel TYPE('i) TYPE('j) tau
    Q cutoff q ?A cutoff qt ?B phi"
  let ?bracket = "slp_mixed_center_finite_bracket_integrand tau
    Q cutoff q ?A cutoff qt ?B phi ::
    slp_point \<Rightarrow> ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex"
  let ?K0 = "slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_kernel
      TYPE('i) TYPE('j) tau Q cutoff q ?A cutoff qt ?B phi"
  let ?K1 = "slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) tau
      Q cutoff q ?A cutoff qt ?B
      (\<lambda>x. slp_center_average tau phi x - phi x)"
  let ?K2 = "slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) tau
      Q cutoff q ?A cutoff qt (\<lambda>_. 1)
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * ?B z) x -
        phi x * ?B x)"
  let ?K3 = "slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) tau
      Q cutoff q (\<lambda>_. 1) cutoff qt ?B
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * ?A z) x -
        phi x * ?A x)"
  let ?K4 = "slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) tau
      Q cutoff q (\<lambda>_. 1) cutoff qt (\<lambda>_. 1)
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * (?A z * ?B z)) x -
        phi x * (?A x * ?B x))"
  let ?F0 = "(\<lambda>center. slp_mixed_center_finite_weighted_oscillatory_integrand tau
      Q cutoff q (\<lambda>x. ?A x - ?A center)
      cutoff qt (\<lambda>x. ?B x - ?B center) phi center ::
      ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
  let ?F1 = "(\<lambda>center. slp_mixed_center_finite_weighted_oscillatory_integrand tau
      Q cutoff q ?A cutoff qt ?B
      (\<lambda>x. slp_center_average tau phi x - phi x) center ::
      ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
  let ?F2 = "(\<lambda>center. slp_mixed_center_finite_weighted_oscillatory_integrand tau
      Q cutoff q ?A cutoff qt (\<lambda>_. 1)
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * ?B z) x -
        phi x * ?B x) center ::
      ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
  let ?F3 = "(\<lambda>center. slp_mixed_center_finite_weighted_oscillatory_integrand tau
      Q cutoff q (\<lambda>_. 1) cutoff qt ?B
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * ?A z) x -
        phi x * ?A x) center ::
      ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
  let ?F4 = "(\<lambda>center. slp_mixed_center_finite_weighted_oscillatory_integrand tau
      Q cutoff q (\<lambda>_. 1) cutoff qt (\<lambda>_. 1)
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * (?A z * ?B z)) x -
        phi x * (?A x * ?B x)) center ::
      ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
  have cutoff_univ: "slp_test_function_on UNIV cutoff"
    using cutoff_test unfolding slp_test_function_on_def by blast
  have cutoff_integrable: "integrable lborel cutoff"
    by (rule slp_test_function_integrable_bounded(1)[OF cutoff_univ])
  have cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    using cutoff_integrable by measurable
  have Q_measurable: "Q \<in> borel_measurable lborel"
    using Q_lp unfolding aim_complex_lp_on_plane_def by blast
  have q_measurable: "q \<in> borel_measurable lborel"
    using q_lp unfolding aim_complex_lp_on_plane_def by blast
  have qt_measurable: "qt \<in> borel_measurable lborel"
    using qt_lp unfolding aim_complex_lp_on_plane_def by blast
  have A_measurable: "?A \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF p_lower p_upper q_lp])
  have B_measurable: "?B \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF p_lower p_upper qt_lp])
  have phi_integrable: "integrable lborel phi"
    by (rule slp_test_function_integrable_bounded(1)[OF phi_test])
  have phi_B: "integrable lborel (\<lambda>x. phi x * ?B x)"
    by (rule slp_test_cauchy_product_integrable[OF p_lower p_upper qt_lp phi_test])
  have phi_A: "integrable lborel (\<lambda>x. phi x * ?A x)"
    by (rule slp_test_cauchy_product_integrable[OF p_lower p_upper q_lp phi_test])
  have phi_AB: "integrable lborel (\<lambda>x. phi x * (?A x * ?B x))"
    by (rule slp_test_two_cauchy_product_integrable[OF
        p_lower p_upper q_lp qt_lp phi_test])
  have full_measurable: "?full \<in> borel_measurable lborel"
    by (rule slp_mixed_finite_bracket_measurable(2)[OF
        Q_measurable cutoff_measurable q_measurable A_measurable
        cutoff_measurable qt_measurable B_measurable phi_integrable phi_B phi_A phi_AB])
  note principal = mixed_hls.slp_mixed_cauchy_difference_integrable[
    where 'i='i and 'j='j and tau=tau and lo=lo and ro=ro, OF
      p_lower p_upper Y_bounded Y_measurable cutoff_test q_lp qt_lp Q_lp
      cutoff_q cutoff_qt Q_in phi_test]
  note smooth = mixed_hls.slp_mixed_smooth_error_integrable[
    where 'i='i and 'j='j and tau=tau and lo=lo and ro=ro, OF
      p_lower p_upper Y_bounded Y_measurable cutoff_test q_lp qt_lp Q_lp
      cutoff_q cutoff_qt Q_in phi_test]
  have tau_positive: "0 < tau" using frequency by linarith
  note cross = mixed_hls.slp_mixed_cross_errors_integrable[
    where 'i='i and 'j='j and tau=tau and lo=lo and ro=ro, OF
      p_lower p_upper Y_bounded Y_measurable cutoff_test q_lp qt_lp Q_lp
      cutoff_q cutoff_qt Q_in phi_test
      hormander_euclidean_l2_fourier_plancherel tau_positive]
  have product_fiber: "AE center in lborel. integrable lborel (?F4 center)"
    by (rule mixed_hls.slp_mixed_unit_terminal_fibers_integrable[OF
        p_lower p_upper Y_bounded Y_measurable cutoff_test q_lp qt_lp Q_lp
        cutoff_q cutoff_qt Q_in])
  have product_center: "integrable lborel ?K4"
    using slp_mixed_weighted_cauchy_product_error(1)[
      where 'i='i and 'j='j and left_orientation=lo and right_orientation=ro, OF
        p_lower p_upper Y_bounded Y_measurable cutoff_test q_lp qt_lp Q_lp
        cutoff_q cutoff_qt Q_in phi_test] frequency by blast
  have principal_fiber: "AE center in lborel. integrable lborel (?F0 center)"
    using principal(1) by blast
  have smooth_fiber: "AE center in lborel. integrable lborel (?F1 center)"
    using smooth(1) by blast
  have left_fiber: "AE center in lborel. integrable lborel (?F2 center)"
    using cross(1) by blast
  have right_fiber: "AE center in lborel. integrable lborel (?F3 center)"
    using cross(3) by blast
  have principal_center: "integrable lborel ?K0" using principal(2) by blast
  have smooth_center: "integrable lborel ?K1" using smooth(2) by blast
  have left_center: "integrable lborel ?K2" using cross(2) by blast
  have right_center: "integrable lborel ?K3" using cross(4) by blast
  have fibers: "AE center in lborel.
      integrable lborel (?F0 center) \<and> integrable lborel (?F1 center) \<and>
      integrable lborel (?F2 center) \<and> integrable lborel (?F3 center) \<and>
      integrable lborel (?F4 center)"
    using principal_fiber smooth_fiber left_fiber right_fiber product_fiber
    by eventually_elim blast
  show "AE center in lborel. integrable lborel (?bracket center)"
    using fibers
  proof eventually_elim
    fix center
    assume data: "integrable lborel (?F0 center) \<and> integrable lborel (?F1 center) \<and>
      integrable lborel (?F2 center) \<and> integrable lborel (?F3 center) \<and>
      integrable lborel (?F4 center)"
    show "integrable lborel (?bracket center)"
      by (rule slp_mixed_finite_bracket_kernel_expansion(1))
        (use data in blast)+
  qed
  note expansion = slp_mixed_finite_bracket_global_expansion[OF
    full_measurable fibers principal_center smooth_center left_center right_center product_center]
  show "integrable lborel ?full" by (rule expansion(1))
  show "integral\<^sup>L lborel ?full =
      integral\<^sup>L lborel ?K0 + integral\<^sup>L lborel ?K1 -
      integral\<^sup>L lborel ?K2 - integral\<^sup>L lborel ?K3 + integral\<^sup>L lborel ?K4"
    by (rule expansion(2))
qed

theorem slp_mixed_cauchy_bracket_tendsto_zero:
  fixes active_type ::
      "((unit + (((('i::finite) + 'i) + unit) + (('j::finite) + 'j))) \<times> bool) itself"
    and p :: real and Y :: "slp_point set"
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
    and stationary_phase: "hormander_quadratic_stationary_phase_decay_claim active_type"
    and density: "evans_compact_smooth_l1_density_claim active_type"
    and smooth_uniform:
      "uniform_limit UNIV (\<lambda>tau. slp_center_average tau phi) phi at_top"
  shows "((\<lambda>tau. integral\<^sup>L lborel (slp_mixed_center_finite_bracket_kernel TYPE('i) TYPE('j) tau
      Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) phi)) \<longlongrightarrow> 0) at_top"
proof -
  interpret mixed_hls: aim_planar_riesz_hls_cauchy by unfold_locales
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
  have phi_bounded: "bounded (range phi)"
    by (rule slp_test_function_integrable_bounded(2)[OF phi_test])
  obtain D where phi_bound: "\<And>x. norm (phi x) \<le> D"
    using phi_bounded unfolding bounded_iff by blast
  let ?full = "\<lambda>tau. integral\<^sup>L lborel (slp_mixed_center_finite_bracket_kernel TYPE('i) TYPE('j) tau
      Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) phi)"
  let ?J0 = "\<lambda>tau. integral\<^sup>L lborel (slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_kernel
      TYPE('i) TYPE('j) tau Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) phi)"
  let ?J1 = "\<lambda>tau. integral\<^sup>L lborel (slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) tau
      Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt)
      (\<lambda>x. slp_center_average tau phi x - phi x))"
  let ?J2 = "\<lambda>tau. integral\<^sup>L lborel (slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) tau
      Q cutoff q (slp_cauchy_transform lo q) cutoff qt (\<lambda>_. 1)
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * (slp_cauchy_transform ro qt) z) x -
        phi x * (slp_cauchy_transform ro qt) x))"
  let ?J3 = "\<lambda>tau. integral\<^sup>L lborel (slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) tau
      Q cutoff q (\<lambda>_. 1) cutoff qt (slp_cauchy_transform ro qt)
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * (slp_cauchy_transform lo q) z) x -
        phi x * (slp_cauchy_transform lo q) x))"
  let ?J4 = "\<lambda>tau. integral\<^sup>L lborel (slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) tau
      Q cutoff q (\<lambda>_. 1) cutoff qt (\<lambda>_. 1)
      (\<lambda>x. slp_center_average tau (\<lambda>z. phi z * ((slp_cauchy_transform lo q) z * (slp_cauchy_transform ro qt) z)) x -
        phi x * ((slp_cauchy_transform lo q) x * (slp_cauchy_transform ro qt) x)))"
  have principal_limit: "(?J0 \<longlongrightarrow> 0) at_top"
    by (rule mixed_hls.slp_mixed_center_finite_weighted_oscillatory_cauchy_center_diff_global_decay[OF
        stationary_phase density R_nonnegative M_nonnegative p_lower p_upper
        Y_measurable Y_bounded phi_test phi_bound cutoff_measurable q_lp qt_lp Q_lp
        Q_outside cutoff_bound Q_support cutoff_support q_support qt_support])
  have smooth_limit: "(?J1 \<longlongrightarrow> 0) at_top"
    by (rule mixed_hls.slp_mixed_center_finite_weighted_cauchy_terminal_smooth_error_integral_decay[OF
        R_nonnegative M_nonnegative p_lower p_upper Y_measurable Y_bounded phi_test
        cutoff_measurable q_lp qt_lp Q_lp Q_outside cutoff_bound Q_support
        cutoff_support q_support qt_support smooth_uniform])
  have left_limit: "(?J2 \<longlongrightarrow> 0) at_top"
    by (rule mixed_hls.slp_mixed_center_finite_left_cauchy_right_unit_error_integral_decay[OF
        hormander_euclidean_l2_fourier_plancherel R_nonnegative M_nonnegative
        p_lower p_upper Y_measurable Y_bounded phi_test cutoff_measurable
        q_lp qt_lp Q_lp Q_outside cutoff_bound Q_support cutoff_support
        q_support qt_support])
  have right_limit: "(?J3 \<longlongrightarrow> 0) at_top"
    by (rule mixed_hls.slp_mixed_center_finite_left_unit_right_cauchy_error_integral_decay[OF
        hormander_euclidean_l2_fourier_plancherel R_nonnegative M_nonnegative
        p_lower p_upper Y_measurable Y_bounded phi_test cutoff_measurable
        q_lp qt_lp Q_lp Q_outside cutoff_bound Q_support cutoff_support
        q_support qt_support])
  have product_limit: "(?J4 \<longlongrightarrow> 0) at_top"
    by (rule slp_mixed_weighted_cauchy_product_error(2)[OF
        p_lower p_upper Y_bounded Y_measurable cutoff_test q_lp qt_lp Q_lp
        cutoff_q cutoff_qt Q_in phi_test])
  have first_sum: "((\<lambda>tau. ?J0 tau + ?J1 tau) \<longlongrightarrow> 0 + 0) at_top"
    by (rule tendsto_add[OF principal_limit smooth_limit])
  have second_sum: "((\<lambda>tau. ?J0 tau + ?J1 tau - ?J2 tau) \<longlongrightarrow> 0 + 0 - 0) at_top"
    by (rule tendsto_diff[OF first_sum left_limit])
  have third_sum: "((\<lambda>tau. ?J0 tau + ?J1 tau - ?J2 tau - ?J3 tau)
      \<longlongrightarrow> 0 + 0 - 0 - 0) at_top"
    by (rule tendsto_diff[OF second_sum right_limit])
  have last_sum: "((\<lambda>tau. ?J0 tau + ?J1 tau - ?J2 tau - ?J3 tau + ?J4 tau)
      \<longlongrightarrow> 0 + 0 - 0 - 0 + 0) at_top"
    by (rule tendsto_add[OF third_sum product_limit])
  have sum_limit: "((\<lambda>tau. ?J0 tau + ?J1 tau - ?J2 tau - ?J3 tau + ?J4 tau)
      \<longlongrightarrow> 0) at_top" using last_sum by simp
  have eventual_expansion: "\<forall>\<^sub>F tau in at_top.
      ?full tau = ?J0 tau + ?J1 tau - ?J2 tau - ?J3 tau + ?J4 tau"
    using eventually_ge_at_top[of "(2::real)"]
  proof eventually_elim
    fix tau::real
    assume frequency: "2 \<le> tau"
    show "?full tau = ?J0 tau + ?J1 tau - ?J2 tau - ?J3 tau + ?J4 tau"
      by (rule slp_mixed_cauchy_bracket_integrable_expansion(3)[OF
          p_lower p_upper Y_bounded Y_measurable cutoff_test q_lp qt_lp Q_lp
          cutoff_q cutoff_qt Q_in phi_test frequency])
  qed
  from sum_limit show ?thesis
    by (rule tendsto_cong[OF eventual_expansion, THEN iffD2])
qed

end

end
