theory Inverse_Schrodinger_Lp_Mixed_Joint_Integrability
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Mixed_Cauchy_Bracket_Closure"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Mixed_Center_Density_Unweighted_Mass_Finite_Lp_Root"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Joint absolute integrability of weighted mixed amplitudes\<close>

theorem slp_mixed_weighted_joint_integrable_of_global_mass:
  fixes left_type :: "'i::finite itself" and right_type :: "'j::finite itself"
    and tau :: real
    and Q left_cutoff q A right_cutoff qt B H :: slp_scalar_field
  assumes Q_measurable: "Q \<in> borel_measurable lborel"
    and left_cutoff_measurable: "left_cutoff \<in> borel_measurable lborel"
    and q_measurable: "q \<in> borel_measurable lborel"
    and A_measurable: "A \<in> borel_measurable lborel"
    and right_cutoff_measurable: "right_cutoff \<in> borel_measurable lborel"
    and qt_measurable: "qt \<in> borel_measurable lborel"
    and B_measurable: "B \<in> borel_measurable lborel"
    and H_measurable: "H \<in> borel_measurable lborel"
    and mass_finite:
      "(\<integral>\<^sup>+ center. slp_mixed_center_finite_weighted_absolute_fiber_mass
        TYPE('i) TYPE('j) Q left_cutoff q A right_cutoff qt B H center \<partial>lborel)
        < top_class.top"
  shows "integrable lborel
      (\<lambda>z :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_mixed_center_finite_weighted_complex_amplitude
          Q left_cutoff q A right_cutoff qt B H (fst z) (snd z))"
    and "integrable lborel
      (\<lambda>z :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_mixed_center_finite_weighted_oscillatory_integrand tau
          Q left_cutoff q A right_cutoff qt B H (fst z) (snd z))"
proof -
  let ?amplitude = "slp_mixed_center_finite_weighted_complex_amplitude
    Q left_cutoff q A right_cutoff qt B H ::
    slp_point \<Rightarrow> ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex"
  let ?joint = "\<lambda>z :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
    ?amplitude (fst z) (snd z)"
  let ?oscillatory = "\<lambda>z :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
    slp_mixed_center_finite_weighted_oscillatory_integrand tau
      Q left_cutoff q A right_cutoff qt B H (fst z) (snd z)"
  have amplitude_measurable: "?joint \<in> borel_measurable lborel"
    by (rule slp_mixed_center_finite_weighted_complex_amplitude_measurable[OF
        Q_measurable left_cutoff_measurable q_measurable A_measurable
        right_cutoff_measurable qt_measurable B_measurable H_measurable])
  have norm_joint_measurable:
    "(\<lambda>z. ennreal (norm (?joint z))) \<in> borel_measurable lborel"
    using amplitude_measurable by measurable
  have norm_product_measurable:
    "(\<lambda>z. ennreal (norm (?joint z))) \<in>
      borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using norm_joint_measurable by (simp only: lborel_prod)
  have norm_mass:
    "(\<integral>\<^sup>+ z. ennreal (norm (?joint z)) \<partial>lborel) =
      (\<integral>\<^sup>+ center. slp_mixed_center_finite_weighted_absolute_fiber_mass
        TYPE('i) TYPE('j) Q left_cutoff q A right_cutoff qt B H center \<partial>lborel)"
    using lborel.nn_integral_fst[OF norm_product_measurable]
    by (simp add: lborel_prod slp_mixed_center_finite_weighted_absolute_fiber_mass_def)
  show "integrable lborel ?joint"
    using amplitude_measurable mass_finite norm_mass
    unfolding integrable_iff_bounded by simp
  have oscillatory_measurable: "?oscillatory \<in> borel_measurable lborel"
    using slp_mixed_center_finite_weighted_oscillatory_integrand_joint_measurable[OF
        Q_measurable left_cutoff_measurable q_measurable A_measurable
        right_cutoff_measurable qt_measurable B_measurable H_measurable,
        where frequency=tau and 'i='i and 'j='j]
    by (simp only: lborel_prod split_beta')
  have norm_identity: "norm (?oscillatory z) = norm (?joint z)" for z
    unfolding slp_mixed_center_finite_weighted_oscillatory_integrand_def
      slp_parameterized_real_phase_integrand_def
    by (simp only: norm_mult norm_exp_i_times mult_1_left)
  show "integrable lborel ?oscillatory"
    using oscillatory_measurable mass_finite norm_mass
    unfolding integrable_iff_bounded by (simp add: norm_identity)
qed

context aim_planar_riesz_hls
begin

theorem slp_mixed_unit_terminal_bounded_mass:
  fixes left_type :: "'i::finite itself" and right_type :: "'j::finite itself"
    and p D :: real and Y :: "slp_point set"
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
    and H_bound: "\<And>x. norm (H x) \<le> D"
  shows "(\<integral>\<^sup>+ center. slp_mixed_center_finite_weighted_absolute_fiber_mass
    TYPE('i) TYPE('j) Q cutoff q (\<lambda>_. 1) cutoff qt (\<lambda>_. 1) H center
    \<partial>lborel) < top_class.top"
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
  have unit_measurable: "(\<lambda>_::slp_point. 1::complex) \<in> borel_measurable lborel"
    by measurable
  have unit_weight_measurable: "(\<lambda>_::slp_point. 1::ennreal) \<in> borel_measurable lborel"
    by measurable
  let ?density = "slp_mixed_center_density (2 * R) cutoff q qt
    (\<lambda>_. 1) (\<lambda>_. 1) CARD('i) CARD('j) Q"
  let ?mass = "slp_mixed_center_finite_weighted_absolute_fiber_mass
    TYPE('i) TYPE('j) Q cutoff q (\<lambda>_. 1) cutoff qt (\<lambda>_. 1) H"
  have density_measurable: "?density \<in> borel_measurable lborel"
    by (rule slp_mixed_center_density_measurable[OF cutoff_measurable
        q_measurable qt_measurable unit_weight_measurable unit_weight_measurable
        Q_measurable])
  have density_finite: "(\<integral>\<^sup>+ center. ?density center \<partial>lborel) < top_class.top"
  proof (rule slp_mixed_center_density_unweighted_mass_finite_lp_root[OF _
      p_lower p_upper Y_measurable Y_bounded cutoff_measurable q_lp qt_lp Q_lp
      Q_outside cutoff_bound M_nonnegative])
    show "0 \<le> 2 * R" using R_nonnegative by simp
  qed
  have fiber_bound: "?mass center \<le> ennreal D * ?density center" for center
  proof -
    have raw: "?mass center \<le> ennreal (norm (H center)) * ?density center"
      using slp_mixed_center_finite_weighted_absolute_fiber_mass_density_bound[
        where left_terminal_value="\<lambda>_. 1" and right_terminal_value="\<lambda>_. 1"
          and center_factor=H and 'i='i and 'j='j,
        OF R_nonnegative Q_measurable cutoff_measurable q_measurable
          unit_measurable qt_measurable unit_measurable Q_support
          cutoff_support q_support qt_support]
      by simp
    have coefficient: "ennreal (norm (H center)) \<le> ennreal D"
      by (rule ennreal_leI[OF H_bound])
    have scaled: "ennreal (norm (H center)) * ?density center \<le>
      ennreal D * ?density center"
      by (rule mult_right_mono[OF coefficient]) simp
    show ?thesis by (rule order_trans[OF raw scaled])
  qed
  have mass_bound: "(\<integral>\<^sup>+ center. ?mass center \<partial>lborel) \<le>
    (\<integral>\<^sup>+ center. ennreal D * ?density center \<partial>lborel)"
    by (rule nn_integral_mono) (rule fiber_bound)
  have pull_constant:
    "(\<integral>\<^sup>+ center. ennreal D * ?density center \<partial>lborel) =
      ennreal D * (\<integral>\<^sup>+ center. ?density center \<partial>lborel)"
    by (rule nn_integral_cmult[OF density_measurable])
  have scaled_finite:
    "ennreal D * (\<integral>\<^sup>+ center. ?density center \<partial>lborel) < top_class.top"
    using density_finite by (simp add: ennreal_mult_less_top)
  show ?thesis
    by (rule le_less_trans[OF mass_bound]) (use pull_constant scaled_finite in simp)
qed

end


end
