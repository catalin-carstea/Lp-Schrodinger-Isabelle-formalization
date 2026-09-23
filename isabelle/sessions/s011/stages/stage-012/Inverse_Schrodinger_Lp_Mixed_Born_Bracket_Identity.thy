theory Inverse_Schrodinger_Lp_Mixed_Born_Bracket_Identity
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Mixed_Preaverage_Transport"
begin

hide_const (open) Commutative_Ring.norm

section \<open>The original mixed Born functional and its four-term bracket\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_mixed_cauchy_preaverage_target_integrable:
  fixes left_type :: "'i::finite itself" and right_type :: "'j::finite itself"
    and p tau :: real and Y :: "slp_point set" and target :: slp_point
    and cutoff q qt Q phi :: slp_scalar_field and lo ro :: slp_cauchy_orientation
  assumes p_lower: "1 < p" and p_upper: "p < 2"
    and Y_bounded: "bounded Y" and Y_measurable: "Y \<in> sets lborel"
    and cutoff_test: "slp_test_function_on Y cutoff"
    and q_lp: "aim_complex_lp_on_plane p q"
    and qt_lp: "aim_complex_lp_on_plane p qt"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and cutoff_q: "\<forall>x. cutoff x * q x = q x"
    and cutoff_qt: "\<forall>x. cutoff x * qt x = qt x"
    and Q_in: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> x \<in> Y"

  shows "integrable lborel
    (\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
      slp_mixed_preaverage_integrand tau Q cutoff q (slp_cauchy_transform lo q)
      cutoff qt (slp_cauchy_transform ro qt) phi target (fst y) (snd y))"
proof -
  let ?A = "slp_cauchy_transform lo q"
  let ?B = "slp_cauchy_transform ro qt"
  let ?Wzero = "(\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_weighted_oscillatory_integrand tau
        Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) (\<lambda>_. 1) (fst y) (snd y))"
  have I0: "integrable lborel ?Wzero"
    by (rule slp_mixed_cauchy_unit_center_amplitudes_integrable(1)[OF
        p_lower p_upper Y_bounded Y_measurable cutoff_test q_lp qt_lp Q_lp
        cutoff_q cutoff_qt Q_in])
  let ?Wone = "(\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_weighted_oscillatory_integrand tau
        Q cutoff q (slp_cauchy_transform lo q) cutoff qt (\<lambda>_. 1) (\<lambda>_. 1) (fst y) (snd y))"
  have I1: "integrable lborel ?Wone"
    by (rule slp_mixed_cauchy_unit_center_amplitudes_integrable(2)[OF
        p_lower p_upper Y_bounded Y_measurable cutoff_test q_lp qt_lp Q_lp
        cutoff_q cutoff_qt Q_in])
  let ?Wtwo = "(\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_weighted_oscillatory_integrand tau
        Q cutoff q (\<lambda>_. 1) cutoff qt (slp_cauchy_transform ro qt) (\<lambda>_. 1) (fst y) (snd y))"
  have I2: "integrable lborel ?Wtwo"
    by (rule slp_mixed_cauchy_unit_center_amplitudes_integrable(3)[OF
        p_lower p_upper Y_bounded Y_measurable cutoff_test q_lp qt_lp Q_lp
        cutoff_q cutoff_qt Q_in])
  let ?Wthree = "(\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_weighted_oscillatory_integrand tau
        Q cutoff q (\<lambda>_. 1) cutoff qt (\<lambda>_. 1) (\<lambda>_. 1) (fst y) (snd y))"
  have I3: "integrable lborel ?Wthree"
    by (rule slp_mixed_cauchy_unit_center_amplitudes_integrable(4)[OF
        p_lower p_upper Y_bounded Y_measurable cutoff_test q_lp qt_lp Q_lp
        cutoff_q cutoff_qt Q_in])
  let ?S = "\<lambda>y. ?Wzero y - ?B target * ?Wone y -
    ?A target * ?Wtwo y + (?A target * ?B target) * ?Wthree y"
  have S_integrable: "integrable lborel ?S"
    by (intro Bochner_Integration.integrable_add Bochner_Integration.integrable_diff
        integrable_mult_right I0 I1 I2 I3)
  let ?T = "\<lambda>y. phi target * ?S y"
  have T_integrable: "integrable lborel ?T"
    by (rule integrable_mult_right[OF S_integrable])
  have T_measurable: "?T \<in> borel_measurable lborel"
    using T_integrable by measurable
  let ?K = "\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
    slp_center_kernel tau (fst y) target"
  have K_continuous: "continuous_on UNIV ?K"
    unfolding slp_center_kernel_def slp_center_phase_def
    by (intro continuous_intros)
  have K_measurable: "?K \<in> borel_measurable lborel"
    using borel_measurable_continuous_onI[OF K_continuous] by simp
  let ?F = "\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
    slp_mixed_preaverage_integrand tau Q cutoff q (slp_cauchy_transform lo q)
      cutoff qt (slp_cauchy_transform ro qt) phi target (fst y) (snd y)"
  have F_identity: "?F y = ?K y * ?T y" for y
    by (simp add: slp_mixed_preaverage_integrand_def
        slp_mixed_weighted_integrand_terminal_factor algebra_simps)
  have F_function: "?F = (\<lambda>y. ?K y * ?T y)"
    by (rule ext) (rule F_identity)
  show ?thesis
  proof (rule Bochner_Integration.integrable_bound[OF T_integrable])
    show "?F \<in> borel_measurable lborel"
      unfolding F_function using K_measurable T_measurable by measurable
    show "AE y in lborel. norm (?F y) \<le> norm (?T y)"
      by (intro AE_I2) (simp add: F_identity norm_mult)
  qed
qed

theorem slp_mixed_preaverage_target_identity:
  fixes left_type :: "'i::finite itself" and right_type :: "'j::finite itself"
    and p tau :: real and Y :: "slp_point set" and target :: slp_point
    and cutoff q qt Q phi :: slp_scalar_field and lo ro :: slp_cauchy_orientation
  assumes p_lower: "1 < p" and p_upper: "p < 2"
    and Y_bounded: "bounded Y" and Y_measurable: "Y \<in> sets lborel"
    and cutoff_test: "slp_test_function_on Y cutoff"
    and q_lp: "aim_complex_lp_on_plane p q"
    and qt_lp: "aim_complex_lp_on_plane p qt"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and cutoff_q: "\<forall>x. cutoff x * q x = q x"
    and cutoff_qt: "\<forall>x. cutoff x * qt x = qt x"
    and Q_in: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> x \<in> Y"

  shows "integral\<^sup>L lborel
      (\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_mixed_preaverage_integrand tau Q cutoff q (slp_cauchy_transform lo q)
      cutoff qt (slp_cauchy_transform ro qt) phi target (fst y) (snd y)) =
     phi target * integral\<^sup>L lborel (\<lambda>root. Q root * slp_center_kernel (-tau) target root *
      slp_left_neumann_iterate CARD('i) tau target cutoff q lo root *
      slp_right_neumann_iterate CARD('j) tau target cutoff qt ro root)"
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

  let ?F = "slp_mixed_preaverage_integrand tau Q cutoff q (slp_cauchy_transform lo q)
      cutoff qt (slp_cauchy_transform ro qt) phi target :: slp_point \<Rightarrow>
    ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex"
  let ?J = "\<lambda>coordinates :: ('i, 'j) slp_mixed_center_finite_coordinates. phi target * Q (fst coordinates) *
      slp_center_kernel (-tau) target (fst coordinates) *
      slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau target
        cutoff q (\<lambda>x. (slp_cauchy_transform lo q) x - (slp_cauchy_transform lo q) target) (fst coordinates) (fst (snd coordinates)) *
      (\<integral>terminal.
        slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau target
          cutoff qt (\<lambda>x. (slp_cauchy_transform ro qt) x - (slp_cauchy_transform ro qt) target) (fst coordinates)
          (snd (snd coordinates), terminal) \<partial>lborel)"
  let ?H = "\<lambda>root. Q root * slp_center_kernel (-tau) target root *
      slp_left_neumann_iterate CARD('i) tau target cutoff q lo root *
      slp_right_neumann_iterate CARD('j) tau target cutoff qt ro root"
  have pre_integrable:
    "integrable lborel (\<lambda>y :: slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
      ?F (fst y) (snd y))"
    by (rule slp_mixed_cauchy_preaverage_target_integrable[OF
        p_lower p_upper Y_bounded Y_measurable cutoff_test q_lp qt_lp Q_lp
        cutoff_q cutoff_qt Q_in])
  have pre_product:
    "integrable ((lborel :: slp_point measure) \<Otimes>\<^sub>M
       (lborel :: ('i, 'j) slp_mixed_center_finite_coordinates measure))
       (case_prod ?F)"
    using pre_integrable by (simp only: lborel_prod split_beta')
  have center_value:
    "integral\<^sup>L lborel (\<lambda>y. ?F (fst y) (snd y)) =
      (\<integral>coordinates. \<integral>center. ?F center coordinates \<partial>lborel \<partial>lborel)"
    using lborel_pair.integral_snd[OF pre_product, symmetric]
    by (simp only: lborel_prod split_beta')
  have coordinates_integrable:
    "integrable lborel (\<lambda>coordinates. \<integral>center. ?F center coordinates \<partial>lborel)"
    by (rule lborel_pair.integrable_snd[OF pre_product])
  have terminal_value:
    "(\<integral>center. ?F center coordinates \<partial>lborel) = ?J coordinates"
    for coordinates
    by (rule slp_mixed_preaverage_terminal_integral[OF
        cutoff_measurable qt_measurable B_measurable])
  have J_integrable: "integrable lborel ?J"
    using coordinates_integrable by (simp only: terminal_value)
  have center_to_J:
    "integral\<^sup>L lborel (\<lambda>y. ?F (fst y) (snd y)) = integral\<^sup>L lborel ?J"
    using center_value by (simp only: terminal_value)
  let ?G = "\<lambda>root. \<integral>(branches :: ((((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) \<times>
        ((slp_point^'j) \<times> (slp_point^'j)))). ?J (root, branches) \<partial>lborel"
  have J_product:
    "integrable ((lborel :: slp_point measure) \<Otimes>\<^sub>M
       (lborel :: ((((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) \<times>
        ((slp_point^'j) \<times> (slp_point^'j))) measure)) ?J"
    using J_integrable by (simp only: lborel_prod)
  have root_integral:
    "integral\<^sup>L lborel ?G = integral\<^sup>L lborel ?J"
    using lborel_pair.integral_fst'[OF J_product]
    by (simp only: lborel_prod)
  have root_identity: "?G root = phi target * ?H root" for root
  proof (cases "Q root = 0")
    case True
    then show ?thesis by simp
  next
    case False
    have root_bound: "norm root \<le> R"
      by (rule Q_support[OF False])
    have separation:
      "(\<integral>(branches :: ((((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) \<times>
        ((slp_point^'j) \<times> (slp_point^'j)))).
        slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau target
          cutoff q (\<lambda>x. ?A x - ?A target) root (fst branches) *
        (\<integral>terminal.
          slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau target
            cutoff qt (\<lambda>x. ?B x - ?B target) root
            (snd branches, terminal) \<partial>lborel) \<partial>lborel) =
       slp_left_neumann_iterate CARD('i) tau target cutoff q lo root *
       slp_right_neumann_iterate CARD('j) tau target cutoff qt ro root"
      by (rule slp_mixed_primitive_fixed_root_branch_separation(2)[OF
          R_nonnegative root_bound cutoff_support q_support qt_support
          p_lower p_upper cutoff_measurable q_lp qt_lp cutoff_bound M_nonnegative])
    show ?thesis
      by (simp only: fst_conv snd_conv mult.assoc
          Bochner_Integration.integral_mult_right_zero separation)
  qed
  have G_function: "?G = (\<lambda>root. phi target * ?H root)"
    by (rule ext) (rule root_identity)
  have root_value:
    "integral\<^sup>L lborel ?G = phi target * integral\<^sup>L lborel ?H"
    by (simp only: G_function Bochner_Integration.integral_mult_right_zero)
  have J_value:
    "integral\<^sup>L lborel ?J = phi target * integral\<^sup>L lborel ?H"
    by (rule trans[OF root_integral[symmetric] root_value])
  show ?thesis by (rule trans[OF center_to_J J_value])
qed

theorem slp_mixed_born_functional_eq_bracket:
  fixes left_type :: "'i::finite itself" and right_type :: "'j::finite itself"
    and p tau :: real and Y :: "slp_point set"
    and cutoff q qt Q phi :: slp_scalar_field and lo ro :: slp_cauchy_orientation
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

  shows "slp_mixed_born_functional CARD('i) CARD('j) tau phi Q cutoff q qt lo ro =
    integral\<^sup>L lborel (slp_mixed_center_finite_bracket_kernel TYPE('i) TYPE('j) tau
      Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) phi)"
    and "integrable lborel (\<lambda>target. phi target * integral\<^sup>L lborel
      (\<lambda>root. Q root * slp_center_kernel (-tau) target root *
      slp_left_neumann_iterate CARD('i) tau target cutoff q lo root *
      slp_right_neumann_iterate CARD('j) tau target cutoff qt ro root))"
proof -
  let ?F = "\<lambda>(target::slp_point) (y::slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates).
    slp_mixed_preaverage_integrand tau Q cutoff q (slp_cauchy_transform lo q)
      cutoff qt (slp_cauchy_transform ro qt) phi target (fst y) (snd y)"
  let ?G = "\<lambda>target. integral\<^sup>L lborel (?F target)"
  let ?H = "\<lambda>target. phi target * integral\<^sup>L lborel (\<lambda>root. Q root * slp_center_kernel (-tau) target root *
      slp_left_neumann_iterate CARD('i) tau target cutoff q lo root *
      slp_right_neumann_iterate CARD('j) tau target cutoff qt ro root)"
  have joint_integrable:
    "integrable lborel (\<lambda>z :: slp_point \<times>
      (slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates).
      ?F (fst z) (snd z))"
    by (rule slp_mixed_cauchy_preaverage_bracket(1)[OF
        p_lower p_upper Y_bounded Y_measurable cutoff_test q_lp qt_lp Q_lp
        cutoff_q cutoff_qt Q_in phi_test])
  have joint_product:
    "integrable ((lborel :: slp_point measure) \<Otimes>\<^sub>M
      (lborel :: (slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates) measure))
      (case_prod ?F)"
    using joint_integrable by (simp only: lborel_prod split_beta')
  have outer_integrable: "integrable lborel ?G"
    by (rule lborel_pair.integrable_fst[OF joint_product])
  have pointwise_value: "?G target = ?H target" for target
    by (rule slp_mixed_preaverage_target_identity[OF
        p_lower p_upper Y_bounded Y_measurable cutoff_test q_lp qt_lp Q_lp
        cutoff_q cutoff_qt Q_in])
  have outer_value: "integral\<^sup>L lborel ?G = integral\<^sup>L lborel ?H"
    by (rule Bochner_Integration.integral_cong[OF refl]) (rule pointwise_value)
  have normalization:
    "(of_real tau :: complex) * inverse (of_real pi) = of_real (tau / pi)"
    by (simp add: divide_inverse)
  have born_preaverage:
    "slp_mixed_born_functional CARD('i) CARD('j) tau phi Q cutoff q qt lo ro =
      of_real (tau / pi) * integral\<^sup>L lborel ?G"
    unfolding slp_mixed_born_functional_def
    by (simp only: normalization outer_value)
  have bracket:
    "of_real (tau / pi) * integral\<^sup>L lborel ?G =
      integral\<^sup>L lborel (slp_mixed_center_finite_bracket_kernel TYPE('i) TYPE('j) tau
        Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) phi)"
    by (rule slp_mixed_cauchy_preaverage_bracket(3)[OF
        p_lower p_upper Y_bounded Y_measurable cutoff_test q_lp qt_lp Q_lp
        cutoff_q cutoff_qt Q_in phi_test])
  show "slp_mixed_born_functional CARD('i) CARD('j) tau phi Q cutoff q qt lo ro =
    integral\<^sup>L lborel (slp_mixed_center_finite_bracket_kernel TYPE('i) TYPE('j) tau
      Q cutoff q (slp_cauchy_transform lo q) cutoff qt (slp_cauchy_transform ro qt) phi)"
    by (rule trans[OF born_preaverage bracket])
  show "integrable lborel ?H"
    using outer_integrable by (simp only: pointwise_value)
qed

end

end
