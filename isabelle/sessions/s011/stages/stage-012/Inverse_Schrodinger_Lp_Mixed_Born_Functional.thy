theory Inverse_Schrodinger_Lp_Mixed_Born_Functional
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Mixed_Bracket_Absolute_Convergence"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Right_Graph_Natural_Conjugate"
begin

hide_const (open) Commutative_Ring.norm

section \<open>The original mixed Born functional\<close>

definition slp_mixed_born_functional ::
  "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_scalar_field \<Rightarrow> slp_cauchy_orientation \<Rightarrow>
    slp_cauchy_orientation \<Rightarrow> complex"
where
  "slp_mixed_born_functional n m tau phi Q cutoff q qt lo ro =
    of_real tau * inverse (of_real pi) *
      integral\<^sup>L lborel (\<lambda>center. phi center *
        integral\<^sup>L lborel (\<lambda>root.
          Q root * slp_center_kernel (-tau) center root *
            slp_left_neumann_iterate n tau center cutoff q lo root *
            slp_right_neumann_iterate m tau center cutoff qt ro root))"

context aim_planar_riesz_hls_cauchy
begin

theorem slp_right_natural_graph_integral_eq_neumann:
  fixes n :: nat and B C p tau :: real
    and center origin :: slp_point and cutoff potential :: slp_scalar_field
    and orientation :: slp_cauchy_orientation
  assumes B_nonnegative: "0 \<le> B"
    and origin_bound: "norm origin \<le> B"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and potential_support: "\<And>x. potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and p_lower: "1 < p" and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows "integral\<^sup>L (((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))
      \<Otimes>\<^sub>M (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))))
      \<Otimes>\<^sub>M (lborel :: slp_point measure))
    (slp_right_branch_oscillatory_graph_kernel_natural n tau center cutoff potential
      (\<lambda>x. slp_cauchy_transform orientation potential x -
        slp_cauchy_transform orientation potential center) origin) =
    slp_right_neumann_iterate n tau center cutoff potential orientation origin"
proof -
  let ?M = "(((PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure)))
      \<Otimes>\<^sub>M (PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))))
      \<Otimes>\<^sub>M (lborel :: slp_point measure))"
  let ?T = "\<lambda>x. slp_cauchy_transform orientation potential x -
    slp_cauchy_transform orientation potential center"
  have cutoff_support_cnj:
    "\<And>x. cnj (cutoff x) \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    by (rule cutoff_support) simp
  have potential_support_cnj:
    "\<And>x. cnj (potential x) \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    by (rule potential_support) simp
  have cnj_borel: "cnj \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF continuous_on_cnj[OF continuous_on_id]])
  have cutoff_measurable_cnj: "(\<lambda>x. cnj (cutoff x)) \<in> borel_measurable lborel"
    using measurable_comp[OF cutoff_measurable cnj_borel] by (simp add: comp_def)
  have potential_lp_cnj: "aim_complex_lp_on_plane p (\<lambda>x. cnj (potential x))"
    using potential_lp by simp
  have cutoff_bound_cnj: "\<And>x. norm (cnj (cutoff x)) \<le> C"
    using cutoff_bound by simp
  have terminal_conjugate:
    "(\<lambda>x. cnj (?T x)) =
      (\<lambda>x. slp_cauchy_transform (slp_opposite_cauchy_orientation orientation)
          (\<lambda>y. cnj (potential y)) x -
        slp_cauchy_transform (slp_opposite_cauchy_orientation orientation)
          (\<lambda>y. cnj (potential y)) center)"
    by (rule ext) simp
  have left_representation:
    "integral\<^sup>L ?M (slp_left_branch_oscillatory_graph_kernel_natural n (-tau) center
      (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (potential x))
      (\<lambda>x. slp_cauchy_transform (slp_opposite_cauchy_orientation orientation)
          (\<lambda>y. cnj (potential y)) x -
        slp_cauchy_transform (slp_opposite_cauchy_orientation orientation)
          (\<lambda>y. cnj (potential y)) center) origin) =
      slp_left_neumann_iterate n (-tau) center
        (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (potential x))
        (slp_opposite_cauchy_orientation orientation) origin"
    by (rule slp_left_branch_oscillatory_graph_kernel_natural_integral_eq_neumann_iterate[OF
        B_nonnegative origin_bound cutoff_support_cnj potential_support_cnj
        p_lower p_upper cutoff_measurable_cnj potential_lp_cnj cutoff_bound_cnj C_nonnegative])
  note right_integral = slp_right_branch_oscillatory_graph_kernel_natural_integral[
    where M="?M" and n=n and tau=tau and center=center and cutoff=cutoff
      and potential=potential and terminal_value="?T" and origin=origin]
  show ?thesis using right_integral
    by (simp only: terminal_conjugate left_representation
    slp_left_neumann_iterate_conjugate_eq_right)
qed

theorem slp_finite_graph_integrals_eq_neumann:
  fixes branch_type :: "'i::finite itself" and B C p tau :: real
    and center origin :: slp_point and cutoff potential :: slp_scalar_field
    and orientation :: slp_cauchy_orientation
  assumes B_nonnegative: "0 \<le> B"
    and origin_bound: "norm origin \<le> B"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and potential_support: "\<And>x. potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and p_lower: "1 < p" and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows "integral\<^sup>L (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) measure)
      (slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau center
        cutoff potential (\<lambda>x. slp_cauchy_transform orientation potential x -
        slp_cauchy_transform orientation potential center) origin) =
      slp_left_neumann_iterate CARD('i) tau center cutoff potential orientation origin"
    and "integral\<^sup>L (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) measure)
      (slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau center
        cutoff potential (\<lambda>x. slp_cauchy_transform orientation potential x -
        slp_cauchy_transform orientation potential center) origin) =
      slp_right_neumann_iterate CARD('i) tau center cutoff potential orientation origin"
proof -
  have potential_measurable: "potential \<in> borel_measurable lborel"
    using potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have cauchy_measurable:
    "slp_cauchy_transform orientation potential \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF p_lower p_upper potential_lp])
  have terminal_measurable:
    "(\<lambda>x. slp_cauchy_transform orientation potential x -
        slp_cauchy_transform orientation potential center) \<in> borel_measurable lborel"
    using cauchy_measurable by measurable
  have left_natural: "integral\<^sup>L (((PiM {..<CARD('i)} (\<lambda>_::nat. (lborel :: slp_point measure)))
      \<Otimes>\<^sub>M (PiM {..<CARD('i)} (\<lambda>_::nat. (lborel :: slp_point measure))))
      \<Otimes>\<^sub>M (lborel :: slp_point measure))
      (slp_left_branch_oscillatory_graph_kernel_natural CARD('i) tau center
        cutoff potential (\<lambda>x. slp_cauchy_transform orientation potential x -
        slp_cauchy_transform orientation potential center) origin) =
      slp_left_neumann_iterate CARD('i) tau center cutoff potential orientation origin"
    by (rule slp_left_branch_oscillatory_graph_kernel_natural_integral_eq_neumann_iterate[OF
        B_nonnegative origin_bound cutoff_support potential_support p_lower
        p_upper cutoff_measurable potential_lp cutoff_bound C_nonnegative])
  note left_finite = slp_left_branch_graph_natural_finite_integral[
    where 'i='i and tau=tau and center=center and origin=origin,
    OF cutoff_measurable potential_measurable terminal_measurable]
  show "integral\<^sup>L (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) measure)
      (slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau center
        cutoff potential (\<lambda>x. slp_cauchy_transform orientation potential x -
        slp_cauchy_transform orientation potential center) origin) =
      slp_left_neumann_iterate CARD('i) tau center cutoff potential orientation origin"
    by (rule trans[OF left_finite left_natural])
  have right_natural: "integral\<^sup>L (((PiM {..<CARD('i)} (\<lambda>_::nat. (lborel :: slp_point measure)))
      \<Otimes>\<^sub>M (PiM {..<CARD('i)} (\<lambda>_::nat. (lborel :: slp_point measure))))
      \<Otimes>\<^sub>M (lborel :: slp_point measure))
      (slp_right_branch_oscillatory_graph_kernel_natural CARD('i) tau center
        cutoff potential (\<lambda>x. slp_cauchy_transform orientation potential x -
        slp_cauchy_transform orientation potential center) origin) =
      slp_right_neumann_iterate CARD('i) tau center cutoff potential orientation origin"
    by (rule slp_right_natural_graph_integral_eq_neumann[OF
        B_nonnegative origin_bound cutoff_support potential_support p_lower
        p_upper cutoff_measurable potential_lp cutoff_bound C_nonnegative])
  note right_finite = slp_right_branch_graph_natural_finite_integral[
    where 'i='i and tau=tau and center=center and origin=origin,
    OF cutoff_measurable potential_measurable terminal_measurable]
  show "integral\<^sup>L (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) measure)
      (slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau center
        cutoff potential (\<lambda>x. slp_cauchy_transform orientation potential x -
        slp_cauchy_transform orientation potential center) origin) =
      slp_right_neumann_iterate CARD('i) tau center cutoff potential orientation origin"
    by (rule trans[OF right_finite right_natural])
qed

theorem slp_mixed_born_functional_eq_finite_graph:
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
  shows "slp_mixed_born_functional CARD('i) CARD('j) tau phi Q cutoff q qt lo ro =
      of_real tau * inverse (of_real pi) *
        integral\<^sup>L lborel (\<lambda>center. phi center *
          integral\<^sup>L lborel (\<lambda>root.
            Q root * slp_center_kernel (-tau) center root *
          (integral\<^sup>L (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) measure)
              (slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau center
                cutoff q (\<lambda>x. slp_cauchy_transform lo q x -
                  slp_cauchy_transform lo q center) root)) *
          (integral\<^sup>L (lborel :: (((slp_point^'j) \<times> (slp_point^'j)) \<times> slp_point) measure)
              (slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau center
                cutoff qt (\<lambda>x. slp_cauchy_transform ro qt x -
                  slp_cauchy_transform ro qt center) root))))"
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
  have equality: "(\<lambda>root. Q root * slp_center_kernel (-tau) center root *
          slp_left_neumann_iterate CARD('i) tau center cutoff q lo root *
          slp_right_neumann_iterate CARD('j) tau center cutoff qt ro root) =
      (\<lambda>root. Q root * slp_center_kernel (-tau) center root *
          (integral\<^sup>L (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) measure)
              (slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau center
                cutoff q (\<lambda>x. slp_cauchy_transform lo q x -
                  slp_cauchy_transform lo q center) root)) *
          (integral\<^sup>L (lborel :: (((slp_point^'j) \<times> (slp_point^'j)) \<times> slp_point) measure)
              (slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau center
                cutoff qt (\<lambda>x. slp_cauchy_transform ro qt x -
                  slp_cauchy_transform ro qt center) root)))" for center
  proof (rule ext)
    fix root
    show "Q root * slp_center_kernel (-tau) center root *
          slp_left_neumann_iterate CARD('i) tau center cutoff q lo root *
          slp_right_neumann_iterate CARD('j) tau center cutoff qt ro root = Q root * slp_center_kernel (-tau) center root *
          (integral\<^sup>L (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) measure)
              (slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau center
                cutoff q (\<lambda>x. slp_cauchy_transform lo q x -
                  slp_cauchy_transform lo q center) root)) *
          (integral\<^sup>L (lborel :: (((slp_point^'j) \<times> (slp_point^'j)) \<times> slp_point) measure)
              (slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau center
                cutoff qt (\<lambda>x. slp_cauchy_transform ro qt x -
                  slp_cauchy_transform ro qt center) root))"
    proof (cases "Q root = 0")
      case True
      then show ?thesis by simp
    next
      case False
      have root_bound: "norm root \<le> R" by (rule Q_support[OF False])
      have left: "integral\<^sup>L (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) measure)
              (slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau center
                cutoff q (\<lambda>x. slp_cauchy_transform lo q x -
                  slp_cauchy_transform lo q center) root) =
          slp_left_neumann_iterate CARD('i) tau center cutoff q lo root"
        by (rule slp_finite_graph_integrals_eq_neumann(1)[OF R_nonnegative
            root_bound cutoff_support q_support p_lower p_upper
            cutoff_measurable q_lp cutoff_bound M_nonnegative])
      have right: "integral\<^sup>L (lborel :: (((slp_point^'j) \<times> (slp_point^'j)) \<times> slp_point) measure)
              (slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau center
                cutoff qt (\<lambda>x. slp_cauchy_transform ro qt x -
                  slp_cauchy_transform ro qt center) root) =
          slp_right_neumann_iterate CARD('j) tau center cutoff qt ro root"
        by (rule slp_finite_graph_integrals_eq_neumann(2)[OF R_nonnegative
            root_bound cutoff_support qt_support p_lower p_upper
            cutoff_measurable qt_lp cutoff_bound M_nonnegative])
      show ?thesis by (simp only: left right)
    qed
  qed
  show ?thesis by (simp only: slp_mixed_born_functional_def equality)
qed

end

end
