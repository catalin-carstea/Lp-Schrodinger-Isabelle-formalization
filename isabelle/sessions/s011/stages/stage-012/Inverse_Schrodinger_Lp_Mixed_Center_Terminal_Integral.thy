theory Inverse_Schrodinger_Lp_Mixed_Center_Terminal_Integral
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Joint_Fubini"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Right_Graph_Natural_Finite_Integral"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Exact mixed center-to-terminal integration\<close>

lemma slp_measurable_lborel_integral_translate:
  fixes f :: "slp_point \<Rightarrow> complex"
  assumes f_measurable: "f \<in> borel_measurable lborel"
  shows "integral\<^sup>L lborel (\<lambda>x. f (a + x)) = integral\<^sup>L lborel f"
proof -
  have add_measurable: "(+) a \<in> measurable lborel borel"
    by measurable
  have f_borel: "f \<in> borel_measurable borel"
    using f_measurable by simp
  have transport:
      "integral\<^sup>L (distr lborel borel ((+) a)) f =
        integral\<^sup>L lborel (\<lambda>x. f (a + x))"
    by (rule Bochner_Integration.integral_distr[OF add_measurable f_borel])
  show ?thesis
    using transport by (simp only: lborel_distr_plus)
qed

theorem slp_mixed_center_finite_terminal_integral:
  fixes coordinates ::
    "('i::finite, 'j::finite) slp_mixed_center_finite_coordinates"
  assumes right_cutoff_measurable:
      "right_cutoff \<in> borel_measurable lborel"
    and right_potential_measurable:
      "right_potential \<in> borel_measurable lborel"
  shows
    "(\<integral>center. slp_center_kernel tau target center *
        slp_mixed_center_finite_oscillatory_integrand tau root_weight
          left_cutoff left_potential right_cutoff right_potential center
          coordinates \<partial>lborel) =
      root_weight (fst coordinates) *
        slp_center_kernel (- tau) target (fst coordinates) *
        slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau target
          left_cutoff left_potential (\<lambda>_. 1) (fst coordinates)
          (fst (snd coordinates)) *
        (\<integral>terminal.
          slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau target
            right_cutoff right_potential (\<lambda>_. 1) (fst coordinates)
            (snd (snd coordinates), terminal) \<partial>lborel)"
proof -
  let ?R = "slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau target
    right_cutoff right_potential (\<lambda>_. 1) (fst coordinates)"
  let ?arrays = "snd (snd coordinates)"
  define shift where "shift = slp_mixed_center_finite_right_terminal 0 coordinates"
  have unit_measurable: "(\<lambda>_::slp_point. 1::complex) \<in> borel_measurable lborel"
    by measurable
  have graph_measurable:
      "?R \<in> borel_measurable
        (lborel :: (((slp_point^'j) \<times> (slp_point^'j)) \<times> slp_point) measure)"
    by (rule slp_right_branch_oscillatory_graph_kernel_fixed_root_finite_measurable[
        OF right_cutoff_measurable right_potential_measurable unit_measurable])
  have graph_borel:
      "?R \<in> borel_measurable
        (borel :: (((slp_point^'j) \<times> (slp_point^'j)) \<times> slp_point) measure)"
    using graph_measurable by simp
  have insertion:
      "(\<lambda>t::slp_point. (?arrays, t)) \<in> measurable lborel borel"
    by measurable
  have section_measurable:
      "(\<lambda>t. ?R (?arrays, t)) \<in> borel_measurable lborel"
    using measurable_comp[OF insertion graph_borel]
    by (simp add: comp_def)
  have terminal_translate:
      "slp_mixed_center_finite_right_terminal center coordinates =
        shift + center" for center
    unfolding shift_def slp_mixed_center_finite_right_terminal_def
    by (simp add: algebra_simps)
  have translated:
      "(\<integral>center.
          ?R (?arrays, slp_mixed_center_finite_right_terminal center coordinates)
          \<partial>lborel) = (\<integral>t. ?R (?arrays, t) \<partial>lborel)"
    unfolding terminal_translate
    by (rule slp_measurable_lborel_integral_translate[OF section_measurable])
  show ?thesis
    by (simp only: slp_mixed_center_finite_transpose_integrand_factorization
        Bochner_Integration.integral_mult_right_zero translated)
qed

context aim_planar_riesz_hls
begin

theorem slp_mixed_center_finite_terminal_fubini:
  fixes tau B C p :: real
    and target :: slp_point
    and cutoff left_potential right_potential root_weight ::
      "slp_point \<Rightarrow> complex"
  assumes B_nonnegative: "0 \<le> B"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and left_potential_lp: "aim_complex_lp_on_plane p left_potential"
    and right_potential_lp: "aim_complex_lp_on_plane p right_potential"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and root_weight_integrable: "integrable lborel root_weight"
    and root_support:
      "\<And>x. root_weight x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and left_potential_support:
      "\<And>x. left_potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and right_potential_support:
      "\<And>x. right_potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
  shows
    "(\<integral>center. slp_center_kernel tau target center *
        slp_mixed_center_finite_fiber_integral TYPE('i::finite)
          TYPE('j::finite) tau root_weight cutoff left_potential cutoff
          right_potential center \<partial>lborel) =
      (\<integral>(coordinates ::
          ('i, 'j) slp_mixed_center_finite_coordinates).
        root_weight (fst coordinates) *
          slp_center_kernel (- tau) target (fst coordinates) *
          slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau target
            cutoff left_potential (\<lambda>_. 1) (fst coordinates)
            (fst (snd coordinates)) *
          (\<integral>terminal.
            slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau target
              cutoff right_potential (\<lambda>_. 1) (fst coordinates)
              (snd (snd coordinates), terminal) \<partial>lborel) \<partial>lborel)"
proof -
  have right_measurable: "right_potential \<in> borel_measurable lborel"
    using right_potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have fubini:
      "(\<integral>center. slp_center_kernel tau target center *
          slp_mixed_center_finite_fiber_integral TYPE('i)
            TYPE('j) tau root_weight cutoff left_potential cutoff
            right_potential center \<partial>lborel) =
        (\<integral>(coordinates ::
            ('i, 'j) slp_mixed_center_finite_coordinates). \<integral>center.
          slp_center_kernel tau target center *
            slp_mixed_center_finite_oscillatory_integrand tau root_weight cutoff
              left_potential cutoff right_potential center coordinates
          \<partial>lborel \<partial>lborel)"
    by (rule slp_mixed_center_finite_center_kernel_fubini[OF
        B_nonnegative p_lower p_upper cutoff_measurable left_potential_lp
        right_potential_lp cutoff_bound C_nonnegative root_weight_integrable
        root_support cutoff_support left_potential_support right_potential_support])
  show ?thesis
    using fubini
    by (simp only: slp_mixed_center_finite_terminal_integral[
        OF cutoff_measurable right_measurable])
qed

end

end
