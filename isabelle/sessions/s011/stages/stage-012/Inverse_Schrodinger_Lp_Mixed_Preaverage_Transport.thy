theory Inverse_Schrodinger_Lp_Mixed_Preaverage_Transport
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Mixed_Primitive_Branch_Separation"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Exact primitive-difference transport before averaging\<close>

lemma slp_finite_graph_terminal_factors:
  fixes coordinates ::
    "((slp_point^'i::finite) \<times> (slp_point^'i)) \<times> slp_point"
    and cutoff potential terminal_value :: slp_scalar_field
  shows
    "slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau center
       cutoff potential terminal_value origin coordinates =
     terminal_value (snd coordinates) *
       slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau center
         cutoff potential (\<lambda>_. 1) origin coordinates"
    "slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau center
       cutoff potential terminal_value origin coordinates =
     terminal_value (snd coordinates) *
       slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau center
         cutoff potential (\<lambda>_. 1) origin coordinates"
proof -
  have left_factor:
    "slp_left_branch_oscillatory_graph_kernel_fixed_root_finite t c d v T root coordinates =
     T (snd coordinates) *
       slp_left_branch_oscillatory_graph_kernel_fixed_root_finite t c d v
         (\<lambda>_. 1) root coordinates" for t c d v T root
    unfolding slp_left_branch_oscillatory_graph_kernel_fixed_root_finite_def
      slp_left_branch_oscillatory_graph_kernel_def
    by (subst slp_left_branch_list_terminal_factor)
       (simp add: algebra_simps)
  show "slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau center
       cutoff potential terminal_value origin coordinates =
     terminal_value (snd coordinates) *
       slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau center
         cutoff potential (\<lambda>_. 1) origin coordinates"
    by (rule left_factor)
  show "slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau center
       cutoff potential terminal_value origin coordinates =
     terminal_value (snd coordinates) *
       slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau center
         cutoff potential (\<lambda>_. 1) origin coordinates"
    unfolding slp_right_branch_oscillatory_graph_kernel_fixed_root_finite_def
    by (subst left_factor)
       (simp only: complex_cnj_mult complex_cnj_cnj complex_cnj_one)
qed

lemma slp_mixed_preaverage_factorization:
  fixes coordinates :: "('i::finite, 'j::finite) slp_mixed_center_finite_coordinates"
    and Q left_cutoff q A right_cutoff qt B phi :: slp_scalar_field
  shows "slp_mixed_preaverage_integrand tau Q left_cutoff q A right_cutoff qt B
      phi target center coordinates = phi target * Q (fst coordinates) *
      slp_center_kernel (-tau) target (fst coordinates) *
      slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau target
        left_cutoff q (\<lambda>x. A x - A target) (fst coordinates) (fst (snd coordinates)) * slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau target
        right_cutoff qt (\<lambda>x. B x - B target) (fst coordinates)
        (snd (snd coordinates), slp_mixed_center_finite_right_terminal center coordinates)"
proof -
  let ?s = "snd (fst (snd coordinates))"
  let ?t = "slp_mixed_center_finite_right_terminal center coordinates"
  let ?L = "slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau target
      left_cutoff q (\<lambda>_. 1) (fst coordinates) (fst (snd coordinates))"
  let ?R = "slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau target
      right_cutoff qt (\<lambda>_. 1) (fst coordinates) (snd (snd coordinates), ?t)"
  have left_factor: "slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau target
        left_cutoff q (\<lambda>x. A x - A target) (fst coordinates) (fst (snd coordinates)) = (A ?s - A target) * ?L"
    using slp_finite_graph_terminal_factors(1)[
      where coordinates="fst (snd coordinates)" and tau=tau and center=target
        and cutoff=left_cutoff and potential=q and origin="fst coordinates" and terminal_value="\<lambda>x. A x - A target"]
    by simp
  have right_factor: "slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau target
        right_cutoff qt (\<lambda>x. B x - B target) (fst coordinates)
        (snd (snd coordinates), slp_mixed_center_finite_right_terminal center coordinates) = (B ?t - B target) * ?R"
    using slp_finite_graph_terminal_factors(2)[
      where coordinates="(snd (snd coordinates), ?t)" and tau=tau and center=target
        and cutoff=right_cutoff and potential=qt and origin="fst coordinates" and terminal_value="\<lambda>x. B x - B target"]
    by simp
  have kernel_symmetry: "slp_center_kernel tau center target = slp_center_kernel tau target center"
    by (rule slp_center_kernel_symmetric)
  have regroup:
    "slp_mixed_preaverage_integrand tau Q left_cutoff q A right_cutoff qt B
      phi target center coordinates =
     phi target * (slp_center_kernel tau target center *
       slp_mixed_center_finite_oscillatory_integrand tau Q
         left_cutoff q right_cutoff qt center coordinates) *
       (A ?s - A target) * (B ?t - B target)"
    unfolding slp_mixed_preaverage_integrand_def
      slp_mixed_center_finite_oscillatory_integrand_def
    by (simp only: kernel_symmetry; simp add: algebra_simps)
  show ?thesis
    by (simp only: regroup slp_mixed_center_finite_transpose_integrand_factorization
        left_factor right_factor; simp add: algebra_simps)
qed

theorem slp_mixed_preaverage_terminal_integral:
  fixes coordinates ::
    "('i::finite, 'j::finite) slp_mixed_center_finite_coordinates"
    and Q left_cutoff q A right_cutoff qt B phi :: slp_scalar_field
  assumes right_cutoff_measurable: "right_cutoff \<in> borel_measurable lborel"
    and qt_measurable: "qt \<in> borel_measurable lborel"
    and B_measurable: "B \<in> borel_measurable lborel"
  shows "(\<integral>center. slp_mixed_preaverage_integrand tau Q left_cutoff q A
      right_cutoff qt B phi target center coordinates \<partial>lborel) =
      phi target * Q (fst coordinates) *
      slp_center_kernel (-tau) target (fst coordinates) *
      slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau target
        left_cutoff q (\<lambda>x. A x - A target) (fst coordinates) (fst (snd coordinates)) *
      (\<integral>terminal.
        slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau target
          right_cutoff qt (\<lambda>x. B x - B target) (fst coordinates)
          (snd (snd coordinates), terminal) \<partial>lborel)"
proof -
  let ?R = "slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau target
    right_cutoff qt (\<lambda>x. B x - B target) (fst coordinates)"
  let ?arrays = "snd (snd coordinates)"
  define shift where "shift = slp_mixed_center_finite_right_terminal 0 coordinates"
  have terminal_measurable: "(\<lambda>x. B x - B target) \<in> borel_measurable lborel"
    using B_measurable by measurable
  have graph_measurable:
      "?R \<in> borel_measurable
        (lborel :: (((slp_point^'j) \<times> (slp_point^'j)) \<times> slp_point) measure)"
    by (rule slp_right_branch_oscillatory_graph_kernel_fixed_root_finite_measurable[
        OF right_cutoff_measurable qt_measurable terminal_measurable])
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
    by (simp only: slp_mixed_preaverage_factorization
        Bochner_Integration.integral_mult_right_zero translated)
qed

end
