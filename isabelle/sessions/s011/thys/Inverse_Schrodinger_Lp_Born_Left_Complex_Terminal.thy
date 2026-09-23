theory Inverse_Schrodinger_Lp_Born_Left_Complex_Terminal
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Left_Complex_Block"
begin

section \<open>Exact normalized complex left-branch terminal factor\<close>

definition slp_left_branch_complex_terminal ::
    "(slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      slp_point \<Rightarrow> slp_point \<Rightarrow> complex"
where
  "slp_left_branch_complex_terminal cutoff terminal_value origin terminal =
    inverse (of_real pi) *
    slp_cauchy_kernel SLP_Partial_Inverse origin terminal *
    cutoff terminal * terminal_value terminal"

lemma slp_left_branch_complex_terminal_measurable:
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and terminal_measurable[measurable]:
      "terminal_value \<in> borel_measurable lborel"
  shows
    "slp_left_branch_complex_terminal cutoff terminal_value origin
      \<in> borel_measurable lborel"
  unfolding slp_left_branch_complex_terminal_def
  using slp_cauchy_kernel_borel_measurable by measurable

lemma slp_left_branch_complex_terminal_norm:
  "norm (slp_left_branch_complex_terminal cutoff terminal_value origin
      terminal) =
    inverse pi * slp_radial_inverse (origin - terminal) *
    norm (cutoff terminal) * norm (terminal_value terminal)"
  unfolding slp_left_branch_complex_terminal_def
  by (simp add: norm_mult norm_inverse slp_cauchy_kernel_norm
      abs_of_pos pi_gt_zero)

lemma slp_left_branch_complex_terminal_positive_weight:
  assumes radius: "norm (origin - terminal) \<le> R"
  shows
    "ennreal (norm (slp_left_branch_complex_terminal cutoff terminal_value
        origin terminal)) =
      ennreal (inverse pi) *
      ennreal (slp_localized_cauchy_kernel R (origin - terminal)) *
      ennreal (norm (cutoff terminal)) *
      ennreal (norm (terminal_value terminal))"
proof -
  have kernel:
      "slp_localized_cauchy_kernel R (origin - terminal) =
        slp_radial_inverse (origin - terminal)"
    using slp_localized_cauchy_kernel_inside[OF radius]
    by (simp only: slp_radial_inverse_def)
  show ?thesis
    unfolding slp_left_branch_complex_terminal_norm kernel
    by (simp add: ennreal_mult)
qed

end
