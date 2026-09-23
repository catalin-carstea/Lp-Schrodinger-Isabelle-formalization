theory Inverse_Schrodinger_Lp_Born_Left_Complex_Amplitude_Support
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Left_Complex_Amplitude_Packed"
begin

section \<open>Bounded supports supply the left-branch radius chain\<close>

lemma slp_norm_sub_le_two_radius:
  assumes B_nonnegative: "0 \<le> B"
    and x_bound: "norm x \<le> B"
    and y_bound: "norm y \<le> B"
  shows "norm (x - y) \<le> 2 * B"
proof -
  have triangle: "norm (x - y) \<le> norm x + norm y"
    using norm_triangle_ineq[of x "- y"] by simp
  show ?thesis
    using triangle x_bound y_bound by linarith
qed

lemma slp_left_branch_complex_kernel_list_support_chain:
  assumes B_nonnegative: "0 \<le> B"
    and origin_bound: "norm origin \<le> B"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and potential_support: "\<And>x. potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and kernel_nonzero:
      "slp_left_branch_complex_kernel_list cutoff potential terminal_value
        pairs origin terminal \<noteq> 0"
  shows "slp_left_branch_radius_chain (2 * B) origin pairs terminal"
  using kernel_nonzero origin_bound
proof (induction pairs arbitrary: origin)
  case Nil
  have cutoff_terminal_nonzero: "cutoff terminal \<noteq> 0"
    using Nil.prems(1)
    unfolding slp_left_branch_complex_kernel_list.simps
      slp_left_branch_complex_terminal_def
    by auto
  have terminal_bound: "norm terminal \<le> B"
    by (rule cutoff_support[OF cutoff_terminal_nonzero])
  have radius: "norm (origin - terminal) \<le> 2 * B"
    by (rule slp_norm_sub_le_two_radius[OF B_nonnegative
          Nil.prems(2) terminal_bound])
  show ?case
    by (simp only: slp_left_branch_radius_chain.simps radius)
next
  case (Cons pair pairs)
  obtain pos_point neg_point where pair: "pair = (pos_point, neg_point)"
    by (cases pair)
  have block_nonzero:
      "slp_left_branch_complex_block cutoff potential origin pos_point
        neg_point \<noteq> 0"
    using Cons.prems(1)
    unfolding pair slp_left_branch_complex_kernel_list.simps
    by auto
  have tail_nonzero:
      "slp_left_branch_complex_kernel_list cutoff potential terminal_value
        pairs neg_point terminal \<noteq> 0"
    using Cons.prems(1)
    unfolding pair slp_left_branch_complex_kernel_list.simps
    by auto
  have cutoff_pos_nonzero: "cutoff pos_point \<noteq> 0"
    using block_nonzero
    unfolding slp_left_branch_complex_block_def by auto
  have potential_neg_nonzero: "potential neg_point \<noteq> 0"
    using block_nonzero
    unfolding slp_left_branch_complex_block_def by auto
  have pos_bound: "norm pos_point \<le> B"
    by (rule cutoff_support[OF cutoff_pos_nonzero])
  have neg_bound: "norm neg_point \<le> B"
    by (rule potential_support[OF potential_neg_nonzero])
  have first_radius: "norm (origin - pos_point) \<le> 2 * B"
    by (rule slp_norm_sub_le_two_radius[OF B_nonnegative
          Cons.prems(2) pos_bound])
  have second_radius: "norm (pos_point - neg_point) \<le> 2 * B"
    by (rule slp_norm_sub_le_two_radius[OF B_nonnegative
          pos_bound neg_bound])
  have tail_chain:
      "slp_left_branch_radius_chain (2 * B) neg_point pairs terminal"
    by (rule Cons.IH[OF tail_nonzero neg_bound])
  show ?case
    unfolding pair
    by (simp only: slp_left_branch_radius_chain.simps fst_conv snd_conv
        first_radius second_radius tail_chain)
qed

lemma slp_left_branch_complex_kernel_finite_support_chain:
  assumes B_nonnegative: "0 \<le> B"
    and origin_bound: "norm origin \<le> B"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and potential_support: "\<And>x. potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and kernel_nonzero:
      "slp_left_branch_complex_kernel_finite cutoff potential terminal_value
        (pos :: 'i::finite \<Rightarrow> slp_point) neg origin terminal \<noteq> 0"
  shows
    "slp_left_branch_radius_chain_finite (2 * B) pos neg origin terminal"
proof -
  have list_kernel_nonzero:
      "slp_left_branch_complex_kernel_list cutoff potential terminal_value
        (slp_finite_branch_pair_list pos neg) origin terminal \<noteq> 0"
    using kernel_nonzero
    unfolding slp_left_branch_complex_kernel_finite_def .
  show ?thesis
    unfolding slp_left_branch_radius_chain_finite_def
    by (rule slp_left_branch_complex_kernel_list_support_chain[OF
          B_nonnegative origin_bound cutoff_support potential_support
          list_kernel_nonzero])
qed

theorem slp_left_branch_complex_amplitude_packed_support_chain:
  fixes branch_coord :: "real^((unit + ('i::finite + 'i)) \<times> bool)"
  assumes B_nonnegative: "0 \<le> B"
    and root_support: "\<And>x. root_weight x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and potential_support: "\<And>x. potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and amplitude_nonzero:
      "slp_left_branch_complex_amplitude_packed root_weight cutoff potential
        terminal_value output_factor root_coord branch_coord \<noteq> 0"
  shows "slp_left_branch_radius_chain_packed (2 * B) root_coord branch_coord"
proof -
  let ?coordinates =
    "slp_one_sided_packed_to_finite_coordinates
      (root_coord, branch_coord)"
  have root_factor_nonzero:
      "root_weight
        (slp_complex_as_point (slp_complex_coordinate_unpack root_coord))
        \<noteq> 0"
    using amplitude_nonzero
    unfolding slp_left_branch_complex_amplitude_packed_def by auto
  have kernel_nonzero:
      "slp_left_branch_complex_kernel_packed cutoff potential terminal_value
        root_coord branch_coord \<noteq> 0"
    using amplitude_nonzero
    unfolding slp_left_branch_complex_amplitude_packed_def by auto
  have root_bound:
      "norm (slp_complex_as_point
        (slp_complex_coordinate_unpack root_coord)) \<le> B"
    by (rule root_support[OF root_factor_nonzero])
  have finite_kernel_nonzero:
      "slp_left_branch_complex_kernel_finite cutoff potential terminal_value
        (\<lambda>i. fst (fst (snd ?coordinates)) $ i)
        (\<lambda>i. snd (fst (snd ?coordinates)) $ i)
        (fst ?coordinates) (snd (snd ?coordinates)) \<noteq> 0"
    using kernel_nonzero
    unfolding slp_left_branch_complex_kernel_packed_def
      slp_left_branch_complex_kernel_joint_def .
  have finite_chain:
      "slp_left_branch_radius_chain_finite (2 * B)
        (\<lambda>i. fst (fst (snd ?coordinates)) $ i)
        (\<lambda>i. snd (fst (snd ?coordinates)) $ i)
        (fst ?coordinates) (snd (snd ?coordinates))"
  proof (rule slp_left_branch_complex_kernel_finite_support_chain[OF
      B_nonnegative _ cutoff_support potential_support finite_kernel_nonzero])
    show "norm (fst ?coordinates) \<le> B"
      using root_bound
      unfolding slp_one_sided_packed_to_finite_coordinates_def Let_def by simp
  qed
  show ?thesis
    using finite_chain
    unfolding slp_left_branch_radius_chain_packed_def
      slp_left_branch_radius_chain_joint_def .
qed

end
