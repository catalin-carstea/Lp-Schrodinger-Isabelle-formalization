theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Support_Chains
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Positive_Weight"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Left_Complex_Amplitude_Support"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Support chains for the finite mixed-center amplitude\<close>

theorem slp_mixed_center_finite_complex_amplitude_support_chains:
  fixes B :: real
    and root_weight left_cutoff left_potential right_cutoff right_potential ::
      "slp_point \<Rightarrow> complex"
    and center :: slp_point
    and coordinates ::
      "('i::finite, 'j::finite) slp_mixed_center_finite_coordinates"
  assumes B_nonnegative: "0 \<le> B"
    and root_support:
      "\<And>x. root_weight x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and left_cutoff_support:
      "\<And>x. left_cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and left_potential_support:
      "\<And>x. left_potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and right_cutoff_support:
      "\<And>x. right_cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and right_potential_support:
      "\<And>x. right_potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and amplitude_nonzero:
      "slp_mixed_center_finite_complex_amplitude root_weight left_cutoff
        left_potential right_cutoff right_potential center coordinates
        \<noteq> 0"
  shows
    "slp_left_branch_radius_chain_joint (2 * B)
        (fst (slp_mixed_center_finite_inserted_coordinates
          center coordinates)) \<and>
      slp_left_branch_radius_chain_joint (2 * B)
        (snd (slp_mixed_center_finite_inserted_coordinates
          center coordinates))"
proof -
  have root_factor_nonzero:
      "root_weight (fst coordinates) \<noteq> 0"
    using amplitude_nonzero
    unfolding slp_mixed_center_finite_complex_amplitude_def by auto
  have left_kernel_nonzero:
      "slp_left_branch_complex_kernel_joint left_cutoff left_potential
          (\<lambda>_. 1)
          (fst (slp_mixed_center_finite_inserted_coordinates
            center coordinates)) \<noteq> 0"
    using amplitude_nonzero
    unfolding slp_mixed_center_finite_complex_amplitude_def by auto
  have right_kernel_nonzero:
      "slp_right_branch_complex_kernel_joint right_cutoff right_potential
          (\<lambda>_. 1)
          (snd (slp_mixed_center_finite_inserted_coordinates
            center coordinates)) \<noteq> 0"
    using amplitude_nonzero
    unfolding slp_mixed_center_finite_complex_amplitude_def by auto
  have root_bound: "norm (fst coordinates) \<le> B"
    by (rule root_support[OF root_factor_nonzero])
  have left_chain:
      "slp_left_branch_radius_chain_joint (2 * B)
        (fst (slp_mixed_center_finite_inserted_coordinates
          center coordinates))"
  proof -
    have finite_kernel_nonzero:
        "slp_left_branch_complex_kernel_finite left_cutoff left_potential
            (\<lambda>_. 1)
            (\<lambda>i. fst (fst (snd (fst
              (slp_mixed_center_finite_inserted_coordinates
                center coordinates)))) $ i)
            (\<lambda>i. snd (fst (snd (fst
              (slp_mixed_center_finite_inserted_coordinates
                center coordinates)))) $ i)
            (fst (fst (slp_mixed_center_finite_inserted_coordinates
              center coordinates)))
            (snd (snd (fst (slp_mixed_center_finite_inserted_coordinates
              center coordinates)))) \<noteq> 0"
      using left_kernel_nonzero
      unfolding slp_left_branch_complex_kernel_joint_def .
    have inserted_origin:
        "fst (fst (slp_mixed_center_finite_inserted_coordinates
          center coordinates)) = fst coordinates"
      unfolding slp_mixed_center_finite_inserted_coordinates_def by simp
    show ?thesis
      unfolding slp_left_branch_radius_chain_joint_def
      by (rule slp_left_branch_complex_kernel_finite_support_chain[OF
            B_nonnegative _ left_cutoff_support left_potential_support
            finite_kernel_nonzero])
        (use root_bound inserted_origin in simp)
  qed
  have right_inner_nonzero:
      "slp_left_branch_complex_kernel_joint
          (\<lambda>x. cnj (right_cutoff x))
          (\<lambda>x. cnj (right_potential x))
          (\<lambda>x. cnj (1 :: complex))
          (snd (slp_mixed_center_finite_inserted_coordinates
            center coordinates)) \<noteq> 0"
    using right_kernel_nonzero
    unfolding slp_right_branch_complex_kernel_joint_def by simp
  have conjugate_cutoff_support:
      "\<And>x. cnj (right_cutoff x) \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    using right_cutoff_support by simp
  have conjugate_potential_support:
      "\<And>x. cnj (right_potential x) \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    using right_potential_support by simp
  have right_chain:
      "slp_left_branch_radius_chain_joint (2 * B)
        (snd (slp_mixed_center_finite_inserted_coordinates
          center coordinates))"
  proof -
    have finite_kernel_nonzero:
        "slp_left_branch_complex_kernel_finite
            (\<lambda>x. cnj (right_cutoff x))
            (\<lambda>x. cnj (right_potential x))
            (\<lambda>x. cnj (1 :: complex))
            (\<lambda>i. fst (fst (snd (snd
              (slp_mixed_center_finite_inserted_coordinates
                center coordinates)))) $ i)
            (\<lambda>i. snd (fst (snd (snd
              (slp_mixed_center_finite_inserted_coordinates
                center coordinates)))) $ i)
            (fst (snd (slp_mixed_center_finite_inserted_coordinates
              center coordinates)))
            (snd (snd (snd (slp_mixed_center_finite_inserted_coordinates
              center coordinates)))) \<noteq> 0"
      using right_inner_nonzero
      unfolding slp_left_branch_complex_kernel_joint_def .
    have inserted_origin:
        "fst (snd (slp_mixed_center_finite_inserted_coordinates
          center coordinates)) = fst coordinates"
      unfolding slp_mixed_center_finite_inserted_coordinates_def by simp
    show ?thesis
      unfolding slp_left_branch_radius_chain_joint_def
      by (rule slp_left_branch_complex_kernel_finite_support_chain[OF
            B_nonnegative _ conjugate_cutoff_support
            conjugate_potential_support finite_kernel_nonzero])
        (use root_bound inserted_origin in simp)
  qed
  show ?thesis
    using left_chain right_chain by blast
qed

end
