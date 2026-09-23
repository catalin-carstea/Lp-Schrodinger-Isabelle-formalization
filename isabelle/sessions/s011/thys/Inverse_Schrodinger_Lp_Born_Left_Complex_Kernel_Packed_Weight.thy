theory Inverse_Schrodinger_Lp_Born_Left_Complex_Kernel_Packed_Weight
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Left_Complex_Kernel_Packed"
begin

section \<open>Positive weights on the exact packed left-branch carrier\<close>

definition slp_left_branch_positive_kernel_joint ::
    "real \<Rightarrow> (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      'i::finite slp_left_branch_finite_coordinates \<Rightarrow> ennreal"
where
  "slp_left_branch_positive_kernel_joint R cutoff potential terminal_value
      coordinates =
    slp_left_branch_positive_kernel_finite R cutoff potential terminal_value
      (\<lambda>i. fst (fst (snd coordinates)) $ i)
      (\<lambda>i. snd (fst (snd coordinates)) $ i)
      (fst coordinates) (snd (snd coordinates))"

definition slp_left_branch_radius_chain_joint ::
    "real \<Rightarrow>
      'i::finite slp_left_branch_finite_coordinates \<Rightarrow> bool"
where
  "slp_left_branch_radius_chain_joint R coordinates \<longleftrightarrow>
    slp_left_branch_radius_chain_finite R
      (\<lambda>i. fst (fst (snd coordinates)) $ i)
      (\<lambda>i. snd (fst (snd coordinates)) $ i)
      (fst coordinates) (snd (snd coordinates))"

lemma slp_left_branch_complex_kernel_joint_positive_weight:
  assumes chain:
    "slp_left_branch_radius_chain_joint R
      (coordinates :: 'i::finite slp_left_branch_finite_coordinates)"
  shows
    "ennreal (norm (slp_left_branch_complex_kernel_joint cutoff potential
        terminal_value coordinates)) =
      slp_left_branch_positive_kernel_joint R cutoff potential terminal_value
        coordinates"
  unfolding slp_left_branch_complex_kernel_joint_def
    slp_left_branch_positive_kernel_joint_def
  by (rule slp_left_branch_complex_kernel_finite_positive_weight)
    (use chain in
      \<open>simp only: slp_left_branch_radius_chain_joint_def\<close>)

definition slp_left_branch_positive_kernel_packed ::
    "real \<Rightarrow> (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      real^bool \<Rightarrow>
      real^((unit + ('i::finite + 'i)) \<times> bool) \<Rightarrow> ennreal"
where
  "slp_left_branch_positive_kernel_packed R cutoff potential terminal_value
      root_coord branch_coord =
    slp_left_branch_positive_kernel_joint R cutoff potential terminal_value
      (slp_one_sided_packed_to_finite_coordinates
        (root_coord, branch_coord))"

definition slp_left_branch_radius_chain_packed ::
    "real \<Rightarrow> real^bool \<Rightarrow>
      real^((unit + ('i::finite + 'i)) \<times> bool) \<Rightarrow> bool"
where
  "slp_left_branch_radius_chain_packed R root_coord branch_coord \<longleftrightarrow>
    slp_left_branch_radius_chain_joint R
      (slp_one_sided_packed_to_finite_coordinates
        (root_coord, branch_coord))"

theorem slp_left_branch_complex_kernel_packed_positive_weight:
  assumes chain:
    "slp_left_branch_radius_chain_packed R root_coord
      (branch_coord :: real^((unit + ('i::finite + 'i)) \<times> bool))"
  shows
    "ennreal (norm (slp_left_branch_complex_kernel_packed cutoff potential
        terminal_value root_coord branch_coord)) =
      slp_left_branch_positive_kernel_packed R cutoff potential terminal_value
        root_coord branch_coord"
  unfolding slp_left_branch_complex_kernel_packed_def
    slp_left_branch_positive_kernel_packed_def
  by (rule slp_left_branch_complex_kernel_joint_positive_weight)
    (use chain in
      \<open>simp only: slp_left_branch_radius_chain_packed_def\<close>)

end
