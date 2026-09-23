theory Inverse_Schrodinger_Lp_Positive_Born_Conjugation_Invariance
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Right_Finite_Oscillatory_Conjugation"
begin

section \<open>Conjugation invariance of positive Born weights\<close>

lemma slp_left_branch_positive_kernel_list_conjugate:
  "slp_left_branch_positive_kernel_list R
      (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (potential x))
      (\<lambda>x. cnj (terminal_value x)) pairs origin terminal =
    slp_left_branch_positive_kernel_list R cutoff potential terminal_value
      pairs origin terminal"
proof (induction pairs arbitrary: origin)
  case Nil
  then show ?case by simp
next
  case (Cons pair pairs)
  then show ?case
    by (simp add: slp_positive_branch_block_weight_def)
qed

lemma slp_left_branch_positive_amplitude_packed_conjugate:
  fixes branch_coord :: "real^((unit + ('i::finite + 'i)) \<times> bool)"
  shows
    "slp_left_branch_positive_amplitude_packed R
        (\<lambda>x. cnj (root_weight x)) (\<lambda>x. cnj (cutoff x))
        (\<lambda>x. cnj (potential x)) (\<lambda>x. cnj (terminal_value x))
        (\<lambda>x. cnj (output_factor x)) root_coord branch_coord =
      slp_left_branch_positive_amplitude_packed R root_weight cutoff potential
        terminal_value output_factor root_coord branch_coord"
  unfolding slp_left_branch_positive_amplitude_packed_def
    slp_left_branch_positive_kernel_packed_def
    slp_left_branch_positive_kernel_joint_def
    slp_left_branch_positive_kernel_finite_def
  by (simp add: slp_left_branch_positive_kernel_list_conjugate)

lemma slp_positive_output_density_conjugate:
  "slp_positive_output_density R (\<lambda>x. cnj (cutoff x))
      (\<lambda>x. cnj (potential x)) terminal_weight n origin target =
    slp_positive_output_density R cutoff potential terminal_weight n
      origin target"
proof (induction n arbitrary: origin target)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by simp
qed

lemma slp_positive_root_output_density_conjugate:
  "slp_positive_root_output_density R (\<lambda>x. cnj (cutoff x))
      (\<lambda>x. cnj (potential x)) terminal_weight n
      (\<lambda>x. cnj (root_weight x)) output =
    slp_positive_root_output_density R cutoff potential terminal_weight n
      root_weight output"
  unfolding slp_positive_root_output_density_def
  by (simp add: slp_positive_output_density_conjugate)

lemma slp_left_one_sided_output_density_conjugate:
  "slp_left_one_sided_output_density R (\<lambda>x. cnj (cutoff x))
      (\<lambda>x. cnj (potential x)) terminal_weight n
      (\<lambda>x. cnj (root_weight x)) output =
    slp_left_one_sided_output_density R cutoff potential terminal_weight n
      root_weight output"
  unfolding slp_left_one_sided_output_density_def
  by (rule slp_positive_root_output_density_conjugate)

end
