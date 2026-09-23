theory Inverse_Schrodinger_Lp_Born_Left_Complex_Kernel_Finite
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Left_Complex_Kernel_List"
    "HOL-Library.Countable_Set"
begin

section \<open>Finite-type coordinates for the complex left-branch kernel\<close>

definition slp_finite_branch_pair_list ::
    "('i::finite \<Rightarrow> slp_point) \<Rightarrow>
      ('i \<Rightarrow> slp_point) \<Rightarrow>
      (slp_point \<times> slp_point) list"
where
  "slp_finite_branch_pair_list pos neg =
    map (\<lambda>k. (pos (from_nat_into UNIV k),
      neg (from_nat_into UNIV k))) [0..<CARD('i)]"

lemma slp_finite_branch_pair_list_length [simp]:
  "length (slp_finite_branch_pair_list
      (pos :: 'i::finite \<Rightarrow> slp_point) neg) = CARD('i)"
  by (simp add: slp_finite_branch_pair_list_def)

lemma slp_finite_branch_pair_list_nth:
  assumes k: "k < CARD('i::finite)"
  shows
    "slp_finite_branch_pair_list
        (pos :: 'i \<Rightarrow> slp_point) neg ! k =
      (pos (from_nat_into UNIV k), neg (from_nat_into UNIV k))"
  using k by (simp add: slp_finite_branch_pair_list_def)

definition slp_left_branch_complex_kernel_finite ::
    "(slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      ('i::finite \<Rightarrow> slp_point) \<Rightarrow>
      ('i \<Rightarrow> slp_point) \<Rightarrow>
      slp_point \<Rightarrow> slp_point \<Rightarrow> complex"
where
  "slp_left_branch_complex_kernel_finite cutoff potential terminal_value
      pos neg origin terminal =
    slp_left_branch_complex_kernel_list cutoff potential terminal_value
      (slp_finite_branch_pair_list pos neg) origin terminal"

definition slp_left_branch_positive_kernel_finite ::
    "real \<Rightarrow> (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      ('i::finite \<Rightarrow> slp_point) \<Rightarrow>
      ('i \<Rightarrow> slp_point) \<Rightarrow>
      slp_point \<Rightarrow> slp_point \<Rightarrow> ennreal"
where
  "slp_left_branch_positive_kernel_finite R cutoff potential terminal_value
      pos neg origin terminal =
    slp_left_branch_positive_kernel_list R cutoff potential terminal_value
      (slp_finite_branch_pair_list pos neg) origin terminal"

definition slp_left_branch_radius_chain_finite ::
    "real \<Rightarrow> ('i::finite \<Rightarrow> slp_point) \<Rightarrow>
      ('i \<Rightarrow> slp_point) \<Rightarrow>
      slp_point \<Rightarrow> slp_point \<Rightarrow> bool"
where
  "slp_left_branch_radius_chain_finite R pos neg origin terminal \<longleftrightarrow>
    slp_left_branch_radius_chain R origin
      (slp_finite_branch_pair_list pos neg) terminal"

lemma slp_left_branch_complex_kernel_finite_terminal_measurable:
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_measurable[measurable]:
      "terminal_value \<in> borel_measurable lborel"
  shows
    "slp_left_branch_complex_kernel_finite cutoff potential terminal_value
        (pos :: 'i::finite \<Rightarrow> slp_point) neg origin
      \<in> borel_measurable lborel"
  unfolding slp_left_branch_complex_kernel_finite_def
  by (rule slp_left_branch_complex_kernel_list_measurable[
        OF cutoff_measurable potential_measurable terminal_measurable])

theorem slp_left_branch_complex_kernel_finite_positive_weight:
  assumes chain:
    "slp_left_branch_radius_chain_finite R
      (pos :: 'i::finite \<Rightarrow> slp_point) neg origin terminal"
  shows
    "ennreal (norm (slp_left_branch_complex_kernel_finite cutoff potential
        terminal_value pos neg origin terminal)) =
      slp_left_branch_positive_kernel_finite R cutoff potential terminal_value
        pos neg origin terminal"
proof -
  have list_chain:
      "slp_left_branch_radius_chain R origin
        (slp_finite_branch_pair_list pos neg) terminal"
    using chain
    unfolding slp_left_branch_radius_chain_finite_def .
  show ?thesis
    unfolding slp_left_branch_complex_kernel_finite_def
      slp_left_branch_positive_kernel_finite_def
    by (rule slp_left_branch_complex_kernel_list_positive_weight[OF
          list_chain])
qed

end
