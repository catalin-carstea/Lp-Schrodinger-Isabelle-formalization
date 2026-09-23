theory Inverse_Schrodinger_Lp_One_Sided_Finite_Principal_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_List_Residual_Decay"
begin

section \<open>The split positive-order principal left functional\<close>

definition slp_left_branch_principal_finite_functional ::
    "'i::finite itself \<Rightarrow> real \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow> complex"
where
  "slp_left_branch_principal_finite_functional dimension_type omega
      root_weight cutoff potential terminal_value test =
    integral\<^sup>L lborel
      (\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
        exp (\<i> * of_real
          (omega * slp_left_branch_residual
            (slp_finite_branch_pair_list
              (\<lambda>i. fst (fst (snd coordinates)) $ i)
              (\<lambda>i. snd (fst (snd coordinates)) $ i))
            (snd (snd coordinates)))) *
        slp_left_branch_complex_amplitude_finite root_weight cutoff potential
          terminal_value test coordinates) -
    integral\<^sup>L lborel
      (\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
        exp (\<i> * of_real
          (omega * slp_left_branch_residual
            (slp_finite_branch_pair_list
              (\<lambda>i. fst (fst (snd coordinates)) $ i)
              (\<lambda>i. snd (fst (snd coordinates)) $ i))
            (snd (snd coordinates)))) *
        slp_left_branch_complex_amplitude_finite root_weight cutoff potential
          (\<lambda>_. 1) (\<lambda>u. test u * terminal_value u) coordinates)"

theorem slp_left_branch_principal_finite_functional_decay:
  fixes branch_dummy :: "'i::finite itself"
  assumes stationary_phase:
      "hormander_quadratic_stationary_phase_decay_claim
        TYPE(('i + 'i) \<times> bool)"
    and density:
      "evans_compact_smooth_l1_density_claim TYPE(('i + 'i) \<times> bool)"
    and B_nonnegative: "0 \<le> B"
    and root_support: "\<And>x. root_weight x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and potential_support: "\<And>x. potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and root_weight_measurable[measurable]:
      "root_weight \<in> borel_measurable lborel"
    and cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_value_measurable[measurable]:
      "terminal_value \<in> borel_measurable lborel"
    and test_measurable[measurable]:
      "test \<in> borel_measurable lborel"
    and terminal_majorant_finite:
      "(\<integral>\<^sup>+ coordinates.
        case_prod (slp_left_branch_positive_amplitude_packed (2 * B)
          root_weight cutoff potential terminal_value test)
          coordinates \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
            (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) <
        \<infinity>"
    and output_majorant_finite:
      "(\<integral>\<^sup>+ coordinates.
        case_prod (slp_left_branch_positive_amplitude_packed (2 * B)
          root_weight cutoff potential (\<lambda>_. 1)
          (\<lambda>u. test u * terminal_value u))
          coordinates \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
            (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) <
        \<infinity>"
  shows
    "((\<lambda>omega. slp_left_branch_principal_finite_functional TYPE('i)
        omega root_weight cutoff potential terminal_value test)
      \<longlongrightarrow> 0) at_top"
proof -
  have terminal_decay:
      "((\<lambda>omega. integral\<^sup>L lborel
        (\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
          exp (\<i> * of_real
            (omega * slp_left_branch_residual
              (slp_finite_branch_pair_list
                (\<lambda>i. fst (fst (snd coordinates)) $ i)
                (\<lambda>i. snd (fst (snd coordinates)) $ i))
              (snd (snd coordinates)))) *
          slp_left_branch_complex_amplitude_finite root_weight cutoff potential
            terminal_value test coordinates))
        \<longlongrightarrow> 0) at_top"
    by (rule slp_left_branch_complex_amplitude_finite_list_residual_decay[
          where B = B, OF stationary_phase density B_nonnegative root_support
            cutoff_support potential_support root_weight_measurable
            cutoff_measurable potential_measurable terminal_value_measurable
            test_measurable terminal_majorant_finite])
  have output_decay:
      "((\<lambda>omega. integral\<^sup>L lborel
        (\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
          exp (\<i> * of_real
            (omega * slp_left_branch_residual
              (slp_finite_branch_pair_list
                (\<lambda>i. fst (fst (snd coordinates)) $ i)
                (\<lambda>i. snd (fst (snd coordinates)) $ i))
              (snd (snd coordinates)))) *
          slp_left_branch_complex_amplitude_finite root_weight cutoff potential
            (\<lambda>_. 1) (\<lambda>u. test u * terminal_value u)
            coordinates))
        \<longlongrightarrow> 0) at_top"
    by (rule slp_left_branch_complex_amplitude_finite_list_residual_decay[
          where B = B, OF stationary_phase density B_nonnegative root_support
            cutoff_support potential_support root_weight_measurable
            cutoff_measurable potential_measurable _ _ output_majorant_finite])
      measurable
  have difference_decay:
      "((\<lambda>omega. integral\<^sup>L lborel
          (\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
            exp (\<i> * of_real
              (omega * slp_left_branch_residual
                (slp_finite_branch_pair_list
                  (\<lambda>i. fst (fst (snd coordinates)) $ i)
                  (\<lambda>i. snd (fst (snd coordinates)) $ i))
                (snd (snd coordinates)))) *
            slp_left_branch_complex_amplitude_finite root_weight cutoff
              potential terminal_value test coordinates) -
        integral\<^sup>L lborel
          (\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
            exp (\<i> * of_real
              (omega * slp_left_branch_residual
                (slp_finite_branch_pair_list
                  (\<lambda>i. fst (fst (snd coordinates)) $ i)
                  (\<lambda>i. snd (fst (snd coordinates)) $ i))
                (snd (snd coordinates)))) *
            slp_left_branch_complex_amplitude_finite root_weight cutoff
              potential (\<lambda>_. 1)
              (\<lambda>u. test u * terminal_value u) coordinates))
        \<longlongrightarrow> 0 - 0) at_top"
    by (rule tendsto_diff[OF terminal_decay output_decay])
  show ?thesis
    unfolding slp_left_branch_principal_finite_functional_def
    using difference_decay by (simp only: diff_zero)
qed

end
