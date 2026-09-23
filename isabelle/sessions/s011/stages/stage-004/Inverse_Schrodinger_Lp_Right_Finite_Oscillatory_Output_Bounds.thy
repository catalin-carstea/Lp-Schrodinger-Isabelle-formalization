theory Inverse_Schrodinger_Lp_Right_Finite_Oscillatory_Output_Bounds
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Positive_Born_Conjugation_Invariance"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_Oscillatory_Terminal_Bound"
begin

section \<open>Finite right oscillatory integrals controlled by output density\<close>

lemma slp_left_branch_positive_amplitude_packed_conjugate_unit_terminal:
  fixes branch_coord :: "real^((unit + ('i::finite + 'i)) \<times> bool)"
  shows
    "slp_left_branch_positive_amplitude_packed R
        (\<lambda>x. cnj (root_weight x)) (\<lambda>x. cnj (cutoff x))
        (\<lambda>x. cnj (potential x)) (\<lambda>_. 1)
        (\<lambda>x. cnj (output_factor x)) root_coord branch_coord =
      slp_left_branch_positive_amplitude_packed R root_weight cutoff potential
        (\<lambda>_. 1) output_factor root_coord branch_coord"
  using slp_left_branch_positive_amplitude_packed_conjugate[
    where R = R and root_weight = root_weight and cutoff = cutoff
      and potential = potential
      and terminal_value = "\<lambda>_ :: slp_point. 1 :: complex"
      and output_factor = output_factor and root_coord = root_coord
      and branch_coord = branch_coord]
  by simp

theorem slp_right_branch_finite_oscillatory_integral_unit_terminal_bound:
  fixes branch_dummy :: "'i::finite itself"
  assumes B_nonnegative: "0 \<le> B"
    and root_support:
      "\<And>x :: slp_point. root_weight x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and cutoff_support:
      "\<And>x :: slp_point. cutoff x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and potential_support:
      "\<And>x :: slp_point. potential x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
    and output_factor_measurable:
      "output_factor \<in> borel_measurable lborel"
    and majorant_finite:
      "(\<integral>\<^sup>+ coordinates.
        case_prod (slp_left_branch_positive_amplitude_packed (2 * B)
          root_weight cutoff potential (\<lambda>_. 1) output_factor)
          coordinates \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
            (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) <
        \<infinity>"
  shows
    "ennreal (Real_Vector_Spaces.norm
        (slp_right_branch_finite_oscillatory_integral TYPE('i) omega
          root_weight cutoff potential (\<lambda>_. 1) output_factor)) \<le>
      (\<integral>\<^sup>+ target.
        slp_right_one_sided_output_density (2 * B) cutoff potential
          (\<lambda>_ :: slp_point. 1 :: ennreal)
          CARD('i) root_weight target *
        ennreal (Real_Vector_Spaces.norm (output_factor target))
        \<partial>lborel)"
proof -
  have cnj_borel_measurable: "cnj \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF
          continuous_on_cnj[OF continuous_on_id]])
  have conjugate_root_support:
      "\<And>x :: slp_point. cnj (root_weight x) \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    using root_support by simp
  have conjugate_cutoff_support:
      "\<And>x :: slp_point. cnj (cutoff x) \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    using cutoff_support by simp
  have conjugate_potential_support:
      "\<And>x :: slp_point. cnj (potential x) \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    using potential_support by simp
  have conjugate_root_measurable:
      "(\<lambda>x. cnj (root_weight x)) \<in> borel_measurable lborel"
    using measurable_comp[OF root_weight_measurable cnj_borel_measurable]
    by (simp add: comp_def)
  have conjugate_cutoff_measurable:
      "(\<lambda>x. cnj (cutoff x)) \<in> borel_measurable lborel"
    using measurable_comp[OF cutoff_measurable cnj_borel_measurable]
    by (simp add: comp_def)
  have conjugate_potential_measurable:
      "(\<lambda>x. cnj (potential x)) \<in> borel_measurable lborel"
    using measurable_comp[OF potential_measurable cnj_borel_measurable]
    by (simp add: comp_def)
  have conjugate_output_measurable:
      "(\<lambda>x. cnj (output_factor x)) \<in> borel_measurable lborel"
    using measurable_comp[OF output_factor_measurable cnj_borel_measurable]
    by (simp add: comp_def)
  have positive_case_prod:
      "case_prod (slp_left_branch_positive_amplitude_packed (2 * B)
          (\<lambda>x. cnj (root_weight x)) (\<lambda>x. cnj (cutoff x))
          (\<lambda>x. cnj (potential x)) (\<lambda>_. 1)
          (\<lambda>x. cnj (output_factor x))) =
        case_prod (slp_left_branch_positive_amplitude_packed (2 * B)
          root_weight cutoff potential (\<lambda>_. 1) output_factor)"
    apply (rule ext)
    apply (case_tac x)
    apply (simp only: case_prod_unfold)
    by (rule
      slp_left_branch_positive_amplitude_packed_conjugate_unit_terminal)
  have conjugate_majorant:
      "(\<integral>\<^sup>+ coordinates.
        case_prod (slp_left_branch_positive_amplitude_packed (2 * B)
          (\<lambda>x. cnj (root_weight x)) (\<lambda>x. cnj (cutoff x))
          (\<lambda>x. cnj (potential x)) (\<lambda>_. 1)
          (\<lambda>x. cnj (output_factor x))) coordinates
        \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
          (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) <
        \<infinity>"
    using majorant_finite by (simp only: positive_case_prod)
  note left_bound =
    slp_left_branch_finite_oscillatory_integral_unit_terminal_bound[
      where 'i = 'i and B = B and omega = "- omega"
        and root_weight = "\<lambda>x. cnj (root_weight x)"
        and cutoff = "\<lambda>x. cnj (cutoff x)"
        and potential = "\<lambda>x. cnj (potential x)"
        and output_factor = "\<lambda>x. cnj (output_factor x)",
      OF B_nonnegative conjugate_root_support conjugate_cutoff_support
        conjugate_potential_support conjugate_root_measurable
        conjugate_cutoff_measurable conjugate_potential_measurable
        conjugate_output_measurable conjugate_majorant]
  show ?thesis
    using left_bound
    unfolding slp_left_one_sided_output_density_def
      slp_right_one_sided_output_density_def
    by (simp add: slp_right_branch_finite_oscillatory_integral_norm
        slp_positive_root_output_density_conjugate)
qed

theorem slp_right_branch_finite_oscillatory_integral_terminal_bound:
  fixes branch_dummy :: "'i::finite itself"
  assumes B_nonnegative: "0 \<le> B"
    and root_support:
      "\<And>x :: slp_point. root_weight x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and cutoff_support:
      "\<And>x :: slp_point. cutoff x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and potential_support:
      "\<And>x :: slp_point. potential x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
    and terminal_value_measurable:
      "terminal_value \<in> borel_measurable lborel"
    and output_factor_measurable:
      "output_factor \<in> borel_measurable lborel"
    and majorant_finite:
      "(\<integral>\<^sup>+ coordinates.
        case_prod (slp_left_branch_positive_amplitude_packed (2 * B)
          root_weight cutoff potential terminal_value output_factor)
          coordinates \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
            (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) <
        \<infinity>"
  shows
    "ennreal (Real_Vector_Spaces.norm
        (slp_right_branch_finite_oscillatory_integral TYPE('i) omega
          root_weight cutoff potential terminal_value output_factor)) \<le>
      (\<integral>\<^sup>+ target.
        slp_right_one_sided_output_density (2 * B) cutoff potential
          (\<lambda>x. ennreal (Real_Vector_Spaces.norm (terminal_value x)))
          CARD('i) root_weight target *
        ennreal (Real_Vector_Spaces.norm (output_factor target))
        \<partial>lborel)"
proof -
  have cnj_borel_measurable: "cnj \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF
          continuous_on_cnj[OF continuous_on_id]])
  have conjugate_root_support:
      "\<And>x :: slp_point. cnj (root_weight x) \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    using root_support by simp
  have conjugate_cutoff_support:
      "\<And>x :: slp_point. cnj (cutoff x) \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    using cutoff_support by simp
  have conjugate_potential_support:
      "\<And>x :: slp_point. cnj (potential x) \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    using potential_support by simp
  have conjugate_root_measurable:
      "(\<lambda>x. cnj (root_weight x)) \<in> borel_measurable lborel"
    using measurable_comp[OF root_weight_measurable cnj_borel_measurable]
    by (simp add: comp_def)
  have conjugate_cutoff_measurable:
      "(\<lambda>x. cnj (cutoff x)) \<in> borel_measurable lborel"
    using measurable_comp[OF cutoff_measurable cnj_borel_measurable]
    by (simp add: comp_def)
  have conjugate_potential_measurable:
      "(\<lambda>x. cnj (potential x)) \<in> borel_measurable lborel"
    using measurable_comp[OF potential_measurable cnj_borel_measurable]
    by (simp add: comp_def)
  have conjugate_terminal_measurable:
      "(\<lambda>x. cnj (terminal_value x)) \<in> borel_measurable lborel"
    using measurable_comp[OF terminal_value_measurable cnj_borel_measurable]
    by (simp add: comp_def)
  have conjugate_output_measurable:
      "(\<lambda>x. cnj (output_factor x)) \<in> borel_measurable lborel"
    using measurable_comp[OF output_factor_measurable cnj_borel_measurable]
    by (simp add: comp_def)
  have positive_case_prod:
      "case_prod (slp_left_branch_positive_amplitude_packed (2 * B)
          (\<lambda>x. cnj (root_weight x)) (\<lambda>x. cnj (cutoff x))
          (\<lambda>x. cnj (potential x))
          (\<lambda>x. cnj (terminal_value x))
          (\<lambda>x. cnj (output_factor x))) =
        case_prod (slp_left_branch_positive_amplitude_packed (2 * B)
          root_weight cutoff potential terminal_value output_factor)"
    apply (rule ext)
    apply (case_tac x)
    apply (simp only: case_prod_unfold)
    by (rule slp_left_branch_positive_amplitude_packed_conjugate)
  have conjugate_majorant:
      "(\<integral>\<^sup>+ coordinates.
        case_prod (slp_left_branch_positive_amplitude_packed (2 * B)
          (\<lambda>x. cnj (root_weight x)) (\<lambda>x. cnj (cutoff x))
          (\<lambda>x. cnj (potential x))
          (\<lambda>x. cnj (terminal_value x))
          (\<lambda>x. cnj (output_factor x))) coordinates
        \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
          (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) <
        \<infinity>"
    using majorant_finite by (simp only: positive_case_prod)
  note left_bound =
    slp_left_branch_finite_oscillatory_integral_terminal_bound[
      where 'i = 'i and B = B and omega = "- omega"
        and root_weight = "\<lambda>x. cnj (root_weight x)"
        and cutoff = "\<lambda>x. cnj (cutoff x)"
        and potential = "\<lambda>x. cnj (potential x)"
        and terminal_value = "\<lambda>x. cnj (terminal_value x)"
        and output_factor = "\<lambda>x. cnj (output_factor x)",
      OF B_nonnegative conjugate_root_support conjugate_cutoff_support
        conjugate_potential_support conjugate_root_measurable
        conjugate_cutoff_measurable conjugate_potential_measurable
        conjugate_terminal_measurable conjugate_output_measurable
        conjugate_majorant]
  show ?thesis
    using left_bound
    unfolding slp_left_one_sided_output_density_def
      slp_right_one_sided_output_density_def
    by (simp add: slp_right_branch_finite_oscillatory_integral_norm
        slp_positive_root_output_density_conjugate)
qed

end
