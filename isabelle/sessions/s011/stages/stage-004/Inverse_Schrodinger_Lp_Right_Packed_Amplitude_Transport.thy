theory Inverse_Schrodinger_Lp_Right_Packed_Amplitude_Transport
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Right_Born_Finite_Cancellation"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_Amplitude_Integral"
begin

section \<open>Exact direct right amplitude on the packed one-sided carrier\<close>

definition slp_right_branch_complex_amplitude_packed ::
    "(slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      real^bool \<Rightarrow>
      real^((unit + ('i::finite + 'i)) \<times> bool) \<Rightarrow> complex"
where
  "slp_right_branch_complex_amplitude_packed root_weight cutoff potential
      terminal_value output_factor root_coord branch_coord =
    cnj (slp_left_branch_complex_amplitude_packed
      (\<lambda>x. cnj (root_weight x)) (\<lambda>x. cnj (cutoff x))
      (\<lambda>x. cnj (potential x)) (\<lambda>x. cnj (terminal_value x))
      (\<lambda>x. cnj (output_factor x)) root_coord branch_coord)"

theorem slp_right_branch_complex_amplitude_packed_finite:
  fixes coordinates :: "'i::finite slp_left_branch_finite_coordinates"
  shows
    "slp_right_branch_complex_amplitude_packed root_weight cutoff potential
        terminal_value output_factor
        (fst (slp_one_sided_finite_to_packed_coordinates coordinates))
        (snd (slp_one_sided_finite_to_packed_coordinates coordinates)) =
      slp_right_branch_complex_amplitude_finite root_weight cutoff potential
        terminal_value output_factor coordinates"
  unfolding slp_right_branch_complex_amplitude_packed_def
  by (simp only: slp_left_branch_complex_amplitude_packed_finite
      slp_right_branch_complex_amplitude_finite_conjugate)

theorem slp_right_branch_complex_amplitude_packed_measurable:
  assumes root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
    and terminal_value_measurable:
      "terminal_value \<in> borel_measurable lborel"
    and output_factor_measurable:
      "output_factor \<in> borel_measurable lborel"
  shows
    "case_prod (slp_right_branch_complex_amplitude_packed root_weight cutoff
        potential terminal_value output_factor) \<in>
      borel_measurable ((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
        (lborel :: (real^((unit + ('i::finite + 'i)) \<times> bool)) measure))"
proof -
  have cnj_borel_measurable: "cnj \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF
          continuous_on_cnj[OF continuous_on_id]])
  have root_weight_cnj_measurable:
      "(\<lambda>x. cnj (root_weight x)) \<in> borel_measurable lborel"
    using measurable_comp[OF root_weight_measurable cnj_borel_measurable]
    by (simp add: comp_def)
  have cutoff_cnj_measurable:
      "(\<lambda>x. cnj (cutoff x)) \<in> borel_measurable lborel"
    using measurable_comp[OF cutoff_measurable cnj_borel_measurable]
    by (simp add: comp_def)
  have potential_cnj_measurable:
      "(\<lambda>x. cnj (potential x)) \<in> borel_measurable lborel"
    using measurable_comp[OF potential_measurable cnj_borel_measurable]
    by (simp add: comp_def)
  have terminal_value_cnj_measurable:
      "(\<lambda>x. cnj (terminal_value x)) \<in> borel_measurable lborel"
    using measurable_comp[OF terminal_value_measurable cnj_borel_measurable]
    by (simp add: comp_def)
  have output_factor_cnj_measurable:
      "(\<lambda>x. cnj (output_factor x)) \<in> borel_measurable lborel"
    using measurable_comp[OF output_factor_measurable cnj_borel_measurable]
    by (simp add: comp_def)
  let ?left =
    "case_prod (slp_left_branch_complex_amplitude_packed
      (\<lambda>x. cnj (root_weight x)) (\<lambda>x. cnj (cutoff x))
      (\<lambda>x. cnj (potential x)) (\<lambda>x. cnj (terminal_value x))
      (\<lambda>x. cnj (output_factor x))) ::
      ((real^bool) \<times>
        (real^((unit + ('i + 'i)) \<times> bool))) \<Rightarrow> complex"
  have left_measurable:
      "?left \<in> borel_measurable ((lborel :: (real^bool) measure)
        \<Otimes>\<^sub>M
          (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))"
    by (rule slp_left_branch_complex_amplitude_packed_measurable[OF
          root_weight_cnj_measurable cutoff_cnj_measurable
          potential_cnj_measurable terminal_value_cnj_measurable
          output_factor_cnj_measurable])
  have right_eq:
      "case_prod (slp_right_branch_complex_amplitude_packed root_weight cutoff
          potential terminal_value output_factor) =
        (\<lambda>coordinates. cnj (?left coordinates))"
    unfolding slp_right_branch_complex_amplitude_packed_def
    by (rule ext) (simp only: case_prod_unfold)
  show ?thesis
    unfolding right_eq
    using left_measurable cnj_borel_measurable by measurable
qed

theorem slp_right_branch_complex_amplitude_packed_integrable_iff_finite:
  fixes branch_dummy :: "'i::finite itself"
  assumes root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
    and terminal_value_measurable:
      "terminal_value \<in> borel_measurable lborel"
    and output_factor_measurable:
      "output_factor \<in> borel_measurable lborel"
  shows
    "integrable ((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
        (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))
        (case_prod (slp_right_branch_complex_amplitude_packed root_weight
          cutoff potential terminal_value output_factor)) \<longleftrightarrow>
      integrable lborel
        (slp_right_branch_complex_amplitude_finite root_weight cutoff potential
          terminal_value output_factor ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
proof -
  let ?packed =
    "case_prod (slp_right_branch_complex_amplitude_packed root_weight cutoff
      potential terminal_value output_factor) ::
      ((real^bool) \<times>
        (real^((unit + ('i + 'i)) \<times> bool))) \<Rightarrow> complex"
  have packed_measurable_product:
      "?packed \<in> borel_measurable ((lborel :: (real^bool) measure)
        \<Otimes>\<^sub>M
          (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))"
    by (rule slp_right_branch_complex_amplitude_packed_measurable[OF
          root_weight_measurable cutoff_measurable potential_measurable
          terminal_value_measurable output_factor_measurable])
  have packed_measurable: "?packed \<in> borel_measurable lborel"
    using packed_measurable_product by (simp only: lborel_prod)
  have pullback:
      "(\<lambda>coordinates. ?packed
          (slp_one_sided_finite_to_packed_coordinates coordinates)) =
        (slp_right_branch_complex_amplitude_finite root_weight cutoff potential
          terminal_value output_factor ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    by (rule ext)
      (simp only: case_prod_unfold
        slp_right_branch_complex_amplitude_packed_finite)
  note transported =
    slp_one_sided_finite_packed_integrable_iff[OF packed_measurable]
  show ?thesis
    using transported by (simp only: lborel_prod pullback)
qed

end
