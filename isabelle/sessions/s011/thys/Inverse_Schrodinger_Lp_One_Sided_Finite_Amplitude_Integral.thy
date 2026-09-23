theory Inverse_Schrodinger_Lp_One_Sided_Finite_Amplitude_Integral
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_Amplitude"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Left_Complex_Amplitude_Integrable"
begin

section \<open>Finite-coordinate integrability of the complete left amplitude\<close>

theorem slp_left_branch_complex_amplitude_finite_integrable:
  fixes branch_dummy :: "'i::finite itself"
  assumes B_nonnegative: "0 \<le> B"
    and root_support: "\<And>x. root_weight x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and potential_support: "\<And>x. potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
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
    "integrable lborel
      (slp_left_branch_complex_amplitude_finite root_weight cutoff potential
        terminal_value output_factor ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
proof -
  let ?packed =
    "(case_prod (slp_left_branch_complex_amplitude_packed root_weight cutoff
      potential terminal_value output_factor) ::
        (real^bool) \<times>
          (real^((unit + ('i + 'i)) \<times> bool)) \<Rightarrow> complex)"
  have packed_measurable: "?packed \<in> borel_measurable lborel"
    using slp_left_branch_complex_amplitude_packed_measurable[OF
      root_weight_measurable cutoff_measurable potential_measurable
      terminal_value_measurable output_factor_measurable]
    by (simp only: lborel_prod)
  have packed_integrable_product:
      "integrable ((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
        (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure)) ?packed"
    by (rule slp_left_branch_complex_amplitude_packed_integrable[
          where B = B, OF B_nonnegative root_support cutoff_support
          potential_support root_weight_measurable cutoff_measurable
          potential_measurable terminal_value_measurable
          output_factor_measurable majorant_finite])
  have packed_integrable: "integrable lborel ?packed"
    using packed_integrable_product
    by (simp only: lborel_prod)
  have pulled_integrable:
      "integrable lborel
        (\<lambda>x. ?packed (slp_one_sided_finite_to_packed_coordinates x))"
    using slp_one_sided_finite_packed_integrable_iff[OF packed_measurable]
      packed_integrable
    by blast
  have pullback:
      "(\<lambda>x. ?packed (slp_one_sided_finite_to_packed_coordinates x)) =
        slp_left_branch_complex_amplitude_finite root_weight cutoff potential
          terminal_value output_factor"
    by (rule ext)
      (simp only: case_prod_unfold
        slp_left_branch_complex_amplitude_packed_finite)
  show ?thesis
    using pulled_integrable by (simp only: pullback)
qed

theorem slp_left_branch_complex_amplitude_finite_integral:
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
    "integral\<^sup>L lborel
        (case_prod (slp_left_branch_complex_amplitude_packed root_weight cutoff
          potential terminal_value output_factor) ::
            (real^bool) \<times>
              (real^((unit + ('i + 'i)) \<times> bool)) \<Rightarrow> complex) =
      integral\<^sup>L lborel
        (slp_left_branch_complex_amplitude_finite root_weight cutoff potential
          terminal_value output_factor ::
            'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
proof -
  let ?packed =
    "(case_prod (slp_left_branch_complex_amplitude_packed root_weight cutoff
      potential terminal_value output_factor) ::
        (real^bool) \<times>
          (real^((unit + ('i + 'i)) \<times> bool)) \<Rightarrow> complex)"
  have packed_measurable: "?packed \<in> borel_measurable lborel"
    using slp_left_branch_complex_amplitude_packed_measurable[OF
      root_weight_measurable cutoff_measurable potential_measurable
      terminal_value_measurable output_factor_measurable]
    by (simp only: lborel_prod)
  have transported:
      "integral\<^sup>L lborel ?packed =
        integral\<^sup>L lborel
          (\<lambda>x. ?packed (slp_one_sided_finite_to_packed_coordinates x))"
    by (rule slp_one_sided_finite_packed_integral[OF packed_measurable])
  have pullback:
      "(\<lambda>x. ?packed (slp_one_sided_finite_to_packed_coordinates x)) =
        slp_left_branch_complex_amplitude_finite root_weight cutoff potential
          terminal_value output_factor"
    by (rule ext)
      (simp only: case_prod_unfold
        slp_left_branch_complex_amplitude_packed_finite)
  show ?thesis
    using transported by (simp only: pullback)
qed

end
