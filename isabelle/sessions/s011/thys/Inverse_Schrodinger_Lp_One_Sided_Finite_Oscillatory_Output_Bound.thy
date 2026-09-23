theory Inverse_Schrodinger_Lp_One_Sided_Finite_Oscillatory_Output_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Cauchy_Principal_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Packed_Unit_Terminal_Output_Pairing"
begin

section \<open>Finite oscillatory integrals controlled by output density\<close>

definition slp_left_branch_finite_oscillatory_integral ::
    "'i::finite itself \<Rightarrow> real \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow> complex"
where
  "slp_left_branch_finite_oscillatory_integral branch_dummy omega root_weight
      cutoff potential terminal_value output_factor =
    integral\<^sup>L lborel
      (\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
        exp (\<i> * of_real
          (omega * slp_one_sided_finite_residual coordinates)) *
        slp_left_branch_complex_amplitude_finite root_weight cutoff potential
          terminal_value output_factor coordinates)"

theorem slp_left_branch_finite_oscillatory_integral_unit_terminal_bound:
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
        (slp_left_branch_finite_oscillatory_integral TYPE('i) omega
          root_weight cutoff potential (\<lambda>_. 1) output_factor)) \<le>
      (\<integral>\<^sup>+ output.
        slp_left_one_sided_output_density (2 * B) cutoff potential
          (\<lambda>_ :: slp_point. 1 :: ennreal)
          CARD('i) root_weight output *
        ennreal (Real_Vector_Spaces.norm (output_factor output))
        \<partial>lborel)"
proof -
  let ?terminal = "\<lambda>_ :: slp_point. 1 :: complex"
  let ?terminal_weight = "\<lambda>_ :: slp_point. 1 :: ennreal"
  let ?amplitude =
    "slp_left_branch_complex_amplitude_finite root_weight cutoff potential
      ?terminal output_factor ::
        'i slp_left_branch_finite_coordinates \<Rightarrow> complex"
  let ?integrand = "\<lambda>(coordinates ::
      'i slp_left_branch_finite_coordinates).
    exp (\<i> * of_real
      (omega * slp_one_sided_finite_residual coordinates)) *
    ?amplitude coordinates"
  have terminal_measurable:
      "?terminal \<in> borel_measurable lborel"
    by measurable
  have amplitude_integrable: "integrable lborel ?amplitude"
    by (rule slp_left_branch_complex_amplitude_finite_integrable[
          where B = B, OF B_nonnegative root_support cutoff_support
            potential_support root_weight_measurable cutoff_measurable
            potential_measurable terminal_measurable
            output_factor_measurable majorant_finite])
  have branch_coordinates_lborel:
      "(\<lambda>x :: 'i slp_left_branch_finite_coordinates.
        snd (slp_one_sided_finite_to_packed_coordinates x))
        \<in> measurable lborel lborel"
    using measurable_compose[
      OF slp_one_sided_finite_to_packed_coordinates_measurable measurable_snd]
    by (simp only: comp_def)
  have finite_residual_measurable:
      "(slp_one_sided_finite_residual ::
        'i slp_left_branch_finite_coordinates \<Rightarrow> real)
        \<in> borel_measurable lborel"
    unfolding slp_one_sided_finite_residual_def
    using measurable_compose[
      OF branch_coordinates_lborel slp_one_sided_packed_residual_measurable]
    by (simp only: comp_def)
  have scaled_residual_measurable:
      "(\<lambda>coordinates :: 'i slp_left_branch_finite_coordinates.
        omega * slp_one_sided_finite_residual coordinates)
        \<in> borel_measurable lborel"
    using finite_residual_measurable by measurable
  have integrand_integrable: "integrable lborel ?integrand"
    by (rule slp_unit_modulus_real_phase_integrable[
          OF amplitude_integrable scaled_residual_measurable])
  have integral_bound:
      "ennreal (Real_Vector_Spaces.norm (integral\<^sup>L lborel ?integrand)) \<le>
        (\<integral>\<^sup>+ coordinates.
          Real_Vector_Spaces.norm (?integrand coordinates)
          \<partial>lborel)"
    using Bochner_Integration.integral_norm_bound_ennreal[OF
      integrand_integrable] .
  have amplitude_le:
      "ennreal (Real_Vector_Spaces.norm (?amplitude coordinates)) \<le>
        slp_left_branch_positive_amplitude_finite (2 * B) root_weight cutoff
          potential ?terminal output_factor coordinates"
    for coordinates
  proof -
    note packed_le = slp_left_branch_complex_amplitude_packed_le_positive[
      where B = B and root_weight = root_weight and cutoff = cutoff
        and potential = potential and terminal_value = ?terminal
        and output_factor = output_factor
        and root_coord =
          "fst (slp_one_sided_finite_to_packed_coordinates coordinates)"
        and branch_coord =
          "snd (slp_one_sided_finite_to_packed_coordinates coordinates)",
      OF B_nonnegative root_support cutoff_support potential_support]
    have packed_le_unconditional:
        "ennreal (Real_Vector_Spaces.norm (?amplitude coordinates)) \<le>
          slp_left_branch_positive_amplitude_packed (2 * B) root_weight
            cutoff potential ?terminal output_factor
            (fst (slp_one_sided_finite_to_packed_coordinates coordinates))
            (snd (slp_one_sided_finite_to_packed_coordinates coordinates))"
      using packed_le
      by (simp add: slp_left_branch_complex_amplitude_packed_finite)
    show ?thesis
      using packed_le_unconditional
      unfolding slp_left_branch_positive_amplitude_finite_def
      by (simp only: case_prod_unfold)
  qed
  have positive_bound:
      "(\<integral>\<^sup>+ coordinates.
          Real_Vector_Spaces.norm (?integrand coordinates)
          \<partial>lborel) \<le>
        (\<integral>\<^sup>+ coordinates.
          slp_left_branch_positive_amplitude_finite (2 * B) root_weight
            cutoff potential ?terminal output_factor coordinates
          \<partial>(lborel ::
            ('i slp_left_branch_finite_coordinates) measure))"
  proof (rule nn_integral_mono)
    fix coordinates
    show "ennreal (Real_Vector_Spaces.norm (?integrand coordinates)) \<le>
        slp_left_branch_positive_amplitude_finite (2 * B) root_weight cutoff
          potential ?terminal output_factor coordinates"
      using amplitude_le[of coordinates]
      by (simp add: norm_mult)
  qed
  have finite_to_output:
      "(\<integral>\<^sup>+ coordinates.
          slp_left_branch_positive_amplitude_finite (2 * B) root_weight
            cutoff potential ?terminal output_factor coordinates
          \<partial>(lborel ::
            ('i slp_left_branch_finite_coordinates) measure)) =
        (\<integral>\<^sup>+ output.
          slp_left_one_sided_output_density (2 * B) cutoff potential
            ?terminal_weight CARD('i) root_weight output *
          ennreal (Real_Vector_Spaces.norm (output_factor output))
          \<partial>lborel)"
  proof -
    note transport = slp_left_branch_positive_amplitude_integral_transport[
      where 'i = 'i and R = "2 * B" and root_weight = root_weight
        and cutoff = cutoff and potential = potential
        and terminal_value = ?terminal and output_factor = output_factor,
      OF root_weight_measurable cutoff_measurable potential_measurable
        terminal_measurable output_factor_measurable]
    note pairing =
      slp_left_branch_positive_amplitude_packed_unit_terminal_pairing[
        where 'i = 'i and R = "2 * B" and root_weight = root_weight
          and cutoff = cutoff and potential = potential
          and output_factor = output_factor,
        OF root_weight_measurable cutoff_measurable potential_measurable
          output_factor_measurable]
    show ?thesis
      using transport pairing by simp
  qed
  have total_bound:
      "ennreal (Real_Vector_Spaces.norm (integral\<^sup>L lborel ?integrand)) \<le>
        (\<integral>\<^sup>+ output.
          slp_left_one_sided_output_density (2 * B) cutoff potential
            ?terminal_weight CARD('i) root_weight output *
          ennreal (Real_Vector_Spaces.norm (output_factor output))
          \<partial>lborel)"
    using order_trans[OF integral_bound positive_bound] finite_to_output
    by simp
  show ?thesis
    using total_bound
    unfolding slp_left_branch_finite_oscillatory_integral_def
    by simp
qed

end
