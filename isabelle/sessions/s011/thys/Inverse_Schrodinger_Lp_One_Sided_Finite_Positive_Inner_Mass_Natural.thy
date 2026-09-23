theory Inverse_Schrodinger_Lp_One_Sided_Finite_Positive_Inner_Mass_Natural
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Branch_Natural_NN_Integral"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_Positive_Inner_Mass"
begin

section \<open>Natural-coordinate expansion of the finite positive inner mass\<close>

theorem slp_left_branch_positive_inner_mass_finite_natural:
  fixes branch_dummy :: "'i::finite itself"
  assumes cutoff_measurable:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable:
      "potential \<in> borel_measurable lborel"
    and terminal_value_measurable:
      "terminal_value \<in> borel_measurable lborel"
    and output_factor_measurable:
      "output_factor \<in> borel_measurable lborel"
  shows
    "slp_left_branch_positive_inner_mass_finite TYPE('i) R cutoff potential
        terminal_value output_factor origin =
      (\<integral>\<^sup>+ pos_natural. \<integral>\<^sup>+ neg_natural.
        \<integral>\<^sup>+ terminal.
          slp_left_branch_positive_kernel_joint R cutoff potential
              terminal_value
              ((origin, (((\<chi> i. pos_natural (to_nat_on UNIV i)),
                (\<chi> j. neg_natural (to_nat_on UNIV j))), terminal)) ::
                  'i slp_left_branch_finite_coordinates) *
            ennreal (norm (output_factor
              (slp_one_sided_packed_output_point
                (snd (slp_one_sided_finite_to_packed_coordinates
                  ((origin, (((\<chi> i. pos_natural (to_nat_on UNIV i)),
                    (\<chi> j. neg_natural (to_nat_on UNIV j))), terminal)) ::
                      'i slp_left_branch_finite_coordinates))))))
          \<partial>lborel
        \<partial>(PiM {..<CARD('i)}
          (\<lambda>_::nat. (lborel :: slp_point measure)))
      \<partial>(PiM {..<CARD('i)}
        (\<lambda>_::nat. (lborel :: slp_point measure))))"
proof -
  let ?A =
    "(slp_left_branch_positive_amplitude_finite R
      (\<lambda>_::slp_point. 1) cutoff potential terminal_value output_factor ::
      'i slp_left_branch_finite_coordinates \<Rightarrow> ennreal)"
  let ?J =
    "\<lambda>coordinates::'i slp_left_branch_finite_coordinates.
      slp_left_branch_positive_kernel_joint R cutoff potential terminal_value
          coordinates *
        ennreal (norm (output_factor
          (slp_one_sided_packed_output_point
            (snd (slp_one_sided_finite_to_packed_coordinates coordinates)))))"
  have unit_root_measurable:
      "(\<lambda>_::slp_point. 1::complex) \<in> borel_measurable lborel"
    by measurable
  have A_measurable: "?A \<in> borel_measurable lborel"
    by (rule slp_left_branch_positive_amplitude_finite_measurable[OF
          unit_root_measurable cutoff_measurable potential_measurable
          terminal_value_measurable output_factor_measurable])
  have A_eq_J: "?A = ?J"
    by (rule ext)
      (simp only: slp_left_branch_positive_amplitude_finite_factors norm_one
        ennreal_1 mult_1_left)
  have J_measurable: "?J \<in> borel_measurable lborel"
    using A_measurable by (simp only: A_eq_J)
  have origin_in_space:
      "origin \<in> space (lborel :: slp_point measure)"
    by simp
  have origin_constant:
      "(\<lambda>_::((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
        origin) \<in> measurable lborel lborel"
    by (rule measurable_const[OF origin_in_space])
  have pair_product_measurable:
      "(\<lambda>branch_coordinates::
          ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
        (origin, branch_coordinates)) \<in>
        measurable lborel
          ((lborel :: slp_point measure) \<Otimes>\<^sub>M
            (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times>
              slp_point) measure))"
  proof -
    note raw = measurable_Pair[OF origin_constant measurable_ident]
    show ?thesis
      using raw by (simp only: id_def)
  qed
  have pair_measurable:
      "(\<lambda>branch_coordinates::
          ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
        (origin, branch_coordinates)) \<in> measurable lborel lborel"
    using pair_product_measurable by (simp only: lborel_prod)
  have fixed_root_measurable:
      "(\<lambda>branch_coordinates::
          ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
        ?J (origin, branch_coordinates)) \<in> borel_measurable lborel"
    using measurable_comp[OF pair_measurable J_measurable]
    by (simp only: comp_def)
  note expanded = slp_nn_integral_branch_natural_coordinates[
    where 'a = slp_point and 'b = slp_point and 'c = slp_point
      and 'i = 'i and 'j = 'i
      and F = "\<lambda>branch_coordinates. ?J (origin, branch_coordinates)",
    OF fixed_root_measurable]
  show ?thesis
    unfolding slp_left_branch_positive_inner_mass_finite_def
    apply (subst expanded)
    apply simp
    done
qed

end
