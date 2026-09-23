theory Inverse_Schrodinger_Lp_Right_Graph_Natural_Finite_Integral
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Right_Graph_Natural_Finite_Pointwise"
begin

section \<open>Fixed-root natural-to-finite right graph integration\<close>

theorem slp_right_branch_graph_natural_finite_compose:
  fixes branch_dummy :: "'i::finite itself"
  shows
    "(\<lambda>coordinates ::
        (((nat \<Rightarrow> slp_point) \<times> (nat \<Rightarrow> slp_point))
          \<times> slp_point).
        slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau center
          cutoff potential terminal_value origin
          (((\<chi> i::'i.
              fst (fst coordinates) (to_nat_on UNIV i)),
            (\<chi> i::'i.
              snd (fst coordinates) (to_nat_on UNIV i))),
            snd coordinates)) =
      slp_right_branch_oscillatory_graph_kernel_natural CARD('i) tau center
        cutoff potential terminal_value origin"
proof (rule ext)
  fix coordinates ::
    "((nat \<Rightarrow> slp_point) \<times> (nat \<Rightarrow> slp_point))
      \<times> slp_point"
  obtain families terminal where coordinates:
      "coordinates = (families, terminal)"
    by (cases coordinates)
  obtain positive negative where families:
      "families = (positive, negative)"
    by (cases families)
  show
    "slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau center
        cutoff potential terminal_value origin
        (((\<chi> i::'i.
            fst (fst coordinates) (to_nat_on UNIV i)),
          (\<chi> i::'i.
            snd (fst coordinates) (to_nat_on UNIV i))),
          snd coordinates) =
      slp_right_branch_oscillatory_graph_kernel_natural CARD('i) tau center
        cutoff potential terminal_value origin coordinates"
    unfolding coordinates families
    apply (simp only: fst_conv snd_conv)
    apply (rule
      slp_right_branch_oscillatory_graph_kernel_natural_to_finite_pointwise[
        where 'i = 'i, symmetric])
    done
qed

theorem slp_right_branch_oscillatory_graph_kernel_fixed_root_finite_measurable:
  fixes branch_dummy :: "'i::finite itself"
  assumes cutoff_measurable:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable:
      "potential \<in> borel_measurable lborel"
    and terminal_value_measurable:
      "terminal_value \<in> borel_measurable lborel"
  shows
    "slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau center
        cutoff potential terminal_value origin \<in>
      borel_measurable
        (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times>
          slp_point) measure)"
proof -
  have cnj_borel_measurable: "cnj \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF
          continuous_on_cnj[OF continuous_on_id]])
  have cutoff_cnj:
      "(\<lambda>x. cnj (cutoff x)) \<in> borel_measurable lborel"
    using measurable_comp[OF cutoff_measurable cnj_borel_measurable]
    by (simp add: comp_def)
  have potential_cnj:
      "(\<lambda>x. cnj (potential x)) \<in> borel_measurable lborel"
    using measurable_comp[OF potential_measurable cnj_borel_measurable]
    by (simp add: comp_def)
  have terminal_cnj:
      "(\<lambda>x. cnj (terminal_value x)) \<in> borel_measurable lborel"
    using measurable_comp[OF terminal_value_measurable cnj_borel_measurable]
    by (simp add: comp_def)
  have left_measurable:
      "slp_left_branch_oscillatory_graph_kernel_fixed_root_finite (- tau)
          center (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (potential x))
          (\<lambda>x. cnj (terminal_value x)) origin \<in>
        borel_measurable
          (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times>
            slp_point) measure)"
    by (rule
      slp_left_branch_oscillatory_graph_kernel_fixed_root_finite_measurable[
        OF cutoff_cnj potential_cnj terminal_cnj])
  show ?thesis
    unfolding slp_right_branch_oscillatory_graph_kernel_fixed_root_finite_def
    using measurable_comp[OF left_measurable cnj_borel_measurable]
    by (simp add: comp_def)
qed

theorem slp_right_branch_graph_natural_finite_integrable_iff:
  fixes branch_dummy :: "'i::finite itself"
  assumes cutoff_measurable:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable:
      "potential \<in> borel_measurable lborel"
    and terminal_value_measurable:
      "terminal_value \<in> borel_measurable lborel"
  shows
    "integrable
        (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times>
          slp_point) measure)
        (slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau center
          cutoff potential terminal_value origin) \<longleftrightarrow>
      integrable
        (((PiM {..<CARD('i)}
            (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
          (PiM {..<CARD('i)}
            (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M
          (lborel :: slp_point measure))
        (slp_right_branch_oscillatory_graph_kernel_natural CARD('i) tau center
          cutoff potential terminal_value origin)"
proof -
  let ?F =
    "slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau center
      cutoff potential terminal_value origin ::
        (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point)
          \<Rightarrow> complex"
  let ?G =
    "slp_right_branch_oscillatory_graph_kernel_natural CARD('i) tau center
      cutoff potential terminal_value origin"
  let ?T = "\<lambda>coordinates.
    (((\<chi> i::'i. fst (fst coordinates) (to_nat_on UNIV i)),
      (\<chi> i::'i. snd (fst coordinates) (to_nat_on UNIV i))),
      snd coordinates)"
  have F_measurable: "?F \<in> borel_measurable lborel"
    by (rule
      slp_right_branch_oscillatory_graph_kernel_fixed_root_finite_measurable[
        OF cutoff_measurable potential_measurable
          terminal_value_measurable])
  have composed: "(\<lambda>coordinates. ?F (?T coordinates)) = ?G"
    by (rule slp_right_branch_graph_natural_finite_compose)
  have transported:
      "integrable
          (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times>
            slp_point) measure) ?F \<longleftrightarrow>
        integrable
          (((PiM {..<CARD('i)}
              (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
            (PiM {..<CARD('i)}
              (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M
            (lborel :: slp_point measure))
          (\<lambda>coordinates. ?F (?T coordinates))"
    by (rule
      slp_integrable_left_branch_natural_to_finite_coordinates[
        OF F_measurable])
  show ?thesis
    using transported by (simp only: composed)
qed

theorem slp_right_branch_graph_natural_finite_integral:
  fixes branch_dummy :: "'i::finite itself"
  assumes cutoff_measurable:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable:
      "potential \<in> borel_measurable lborel"
    and terminal_value_measurable:
      "terminal_value \<in> borel_measurable lborel"
  shows
    "integral\<^sup>L
        (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times>
          slp_point) measure)
        (slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau center
          cutoff potential terminal_value origin) =
      integral\<^sup>L
        (((PiM {..<CARD('i)}
            (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
          (PiM {..<CARD('i)}
            (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M
          (lborel :: slp_point measure))
        (slp_right_branch_oscillatory_graph_kernel_natural CARD('i) tau center
          cutoff potential terminal_value origin)"
proof -
  let ?F =
    "slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau center
      cutoff potential terminal_value origin ::
        (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point)
          \<Rightarrow> complex"
  let ?G =
    "slp_right_branch_oscillatory_graph_kernel_natural CARD('i) tau center
      cutoff potential terminal_value origin"
  let ?T = "\<lambda>coordinates.
    (((\<chi> i::'i. fst (fst coordinates) (to_nat_on UNIV i)),
      (\<chi> i::'i. snd (fst coordinates) (to_nat_on UNIV i))),
      snd coordinates)"
  have F_measurable: "?F \<in> borel_measurable lborel"
    by (rule
      slp_right_branch_oscillatory_graph_kernel_fixed_root_finite_measurable[
        OF cutoff_measurable potential_measurable
          terminal_value_measurable])
  have composed: "(\<lambda>coordinates. ?F (?T coordinates)) = ?G"
    by (rule slp_right_branch_graph_natural_finite_compose)
  have transported:
      "integral\<^sup>L
          (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times>
            slp_point) measure) ?F =
        integral\<^sup>L
          (((PiM {..<CARD('i)}
              (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
            (PiM {..<CARD('i)}
              (\<lambda>_::nat. (lborel :: slp_point measure)))) \<Otimes>\<^sub>M
            (lborel :: slp_point measure))
          (\<lambda>coordinates. ?F (?T coordinates))"
    by (rule
      slp_integral_left_branch_natural_to_finite_coordinates[
        OF F_measurable])
  show ?thesis
    using transported by (simp only: composed)
qed

end
