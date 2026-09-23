theory Inverse_Schrodinger_Lp_Born_Left_Complex_Kernel_List
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Left_Complex_Terminal"
begin

section \<open>Exact finite-list complex left-branch kernel\<close>

primrec slp_left_branch_complex_kernel_list ::
    "(slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<times> slp_point) list \<Rightarrow>
      slp_point \<Rightarrow> slp_point \<Rightarrow> complex"
where
  "slp_left_branch_complex_kernel_list cutoff potential terminal_value []
      origin terminal =
    slp_left_branch_complex_terminal cutoff terminal_value origin terminal"
| "slp_left_branch_complex_kernel_list cutoff potential terminal_value
      (pair # pairs) origin terminal =
    inverse (of_real (pi ^ 2)) *
    slp_left_branch_complex_block cutoff potential origin (fst pair)
      (snd pair) *
    slp_left_branch_complex_kernel_list cutoff potential terminal_value pairs
      (snd pair) terminal"

primrec slp_left_branch_positive_kernel_list ::
    "real \<Rightarrow> (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<times> slp_point) list \<Rightarrow>
      slp_point \<Rightarrow> slp_point \<Rightarrow> ennreal"
where
  "slp_left_branch_positive_kernel_list R cutoff potential terminal_value []
      origin terminal =
    ennreal (inverse pi) *
    ennreal (slp_localized_cauchy_kernel R (origin - terminal)) *
    ennreal (norm (cutoff terminal)) *
    ennreal (norm (terminal_value terminal))"
| "slp_left_branch_positive_kernel_list R cutoff potential terminal_value
      (pair # pairs) origin terminal =
    ennreal (inverse (pi ^ 2)) *
    slp_positive_branch_block_weight R cutoff potential origin (fst pair)
      (snd pair) *
    slp_left_branch_positive_kernel_list R cutoff potential terminal_value
      pairs (snd pair) terminal"

primrec slp_left_branch_radius_chain ::
    "real \<Rightarrow> slp_point \<Rightarrow>
      (slp_point \<times> slp_point) list \<Rightarrow> slp_point \<Rightarrow> bool"
where
  "slp_left_branch_radius_chain R origin [] terminal \<longleftrightarrow>
    norm (origin - terminal) \<le> R"
| "slp_left_branch_radius_chain R origin (pair # pairs) terminal \<longleftrightarrow>
    norm (origin - fst pair) \<le> R \<and>
    norm (fst pair - snd pair) \<le> R \<and>
    slp_left_branch_radius_chain R (snd pair) pairs terminal"

lemma slp_left_branch_complex_kernel_list_measurable:
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_measurable[measurable]:
      "terminal_value \<in> borel_measurable lborel"
  shows
    "slp_left_branch_complex_kernel_list cutoff potential terminal_value pairs
      origin \<in> borel_measurable lborel"
proof (induction pairs arbitrary: origin)
  case Nil
  show ?case
    unfolding slp_left_branch_complex_kernel_list.simps
    by (rule slp_left_branch_complex_terminal_measurable[OF
          cutoff_measurable terminal_measurable])
next
  case (Cons pair pairs)
  have tail_measurable[measurable]:
      "slp_left_branch_complex_kernel_list cutoff potential terminal_value
        pairs (snd pair) \<in> borel_measurable lborel"
    by (rule Cons.IH)
  show ?case
    unfolding slp_left_branch_complex_kernel_list.simps
    by measurable
qed

lemma slp_left_branch_complex_step_positive_weight:
  assumes origin_pos_radius: "norm (origin - pos_point) \<le> R"
    and pos_neg_radius: "norm (pos_point - neg_point) \<le> R"
  shows
    "ennreal (norm (inverse (of_real (pi ^ 2)) *
        slp_left_branch_complex_block cutoff potential origin pos_point
          neg_point)) =
      ennreal (inverse (pi ^ 2)) *
      slp_positive_branch_block_weight R cutoff potential origin pos_point
        neg_point"
proof -
  have pi_sq_pos: "(0 :: real) < pi ^ 2"
    by (rule zero_less_power[OF pi_gt_zero])
  have coefficient_norm:
      "norm (inverse (of_real (pi ^ 2) :: complex)) = inverse (pi ^ 2)"
    by (simp add: norm_inverse norm_power norm_of_real abs_of_pos pi_sq_pos
        pi_gt_zero)
  have block:
      "ennreal (norm (slp_left_branch_complex_block cutoff potential origin
          pos_point neg_point)) =
        slp_positive_branch_block_weight R cutoff potential origin pos_point
          neg_point"
    by (rule slp_left_branch_complex_block_positive_weight[OF
          origin_pos_radius pos_neg_radius])
  have coefficient_nonneg: "(0 :: real) \<le> inverse (pi ^ 2)"
    using pi_sq_pos by simp
  show ?thesis
    apply (subst norm_mult)
    apply (subst coefficient_norm)
    apply (subst ennreal_mult)
      apply (rule coefficient_nonneg)
     apply (rule norm_ge_zero)
    apply (subst block)
    apply (rule refl)
    done
qed

theorem slp_left_branch_complex_kernel_list_positive_weight:
  assumes chain:
    "slp_left_branch_radius_chain R origin pairs terminal"
  shows
    "ennreal (norm (slp_left_branch_complex_kernel_list cutoff potential
        terminal_value pairs origin terminal)) =
      slp_left_branch_positive_kernel_list R cutoff potential terminal_value
        pairs origin terminal"
  using chain
proof (induction pairs arbitrary: origin)
  case Nil
  then show ?case
    using slp_left_branch_complex_terminal_positive_weight
    by simp
next
  case (Cons pair pairs)
  obtain pos_point neg_point where pair:
      "pair = (pos_point, neg_point)"
    by (cases pair)
  from Cons.prems have origin_pos_radius:
      "norm (origin - pos_point) \<le> R"
    and pos_neg_radius: "norm (pos_point - neg_point) \<le> R"
    and tail_chain:
      "slp_left_branch_radius_chain R neg_point pairs terminal"
    unfolding pair by simp_all
  have step:
      "ennreal (norm (inverse (of_real (pi ^ 2)) *
          slp_left_branch_complex_block cutoff potential origin pos_point
            neg_point)) =
        ennreal (inverse (pi ^ 2)) *
        slp_positive_branch_block_weight R cutoff potential origin pos_point
          neg_point"
    by (rule slp_left_branch_complex_step_positive_weight[OF
          origin_pos_radius pos_neg_radius])
  have tail:
      "ennreal (norm (slp_left_branch_complex_kernel_list cutoff potential
          terminal_value pairs neg_point terminal)) =
        slp_left_branch_positive_kernel_list R cutoff potential terminal_value
          pairs neg_point terminal"
    by (rule Cons.IH[OF tail_chain])
  have exact_product:
      "ennreal (norm (
          (inverse (of_real (pi ^ 2)) *
            slp_left_branch_complex_block cutoff potential origin pos_point
              neg_point) *
          slp_left_branch_complex_kernel_list cutoff potential terminal_value
            pairs neg_point terminal)) =
        ennreal (inverse (pi ^ 2)) *
          slp_positive_branch_block_weight R cutoff potential origin pos_point
            neg_point *
        slp_left_branch_positive_kernel_list R cutoff potential
          terminal_value pairs neg_point terminal"
  proof -
    have norm_split:
        "ennreal (norm (
          (inverse (of_real (pi ^ 2)) *
            slp_left_branch_complex_block cutoff potential origin pos_point
              neg_point) *
          slp_left_branch_complex_kernel_list cutoff potential terminal_value
            pairs neg_point terminal)) =
        ennreal (norm (inverse (of_real (pi ^ 2)) *
          slp_left_branch_complex_block cutoff potential origin pos_point
            neg_point)) *
        ennreal (norm (slp_left_branch_complex_kernel_list cutoff potential
          terminal_value pairs neg_point terminal))"
      apply (subst norm_mult)
      apply (rule ennreal_mult)
       apply (rule norm_ge_zero)
      apply (rule norm_ge_zero)
      done
    have substitute_weights:
        "ennreal (norm (inverse (of_real (pi ^ 2)) *
            slp_left_branch_complex_block cutoff potential origin pos_point
              neg_point)) *
          ennreal (norm (slp_left_branch_complex_kernel_list cutoff potential
            terminal_value pairs neg_point terminal)) =
        (ennreal (inverse (pi ^ 2)) *
          slp_positive_branch_block_weight R cutoff potential origin pos_point
            neg_point) *
        slp_left_branch_positive_kernel_list R cutoff potential terminal_value
          pairs neg_point terminal"
      by (simp only: step tail)
    show ?thesis
      by (rule trans[OF norm_split substitute_weights])
  qed
  show ?case
    unfolding pair slp_left_branch_complex_kernel_list.simps
      slp_left_branch_positive_kernel_list.simps
    by (simp only: fst_conv snd_conv; rule exact_product)
qed

end
