theory Inverse_Schrodinger_Lp_Positive_Kernel_List_Functional_Induction
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Positive_Kernel_List_Functional_Zero"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Positive_Kernel_List_Functional_Suc_Integrated"
begin

section \<open>Positive list kernels as recursive branch functionals\<close>

theorem slp_left_branch_positive_kernel_list_integral_functional_distinct:
  fixes ks :: "nat list"
  assumes distinct_ks: "distinct ks"
    and cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_value_measurable[measurable]:
      "terminal_value \<in> borel_measurable lborel"
    and output_factor_measurable[measurable]:
      "output_factor \<in> borel_measurable lborel"
  shows
    "nn_integral
        (PiM (set ks) (\<lambda>_::nat. (lborel :: slp_point measure)))
        (\<lambda>pos. nn_integral
          (PiM (set ks) (\<lambda>_::nat. (lborel :: slp_point measure)))
          (\<lambda>neg. nn_integral lborel
            (\<lambda>terminal.
              slp_left_branch_positive_kernel_list R cutoff potential
                  terminal_value (map (\<lambda>k. (pos k, neg k)) ks)
                  origin terminal *
                ennreal (norm (output_factor
                  (slp_left_branch_output
                    (map (\<lambda>k. (pos k, neg k)) ks) terminal)))))) =
      slp_positive_branch_functional R cutoff potential
        (\<lambda>x. ennreal (norm (terminal_value x))) (length ks) origin
        (\<lambda>x. ennreal (norm (output_factor x)))"
  using distinct_ks output_factor_measurable
proof (induction ks arbitrary: origin output_factor)
  case Nil
  interpret product:
    product_sigma_finite
      "\<lambda>_::nat. (lborel :: slp_point measure)"
    by standard
  show ?case
    apply (simp only: list.set list.map list.size)
    apply (subst product.nn_integral_empty)
     apply simp
    apply (subst product.nn_integral_empty)
     apply simp
    by (rule slp_left_branch_positive_kernel_list_zero_functional)
next
  case (Cons k ks)
  interpret product:
    product_sigma_finite
      "\<lambda>_::nat. (lborel :: slp_point measure)"
    by standard
  have finite_tail: "finite (set ks)"
    by simp
  have head_not_tail: "k \<notin> set ks"
    using Cons.prems(1) by simp
  have tail_distinct: "distinct ks"
    using Cons.prems(1) by simp
  have output_factor_current[measurable]:
      "output_factor \<in> borel_measurable lborel"
    using Cons.prems(2) .
  let ?MI = "PiM (insert k (set ks))
    (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?MT = "PiM (set ks)
    (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?MF = "(?MI \<Otimes>\<^sub>M ?MI) \<Otimes>\<^sub>M
    (lborel :: slp_point measure)"
  have pos_projection:
      "(fst \<circ> fst) \<in> measurable ?MF ?MI"
  proof -
    have family_projection:
        "fst \<in> measurable ?MF (?MI \<Otimes>\<^sub>M ?MI)"
      by (rule measurable_fst)
    show ?thesis
      using measurable_compose[OF family_projection measurable_fst]
      by (simp only: comp_def)
  qed
  have neg_projection:
      "(snd \<circ> fst) \<in> measurable ?MF ?MI"
  proof -
    have family_projection:
        "fst \<in> measurable ?MF (?MI \<Otimes>\<^sub>M ?MI)"
      by (rule measurable_fst)
    show ?thesis
      using measurable_compose[OF family_projection measurable_snd]
      by (simp only: comp_def)
  qed
  have pos_coordinate:
      "\<And>j. j \<in> insert k (set ks) \<Longrightarrow>
        (\<lambda>((pos, neg), terminal). pos j) \<in> measurable ?MF lborel"
  proof -
    fix j
    assume j: "j \<in> insert k (set ks)"
    have component:
        "(\<lambda>pos. pos j) \<in> measurable ?MI lborel"
      by (rule measurable_component_singleton[OF j])
    show "(\<lambda>((pos, neg), terminal). pos j)
        \<in> measurable ?MF lborel"
      using measurable_compose[OF pos_projection component]
      by (simp only: comp_def split_beta')
  qed
  have neg_coordinate:
      "\<And>j. j \<in> insert k (set ks) \<Longrightarrow>
        (\<lambda>((pos, neg), terminal). neg j) \<in> measurable ?MF lborel"
  proof -
    fix j
    assume j: "j \<in> insert k (set ks)"
    have component:
        "(\<lambda>neg. neg j) \<in> measurable ?MI lborel"
      by (rule measurable_component_singleton[OF j])
    show "(\<lambda>((pos, neg), terminal). neg j)
        \<in> measurable ?MF lborel"
      using measurable_compose[OF neg_projection component]
      by (simp only: comp_def split_beta')
  qed
  have kernel_joint:
      "(\<lambda>((pos, neg), terminal).
        slp_left_branch_positive_kernel_list R cutoff potential terminal_value
          (map (\<lambda>j. (pos j, neg j)) (k # ks)) origin terminal)
        \<in> borel_measurable ?MF"
  proof -
    let ?pair_functions =
      "(map (\<lambda>j. \<lambda>((pos, neg), terminal). (pos j, neg j))
        (k # ks) ::
        ((((nat \<Rightarrow> slp_point) \<times> (nat \<Rightarrow> slp_point)) \<times>
            slp_point) \<Rightarrow> slp_point \<times> slp_point) list)"
    have pair_first:
        "\<And>pair. pair \<in> set ?pair_functions \<Longrightarrow>
          (\<lambda>x. fst (pair x)) \<in> measurable ?MF lborel"
    proof -
      fix pair
      assume "pair \<in> set ?pair_functions"
      then obtain j where j: "j \<in> insert k (set ks)"
        and pair:
          "pair = (\<lambda>((pos, neg), terminal). (pos j, neg j))"
        by auto
      show "(\<lambda>x. fst (pair x)) \<in> measurable ?MF lborel"
        unfolding pair
        using pos_coordinate[OF j]
        by (simp only: split_beta' fst_conv)
    qed
    have pair_second:
        "\<And>pair. pair \<in> set ?pair_functions \<Longrightarrow>
          (\<lambda>x. snd (pair x)) \<in> measurable ?MF lborel"
    proof -
      fix pair
      assume "pair \<in> set ?pair_functions"
      then obtain j where j: "j \<in> insert k (set ks)"
        and pair:
          "pair = (\<lambda>((pos, neg), terminal). (pos j, neg j))"
        by auto
      show "(\<lambda>x. snd (pair x)) \<in> measurable ?MF lborel"
        unfolding pair
        using neg_coordinate[OF j]
        by (simp only: split_beta' snd_conv)
    qed
    have origin_constant:
        "(\<lambda>_::((nat \<Rightarrow> slp_point) \<times>
            (nat \<Rightarrow> slp_point)) \<times> slp_point. origin)
          \<in> measurable ?MF lborel"
      by measurable
    have terminal_projection:
        "(\<lambda>((pos, neg), terminal). terminal)
          \<in> measurable ?MF lborel"
    proof -
      have raw:
          "snd \<in> measurable ?MF (lborel :: slp_point measure)"
        by (rule measurable_snd)
      show ?thesis
        using raw by (simp only: split_beta')
    qed
    note raw = slp_left_branch_positive_kernel_list_param_measurable[
      where M = ?MF and pair_functions = ?pair_functions
        and origin = "\<lambda>_. origin"
        and terminal = "\<lambda>((pos, neg), terminal). terminal",
      OF cutoff_measurable potential_measurable terminal_value_measurable
        origin_constant terminal_projection pair_first pair_second]
    show ?thesis
      using raw
      by (simp only: list.map map_map comp_def split_beta')
  qed
  have increment_sum_measurable:
      "\<And>js. set js \<subseteq> insert k (set ks) \<Longrightarrow>
        (\<lambda>((pos, neg), terminal).
          sum_list (map (\<lambda>j. pos j - neg j) js))
        \<in> borel_measurable ?MF"
  proof -
    fix js
    assume subset: "set js \<subseteq> insert k (set ks)"
    show "(\<lambda>((pos, neg), terminal).
        sum_list (map (\<lambda>j. pos j - neg j) js))
      \<in> borel_measurable ?MF"
      using subset
    proof (induction js)
      case Nil
      then show ?case
        by (simp only: list.map sum_list.Nil split_beta') measurable
    next
      case (Cons j js)
      have j: "j \<in> insert k (set ks)"
        using Cons.prems by simp
      have tail: "set js \<subseteq> insert k (set ks)"
        using Cons.prems by simp
      have pos_j[measurable]:
          "(\<lambda>((pos, neg), terminal). pos j)
            \<in> borel_measurable ?MF"
        using pos_coordinate[OF j]
        by (simp only: measurable_lborel1)
      have neg_j[measurable]:
          "(\<lambda>((pos, neg), terminal). neg j)
            \<in> borel_measurable ?MF"
        using neg_coordinate[OF j]
        by (simp only: measurable_lborel1)
      have tail_sum[measurable]:
          "(\<lambda>((pos, neg), terminal).
            sum_list (map (\<lambda>j. pos j - neg j) js))
            \<in> borel_measurable ?MF"
        by (rule Cons.IH[OF tail])
      have pos_j_raw[measurable]:
          "(\<lambda>x. fst (fst x) j) \<in> borel_measurable ?MF"
        using pos_j by (simp only: split_beta')
      have neg_j_raw[measurable]:
          "(\<lambda>x. snd (fst x) j) \<in> borel_measurable ?MF"
        using neg_j by (simp only: split_beta')
      have tail_sum_raw[measurable]:
          "(\<lambda>x. sum_list
            (map (\<lambda>j. fst (fst x) j - snd (fst x) j) js))
            \<in> borel_measurable ?MF"
        using tail_sum by (simp only: split_beta')
      show ?case
        by (simp only: list.map sum_list.Cons split_beta') measurable
    qed
  qed
  have output_joint:
      "(\<lambda>((pos, neg), terminal).
        output_factor
          (slp_left_branch_output
            (map (\<lambda>j. (pos j, neg j)) (k # ks)) terminal))
        \<in> borel_measurable ?MF"
  proof -
    have terminal_measurable[measurable]:
        "(\<lambda>((pos, neg), terminal). terminal)
          \<in> borel_measurable ?MF"
    proof -
      have raw:
          "snd \<in> measurable ?MF (lborel :: slp_point measure)"
        by (rule measurable_snd)
      show ?thesis
        using raw by (simp only: measurable_lborel1 split_beta')
    qed
    have sums[measurable]:
        "(\<lambda>((pos, neg), terminal).
          sum_list (map (\<lambda>j. pos j - neg j) (k # ks)))
          \<in> borel_measurable ?MF"
      by (rule increment_sum_measurable) simp
    have output_argument[measurable]:
        "(\<lambda>((pos, neg), terminal).
          terminal +
            sum_list (map (\<lambda>j. pos j - neg j) (k # ks)))
          \<in> borel_measurable ?MF"
    proof -
      have terminal_raw:
          "snd \<in> borel_measurable ?MF"
        using terminal_measurable by (simp only: split_beta')
      have sums_raw:
          "(\<lambda>x. sum_list (map
            (\<lambda>j. fst (fst x) j - snd (fst x) j) (k # ks)))
            \<in> borel_measurable ?MF"
        using sums by (simp only: split_beta')
      note raw = borel_measurable_add[OF terminal_raw sums_raw]
      show ?thesis
        using raw by (simp only: split_beta')
    qed
    note output_argument_lborel =
      output_argument[folded measurable_lborel1]
    note composed = measurable_comp[OF output_argument_lborel
      output_factor_current]
    have output_rewrite:
        "\<And>pos neg terminal.
          slp_left_branch_output
              (map (\<lambda>j. (pos j, neg j)) (k # ks)) terminal =
            terminal +
              sum_list (map (\<lambda>j. pos j - neg j) (k # ks))"
      unfolding slp_left_branch_output_def slp_branch_increment_def
      by (simp only: map_map comp_def fst_conv snd_conv)
    have output_function_eq:
        "(\<lambda>((pos, neg), terminal).
          output_factor
            (slp_left_branch_output
              (map (\<lambda>j. (pos j, neg j)) (k # ks)) terminal)) =
        output_factor \<circ>
          (\<lambda>((pos, neg), terminal).
            terminal +
              sum_list (map (\<lambda>j. pos j - neg j) (k # ks)))"
      by (rule ext;
          simp only: comp_apply split_beta' fst_conv snd_conv;
          rule arg_cong;
          rule output_rewrite)
    show ?thesis
      apply (subst output_function_eq)
      apply (rule measurable_comp)
       apply (rule output_argument_lborel)
      apply (rule output_factor_current)
      done
  qed
  have output_norm_joint:
      "(\<lambda>((pos, neg), terminal).
        norm (output_factor
          (slp_left_branch_output
            (map (\<lambda>j. (pos j, neg j)) (k # ks)) terminal)))
        \<in> borel_measurable ?MF"
    using measurable_compose[OF output_joint borel_measurable_norm]
    by (simp only: comp_def split_beta')
  have output_ennreal_joint:
      "(\<lambda>((pos, neg), terminal).
        ennreal (norm (output_factor
          (slp_left_branch_output
            (map (\<lambda>j. (pos j, neg j)) (k # ks)) terminal))))
        \<in> borel_measurable ?MF"
    using measurable_compose[OF output_norm_joint measurable_ennreal]
    by (simp only: comp_def split_beta')
  have joint_integrand:
      "(\<lambda>((pos, neg), terminal).
        slp_left_branch_positive_kernel_list R cutoff potential terminal_value
            (map (\<lambda>j. (pos j, neg j)) (k # ks)) origin terminal *
          ennreal (norm (output_factor
            (slp_left_branch_output
              (map (\<lambda>j. (pos j, neg j)) (k # ks)) terminal))))
        \<in> borel_measurable ?MF"
  proof -
    note raw = borel_measurable_times_ennreal[OF
      kernel_joint output_ennreal_joint]
    show ?thesis
      using raw by (simp only: split_beta')
  qed
  have terminal_integral_measurable:
      "(\<lambda>(pos, neg). nn_integral lborel
        (\<lambda>terminal.
          slp_left_branch_positive_kernel_list R cutoff potential
              terminal_value (map (\<lambda>j. (pos j, neg j)) (k # ks))
              origin terminal *
            ennreal (norm (output_factor
              (slp_left_branch_output
                (map (\<lambda>j. (pos j, neg j)) (k # ks)) terminal)))))
        \<in> borel_measurable (?MI \<Otimes>\<^sub>M ?MI)"
  proof -
    note raw = lborel.borel_measurable_nn_integral_fst[OF joint_integrand]
    show ?thesis
      using raw by (simp only: split_beta' fst_conv snd_conv)
  qed
  have negative_integrand_measurable:
      "\<And>pos. (\<lambda>neg. nn_integral lborel
        (\<lambda>terminal.
          slp_left_branch_positive_kernel_list R cutoff potential
              terminal_value (map (\<lambda>j. (pos j, neg j)) (k # ks))
              origin terminal *
            ennreal (norm (output_factor
              (slp_left_branch_output
                (map (\<lambda>j. (pos j, neg j)) (k # ks)) terminal)))))
        \<in> borel_measurable ?MI"
  proof -
    fix pos :: "nat \<Rightarrow> slp_point"
    let ?pos = "restrict pos (insert k (set ks))"
    have pos_space: "?pos \<in> space ?MI"
      by (simp add: space_PiM PiE_iff)
    have pair_measurable:
        "(\<lambda>neg. (?pos, neg))
          \<in> measurable ?MI (?MI \<Otimes>\<^sub>M ?MI)"
      by measurable
    note raw = measurable_compose[OF pair_measurable
      terminal_integral_measurable]
    have pairs:
        "map (\<lambda>j. (?pos j, neg j)) (k # ks) =
          map (\<lambda>j. (pos j, neg j)) (k # ks)"
      for neg
      by (rule map_cong[OF refl]) (simp add: restrict_apply')
    show "(\<lambda>neg. nn_integral lborel
        (\<lambda>terminal.
          slp_left_branch_positive_kernel_list R cutoff potential
              terminal_value (map (\<lambda>j. (pos j, neg j)) (k # ks))
              origin terminal *
            ennreal (norm (output_factor
              (slp_left_branch_output
                (map (\<lambda>j. (pos j, neg j)) (k # ks)) terminal)))))
        \<in> borel_measurable ?MI"
      using raw
      by (simp only: comp_def split_beta' fst_conv snd_conv pairs)
  qed
  have MT_sigma: "sigma_finite_measure ?MT"
    by (rule product.sigma_finite) simp
  interpret tail: sigma_finite_measure ?MT
    by (rule MT_sigma)
  interpret swap: pair_sigma_finite ?MT "(lborel :: slp_point measure)"
    by standard
  have swap_integrand_measurable:
      "\<And>y. (\<lambda>(x, ya). nn_integral ?MT
        (\<lambda>xa. nn_integral lborel
          (\<lambda>terminal.
            slp_left_branch_positive_kernel_list R cutoff potential
                terminal_value
                (map (\<lambda>j. ((x(k := y)) j, (xa(k := ya)) j))
                  (k # ks)) origin terminal *
              ennreal (norm (output_factor
                (slp_left_branch_output
                  (map (\<lambda>j. ((x(k := y)) j, (xa(k := ya)) j))
                    (k # ks)) terminal))))))
        \<in> borel_measurable (?MT \<Otimes>\<^sub>M lborel)"
  proof -
    fix y :: slp_point
    let ?MS = "((?MT \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M ?MT) \<Otimes>\<^sub>M
      (lborel :: slp_point measure)"
    have insert_union: "insert k (set ks) = set ks \<union> {k}"
      by simp
    have pos_tail_projection:
        "(\<lambda>(((x, ya), xa), terminal). x)
          \<in> measurable ?MS ?MT"
    proof -
      have first:
          "fst \<in> measurable ?MS ((?MT \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M ?MT)"
        by (rule measurable_fst)
      have second:
          "fst \<in> measurable ((?MT \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M ?MT)
            (?MT \<Otimes>\<^sub>M lborel)"
        by (rule measurable_fst)
      have third:
          "fst \<in> measurable (?MT \<Otimes>\<^sub>M lborel) ?MT"
        by (rule measurable_fst)
      note raw = measurable_compose[OF measurable_compose[OF first second]
        third]
      show ?thesis
        using raw by (simp only: comp_def split_beta')
    qed
    have y_constant:
        "(\<lambda>_. y) \<in> measurable ?MS (lborel :: slp_point measure)"
      by measurable
    have pos_full[measurable]:
        "(\<lambda>(((x, ya), xa), terminal). x(k := y))
          \<in> measurable ?MS ?MI"
    proof -
      note raw = measurable_fun_upd[
        where I="insert k (set ks)" and J="set ks" and i=k
          and M="\<lambda>_::nat. (lborel :: slp_point measure)"
          and f="\<lambda>(((x, ya), xa), terminal). x"
          and h="\<lambda>_. y",
        OF insert_union pos_tail_projection y_constant]
      show ?thesis
        using raw by (simp only: split_beta')
    qed
    have neg_tail_projection:
        "(\<lambda>(((x, ya), xa), terminal). xa)
          \<in> measurable ?MS ?MT"
    proof -
      have first:
          "fst \<in> measurable ?MS ((?MT \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M ?MT)"
        by (rule measurable_fst)
      have second:
          "snd \<in> measurable ((?MT \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M ?MT) ?MT"
        by (rule measurable_snd)
      note raw = measurable_compose[OF first second]
      show ?thesis
        using raw by (simp only: comp_def split_beta')
    qed
    have neg_head_projection:
        "(\<lambda>(((x, ya), xa), terminal). ya)
          \<in> measurable ?MS (lborel :: slp_point measure)"
    proof -
      have first:
          "fst \<in> measurable ?MS ((?MT \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M ?MT)"
        by (rule measurable_fst)
      have second:
          "fst \<in> measurable ((?MT \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M ?MT)
            (?MT \<Otimes>\<^sub>M lborel)"
        by (rule measurable_fst)
      have third:
          "snd \<in> measurable (?MT \<Otimes>\<^sub>M lborel)
            (lborel :: slp_point measure)"
        by (rule measurable_snd)
      note raw = measurable_compose[OF measurable_compose[OF first second]
        third]
      show ?thesis
        using raw by (simp only: comp_def split_beta')
    qed
    have neg_full[measurable]:
        "(\<lambda>(((x, ya), xa), terminal). xa(k := ya))
          \<in> measurable ?MS ?MI"
    proof -
      note raw = measurable_fun_upd[
        where I="insert k (set ks)" and J="set ks" and i=k
          and M="\<lambda>_::nat. (lborel :: slp_point measure)"
          and f="\<lambda>(((x, ya), xa), terminal). xa"
          and h="\<lambda>(((x, ya), xa), terminal). ya",
        OF insert_union neg_tail_projection neg_head_projection]
      show ?thesis
        using raw by (simp only: split_beta')
    qed
    have family_update:
        "(\<lambda>(((x, ya), xa), terminal).
          (x(k := y), xa(k := ya)))
          \<in> measurable ?MS (?MI \<Otimes>\<^sub>M ?MI)"
    proof -
      note raw = measurable_Pair[OF pos_full neg_full]
      show ?thesis
        using raw by (simp only: split_beta')
    qed
    have terminal_projection:
        "(\<lambda>(((x, ya), xa), terminal). terminal)
          \<in> measurable ?MS (lborel :: slp_point measure)"
    proof -
      have raw:
          "snd \<in> measurable ?MS (lborel :: slp_point measure)"
        by (rule measurable_snd)
      show ?thesis
        using raw by (simp only: split_beta')
    qed
    have full_update[measurable]:
        "(\<lambda>(((x, ya), xa), terminal).
          ((x(k := y), xa(k := ya)), terminal))
          \<in> measurable ?MS ?MF"
    proof -
      note raw = measurable_Pair[OF family_update terminal_projection]
      show ?thesis
        using raw by (simp only: split_beta')
    qed
    have full_joint:
        "(\<lambda>(((x, ya), xa), terminal).
          slp_left_branch_positive_kernel_list R cutoff potential
              terminal_value
              (map (\<lambda>j. ((x(k := y)) j, (xa(k := ya)) j))
                (k # ks)) origin terminal *
            ennreal (norm (output_factor
              (slp_left_branch_output
                (map (\<lambda>j. ((x(k := y)) j, (xa(k := ya)) j))
                  (k # ks)) terminal))))
          \<in> borel_measurable ?MS"
      using measurable_compose[OF full_update joint_integrand]
      by (simp only: comp_def split_beta' fst_conv snd_conv)
    have after_terminal:
        "(\<lambda>((x, ya), xa). nn_integral lborel
          (\<lambda>terminal.
            slp_left_branch_positive_kernel_list R cutoff potential
                terminal_value
                (map (\<lambda>j. ((x(k := y)) j, (xa(k := ya)) j))
                  (k # ks)) origin terminal *
              ennreal (norm (output_factor
                (slp_left_branch_output
                  (map (\<lambda>j. ((x(k := y)) j, (xa(k := ya)) j))
                    (k # ks)) terminal)))))
          \<in> borel_measurable ((?MT \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M ?MT)"
    proof -
      note raw = lborel.borel_measurable_nn_integral_fst[OF full_joint]
      show ?thesis
        using raw by (simp only: split_beta' fst_conv snd_conv)
    qed
    note raw = tail.borel_measurable_nn_integral_fst[OF after_terminal]
    show "(\<lambda>(x, ya). nn_integral ?MT
        (\<lambda>xa. nn_integral lborel
          (\<lambda>terminal.
            slp_left_branch_positive_kernel_list R cutoff potential
                terminal_value
                (map (\<lambda>j. ((x(k := y)) j, (xa(k := ya)) j))
                  (k # ks)) origin terminal *
              ennreal (norm (output_factor
                (slp_left_branch_output
                  (map (\<lambda>j. ((x(k := y)) j, (xa(k := ya)) j))
                    (k # ks)) terminal))))))
        \<in> borel_measurable (?MT \<Otimes>\<^sub>M lborel)"
      using raw by (simp only: split_beta' fst_conv snd_conv)
  qed
  have swap_tail_head_negative:
      "\<And>y. nn_integral ?MT
        (\<lambda>x. nn_integral lborel
          (\<lambda>ya. nn_integral ?MT
            (\<lambda>xa. nn_integral lborel
              (\<lambda>terminal.
                slp_left_branch_positive_kernel_list R cutoff potential
                    terminal_value
                    (map (\<lambda>j. ((x(k := y)) j, (xa(k := ya)) j))
                      (k # ks)) origin terminal *
                  ennreal (norm (output_factor
                    (slp_left_branch_output
                      (map (\<lambda>j. ((x(k := y)) j, (xa(k := ya)) j))
                        (k # ks)) terminal))))))) =
        nn_integral lborel
          (\<lambda>ya. nn_integral ?MT
            (\<lambda>x. nn_integral ?MT
              (\<lambda>xa. nn_integral lborel
                (\<lambda>terminal.
                  slp_left_branch_positive_kernel_list R cutoff potential
                      terminal_value
                      (map (\<lambda>j. ((x(k := y)) j, (xa(k := ya)) j))
                        (k # ks)) origin terminal *
                    ennreal (norm (output_factor
                      (slp_left_branch_output
                        (map (\<lambda>j. ((x(k := y)) j, (xa(k := ya)) j))
                          (k # ks)) terminal)))))))"
  proof -
    fix y :: slp_point
    note raw = swap.Fubini'[OF swap_integrand_measurable[of y], symmetric]
    show "nn_integral ?MT
        (\<lambda>x. nn_integral lborel
          (\<lambda>ya. nn_integral ?MT
            (\<lambda>xa. nn_integral lborel
              (\<lambda>terminal.
                slp_left_branch_positive_kernel_list R cutoff potential
                    terminal_value
                    (map (\<lambda>j. ((x(k := y)) j, (xa(k := ya)) j))
                      (k # ks)) origin terminal *
                  ennreal (norm (output_factor
                    (slp_left_branch_output
                      (map (\<lambda>j. ((x(k := y)) j, (xa(k := ya)) j))
                        (k # ks)) terminal))))))) =
        nn_integral lborel
          (\<lambda>ya. nn_integral ?MT
            (\<lambda>x. nn_integral ?MT
              (\<lambda>xa. nn_integral lborel
                (\<lambda>terminal.
                  slp_left_branch_positive_kernel_list R cutoff potential
                      terminal_value
                      (map (\<lambda>j. ((x(k := y)) j, (xa(k := ya)) j))
                        (k # ks)) origin terminal *
                    ennreal (norm (output_factor
                      (slp_left_branch_output
                        (map (\<lambda>j. ((x(k := y)) j, (xa(k := ya)) j))
                          (k # ks)) terminal)))))))"
      using raw by (simp only: split_beta')
  qed
  have updated_pairs:
      "\<And>x y xa ya.
        map (\<lambda>j. ((x(k := y)) j, (xa(k := ya)) j)) (k # ks) =
          (y, ya) # map (\<lambda>j. (x j, xa j)) ks"
  proof -
    fix x y xa ya
    have tail:
        "map (\<lambda>j. ((x(k := y)) j, (xa(k := ya)) j)) ks =
          map (\<lambda>j. (x j, xa j)) ks"
      by (rule map_cong[OF refl]) (use head_not_tail in auto)
    show "map (\<lambda>j. ((x(k := y)) j, (xa(k := ya)) j)) (k # ks) =
        (y, ya) # map (\<lambda>j. (x j, xa j)) ks"
      by (simp only: list.map fun_upd_same tail)
  qed
  let ?TF = "(?MT \<Otimes>\<^sub>M ?MT) \<Otimes>\<^sub>M
    (lborel :: slp_point measure)"
  have tail_pos_projection:
      "(fst \<circ> fst) \<in> measurable ?TF ?MT"
  proof -
    have first: "fst \<in> measurable ?TF (?MT \<Otimes>\<^sub>M ?MT)"
      by (rule measurable_fst)
    show ?thesis
      using measurable_compose[OF first measurable_fst]
      by (simp only: comp_def)
  qed
  have tail_neg_projection:
      "(snd \<circ> fst) \<in> measurable ?TF ?MT"
  proof -
    have first: "fst \<in> measurable ?TF (?MT \<Otimes>\<^sub>M ?MT)"
      by (rule measurable_fst)
    show ?thesis
      using measurable_compose[OF first measurable_snd]
      by (simp only: comp_def)
  qed
  have tail_pos_coordinate:
      "\<And>j. j \<in> set ks \<Longrightarrow>
        (\<lambda>((x, xa), terminal). x j) \<in> measurable ?TF lborel"
  proof -
    fix j
    assume j: "j \<in> set ks"
    have component: "(\<lambda>x. x j) \<in> measurable ?MT lborel"
      by (rule measurable_component_singleton[OF j])
    show "(\<lambda>((x, xa), terminal). x j) \<in> measurable ?TF lborel"
      using measurable_compose[OF tail_pos_projection component]
      by (simp only: comp_def split_beta')
  qed
  have tail_neg_coordinate:
      "\<And>j. j \<in> set ks \<Longrightarrow>
        (\<lambda>((x, xa), terminal). xa j) \<in> measurable ?TF lborel"
  proof -
    fix j
    assume j: "j \<in> set ks"
    have component: "(\<lambda>xa. xa j) \<in> measurable ?MT lborel"
      by (rule measurable_component_singleton[OF j])
    show "(\<lambda>((x, xa), terminal). xa j) \<in> measurable ?TF lborel"
      using measurable_compose[OF tail_neg_projection component]
      by (simp only: comp_def split_beta')
  qed
  have tail_kernel_joint:
      "\<And>ya. (\<lambda>((x, xa), terminal).
        slp_left_branch_positive_kernel_list R cutoff potential terminal_value
          (map (\<lambda>j. (x j, xa j)) ks) ya terminal)
        \<in> borel_measurable ?TF"
  proof -
    fix ya :: slp_point
    let ?pair_functions =
      "(map (\<lambda>j. \<lambda>((x, xa), terminal). (x j, xa j)) ks ::
        ((((nat \<Rightarrow> slp_point) \<times> (nat \<Rightarrow> slp_point)) \<times>
            slp_point) \<Rightarrow> slp_point \<times> slp_point) list)"
    have pair_first:
        "\<And>pair. pair \<in> set ?pair_functions \<Longrightarrow>
          (\<lambda>z. fst (pair z)) \<in> measurable ?TF lborel"
    proof -
      fix pair
      assume "pair \<in> set ?pair_functions"
      then obtain j where j: "j \<in> set ks"
        and pair: "pair = (\<lambda>((x, xa), terminal). (x j, xa j))"
        by auto
      show "(\<lambda>z. fst (pair z)) \<in> measurable ?TF lborel"
        unfolding pair
        using tail_pos_coordinate[OF j]
        by (simp only: split_beta' fst_conv)
    qed
    have pair_second:
        "\<And>pair. pair \<in> set ?pair_functions \<Longrightarrow>
          (\<lambda>z. snd (pair z)) \<in> measurable ?TF lborel"
    proof -
      fix pair
      assume "pair \<in> set ?pair_functions"
      then obtain j where j: "j \<in> set ks"
        and pair: "pair = (\<lambda>((x, xa), terminal). (x j, xa j))"
        by auto
      show "(\<lambda>z. snd (pair z)) \<in> measurable ?TF lborel"
        unfolding pair
        using tail_neg_coordinate[OF j]
        by (simp only: split_beta' snd_conv)
    qed
    have origin_constant:
        "(\<lambda>_::((nat \<Rightarrow> slp_point) \<times>
            (nat \<Rightarrow> slp_point)) \<times> slp_point. ya)
          \<in> measurable ?TF lborel"
      by measurable
    have terminal_projection:
        "(\<lambda>((x, xa), terminal). terminal) \<in> measurable ?TF lborel"
    proof -
      have raw: "snd \<in> measurable ?TF (lborel :: slp_point measure)"
        by (rule measurable_snd)
      show ?thesis
        using raw by (simp only: split_beta')
    qed
    note raw = slp_left_branch_positive_kernel_list_param_measurable[
      where M = ?TF and pair_functions = ?pair_functions
        and origin = "\<lambda>_. ya"
        and terminal = "\<lambda>((x, xa), terminal). terminal",
      OF cutoff_measurable potential_measurable terminal_value_measurable
        origin_constant terminal_projection pair_first pair_second]
    show "(\<lambda>((x, xa), terminal).
        slp_left_branch_positive_kernel_list R cutoff potential terminal_value
          (map (\<lambda>j. (x j, xa j)) ks) ya terminal)
        \<in> borel_measurable ?TF"
      using raw
      by (simp only: list.map map_map comp_def split_beta')
  qed
  have tail_increment_sum_measurable:
      "\<And>js. set js \<subseteq> set ks \<Longrightarrow>
        (\<lambda>((x, xa), terminal).
          sum_list (map (\<lambda>j. x j - xa j) js))
        \<in> borel_measurable ?TF"
  proof -
    fix js
    assume subset: "set js \<subseteq> set ks"
    show "(\<lambda>((x, xa), terminal).
        sum_list (map (\<lambda>j. x j - xa j) js))
      \<in> borel_measurable ?TF"
      using subset
    proof (induction js)
      case Nil
      then show ?case
        by (simp only: list.map sum_list.Nil split_beta') measurable
    next
      case (Cons j js)
      have j: "j \<in> set ks"
        using Cons.prems by simp
      have rest: "set js \<subseteq> set ks"
        using Cons.prems by simp
      have pos_j[measurable]:
          "(\<lambda>((x, xa), terminal). x j) \<in> borel_measurable ?TF"
        using tail_pos_coordinate[OF j]
        by (simp only: measurable_lborel1)
      have neg_j[measurable]:
          "(\<lambda>((x, xa), terminal). xa j) \<in> borel_measurable ?TF"
        using tail_neg_coordinate[OF j]
        by (simp only: measurable_lborel1)
      have tail_sum[measurable]:
          "(\<lambda>((x, xa), terminal).
            sum_list (map (\<lambda>j. x j - xa j) js))
            \<in> borel_measurable ?TF"
        by (rule Cons.IH[OF rest])
      have pos_raw[measurable]:
          "(\<lambda>z. fst (fst z) j) \<in> borel_measurable ?TF"
        using pos_j by (simp only: split_beta')
      have neg_raw[measurable]:
          "(\<lambda>z. snd (fst z) j) \<in> borel_measurable ?TF"
        using neg_j by (simp only: split_beta')
      have tail_raw[measurable]:
          "(\<lambda>z. sum_list
            (map (\<lambda>j. fst (fst z) j - snd (fst z) j) js))
            \<in> borel_measurable ?TF"
        using tail_sum by (simp only: split_beta')
      show ?case
        by (simp only: list.map sum_list.Cons split_beta') measurable
    qed
  qed
  have tail_output_argument:
      "\<And>y ya. (\<lambda>((x, xa), terminal).
        slp_left_branch_output (map (\<lambda>j. (x j, xa j)) ks) terminal +
          y - ya) \<in> measurable ?TF lborel"
  proof -
    fix y ya :: slp_point
    have terminal_measurable[measurable]:
        "(\<lambda>((x, xa), terminal). terminal) \<in> borel_measurable ?TF"
    proof -
      have raw: "snd \<in> measurable ?TF (lborel :: slp_point measure)"
        by (rule measurable_snd)
      show ?thesis
        using raw by (simp only: measurable_lborel1 split_beta')
    qed
    have sums[measurable]:
        "(\<lambda>((x, xa), terminal).
          sum_list (map (\<lambda>j. x j - xa j) ks))
          \<in> borel_measurable ?TF"
      by (rule tail_increment_sum_measurable) simp
    have terminal_raw: "snd \<in> borel_measurable ?TF"
      using terminal_measurable by (simp only: split_beta')
    have sums_raw:
        "(\<lambda>z. sum_list
          (map (\<lambda>j. fst (fst z) j - snd (fst z) j) ks))
          \<in> borel_measurable ?TF"
      using sums by (simp only: split_beta')
    have first_raw:
        "(\<lambda>z. snd z + sum_list
          (map (\<lambda>j. fst (fst z) j - snd (fst z) j) ks))
          \<in> borel_measurable ?TF"
      by (rule borel_measurable_add[OF terminal_raw sums_raw])
    have y_raw:
        "(\<lambda>_::((nat \<Rightarrow> slp_point) \<times>
            (nat \<Rightarrow> slp_point)) \<times> slp_point. y)
          \<in> borel_measurable ?TF"
      by measurable
    have plus_y_raw:
        "(\<lambda>z. snd z + sum_list
            (map (\<lambda>j. fst (fst z) j - snd (fst z) j) ks) + y)
          \<in> borel_measurable ?TF"
      by (rule borel_measurable_add[OF first_raw y_raw])
    have ya_raw:
        "(\<lambda>_::((nat \<Rightarrow> slp_point) \<times>
            (nat \<Rightarrow> slp_point)) \<times> slp_point. ya)
          \<in> borel_measurable ?TF"
      by measurable
    have raw:
        "(\<lambda>z. snd z + sum_list
            (map (\<lambda>j. fst (fst z) j - snd (fst z) j) ks) + y - ya)
          \<in> borel_measurable ?TF"
      by (rule borel_measurable_diff[OF plus_y_raw ya_raw])
    show "(\<lambda>((x, xa), terminal).
        slp_left_branch_output (map (\<lambda>j. (x j, xa j)) ks) terminal +
          y - ya) \<in> measurable ?TF lborel"
      using raw
      unfolding slp_left_branch_output_def slp_branch_increment_def
      by (simp only: measurable_lborel1 map_map comp_def split_beta'
          fst_conv snd_conv)
  qed
  have tail_joint_integrand:
      "(\<lambda>((x, xa), terminal).
        slp_left_branch_positive_kernel_list R cutoff potential terminal_value
            (map (\<lambda>j. (x j, xa j)) ks) ya terminal *
          ennreal (norm (output_factor
            (slp_left_branch_output (map (\<lambda>j. (x j, xa j)) ks)
              terminal + y - ya))))
        \<in> borel_measurable ?TF"
      for y ya
  proof -
    have output_value:
        "(\<lambda>((x, xa), terminal). output_factor
          (slp_left_branch_output (map (\<lambda>j. (x j, xa j)) ks)
            terminal + y - ya)) \<in> borel_measurable ?TF"
      using measurable_comp[OF tail_output_argument[of y ya]
        output_factor_current]
      by (simp only: comp_def split_beta')
    have output_norm:
        "(\<lambda>((x, xa), terminal). norm (output_factor
          (slp_left_branch_output (map (\<lambda>j. (x j, xa j)) ks)
            terminal + y - ya))) \<in> borel_measurable ?TF"
      using measurable_compose[OF output_value borel_measurable_norm]
      by (simp only: comp_def split_beta')
    have output_ennreal:
        "(\<lambda>((x, xa), terminal). ennreal (norm (output_factor
          (slp_left_branch_output (map (\<lambda>j. (x j, xa j)) ks)
            terminal + y - ya)))) \<in> borel_measurable ?TF"
      using measurable_compose[OF output_norm measurable_ennreal]
      by (simp only: comp_def split_beta')
    note raw = borel_measurable_times_ennreal[OF
      tail_kernel_joint[of ya] output_ennreal]
    show ?thesis
      using raw by (simp only: split_beta')
  qed
  have tail_after_terminal:
      "(\<lambda>(x, xa). nn_integral lborel
        (\<lambda>terminal.
          slp_left_branch_positive_kernel_list R cutoff potential terminal_value
              (map (\<lambda>j. (x j, xa j)) ks) ya terminal *
            ennreal (norm (output_factor
              (slp_left_branch_output (map (\<lambda>j. (x j, xa j)) ks)
                terminal + y - ya)))))
        \<in> borel_measurable (?MT \<Otimes>\<^sub>M ?MT)"
      for y ya
  proof -
    note raw = lborel.borel_measurable_nn_integral_fst[OF
      tail_joint_integrand[of ya y]]
    show ?thesis
      using raw by (simp only: split_beta' fst_conv snd_conv)
  qed
  let ?T = "\<lambda>y ya x xa. nn_integral lborel
    (\<lambda>terminal.
      slp_left_branch_positive_kernel_list R cutoff potential terminal_value
          (map (\<lambda>j. (x j, xa j)) ks) ya terminal *
        ennreal (norm (output_factor
          (slp_left_branch_output (map (\<lambda>j. (x j, xa j)) ks)
            terminal + y - ya))))"
  have tail_slice_measurable:
      "(\<lambda>xa. ?T y ya x xa) \<in> borel_measurable ?MT"
      for y ya x
  proof -
    let ?x = "restrict x (set ks)"
    have x_space: "?x \<in> space ?MT"
      by (simp add: space_PiM PiE_iff)
    have pair_measurable:
        "(\<lambda>xa. (?x, xa)) \<in> measurable ?MT (?MT \<Otimes>\<^sub>M ?MT)"
      using x_space by measurable
    note raw = measurable_compose[OF pair_measurable
      tail_after_terminal[of ya y]]
    have pairs:
        "map (\<lambda>j. (?x j, xa j)) ks =
          map (\<lambda>j. (x j, xa j)) ks"
        for xa
      by (rule map_cong[OF refl]) (simp add: restrict_apply')
    show ?thesis
      using raw
      by (simp only: comp_def split_beta' fst_conv snd_conv pairs)
  qed
  have tail_nested_measurable:
      "(\<lambda>x. nn_integral ?MT (\<lambda>xa. ?T y ya x xa))
        \<in> borel_measurable ?MT"
      for y ya
  proof -
    note raw = tail.borel_measurable_nn_integral_fst[OF
      tail_after_terminal[of ya y]]
    show ?thesis
      using raw by (simp only: split_beta' fst_conv snd_conv)
  qed
  have translated_output_measurable:
      "(\<lambda>z. output_factor (z + y - ya)) \<in> borel_measurable lborel"
      for y ya
    by measurable
  have tail_induction:
      "nn_integral ?MT
          (\<lambda>x. nn_integral ?MT (\<lambda>xa. ?T y ya x xa)) =
        slp_positive_branch_functional R cutoff potential
          (\<lambda>z. ennreal (norm (terminal_value z))) (length ks) ya
          (\<lambda>z. ennreal (norm (output_factor (z + y - ya))))"
      for y ya
    by (rule Cons.IH[OF tail_distinct translated_output_measurable])
  let ?C = "ennreal (inverse (pi ^ 2))"
  have factor_negative_tail:
      "nn_integral ?MT
          (\<lambda>xa. ?C *
            slp_positive_branch_block_weight R cutoff potential origin y ya *
            ?T y ya x xa) =
        (?C * slp_positive_branch_block_weight R cutoff potential origin y ya) *
          nn_integral ?MT (\<lambda>xa. ?T y ya x xa)"
      for y ya x
    by (rule nn_integral_cmult[OF tail_slice_measurable])
  have factor_both_tails:
      "nn_integral ?MT
          (\<lambda>x. nn_integral ?MT
            (\<lambda>xa. ?C *
              slp_positive_branch_block_weight R cutoff potential origin y ya *
              ?T y ya x xa)) =
        (?C * slp_positive_branch_block_weight R cutoff potential origin y ya) *
          nn_integral ?MT
            (\<lambda>x. nn_integral ?MT (\<lambda>xa. ?T y ya x xa))"
      for y ya
    by (simp only: factor_negative_tail
        nn_integral_cmult[OF tail_nested_measurable])
  have MI_sigma: "sigma_finite_measure ?MI"
    by (rule product.sigma_finite) simp
  interpret family: sigma_finite_measure ?MI
    by (rule MI_sigma)
  have outer_integrand_measurable:
      "(\<lambda>pos. nn_integral ?MI
        (\<lambda>neg. nn_integral lborel
          (\<lambda>terminal.
            slp_left_branch_positive_kernel_list R cutoff potential
                terminal_value (map (\<lambda>j. (pos j, neg j)) (k # ks))
                origin terminal *
              ennreal (norm (output_factor
                (slp_left_branch_output
                  (map (\<lambda>j. (pos j, neg j)) (k # ks)) terminal))))))
        \<in> borel_measurable ?MI"
  proof -
    note raw = family.borel_measurable_nn_integral_fst[OF
      terminal_integral_measurable]
    show ?thesis
      using raw by (simp only: split_beta' fst_conv snd_conv)
  qed
  let ?H = "\<lambda>y ya.
    slp_positive_branch_block_weight R cutoff potential origin y ya *
      slp_positive_branch_functional R cutoff potential
        (\<lambda>z. ennreal (norm (terminal_value z))) (length ks) ya
        (\<lambda>z. ennreal (norm (output_factor (z + y - ya))))"
  have head_tail_value:
      "nn_integral ?MT
          (\<lambda>x. nn_integral ?MT
            (\<lambda>xa. nn_integral lborel
              (\<lambda>terminal.
                slp_left_branch_positive_kernel_list R cutoff potential
                    terminal_value
                    ((y, ya) # map (\<lambda>j. (x j, xa j)) ks)
                    origin terminal *
                  ennreal (norm (output_factor
                    (slp_left_branch_output
                      ((y, ya) # map (\<lambda>j. (x j, xa j)) ks)
                      terminal)))))) =
        ?C * ?H y ya"
      for y ya
  proof -
    show ?thesis
      apply (simp only:
        slp_left_branch_positive_kernel_list_Suc_integral[
          OF cutoff_measurable potential_measurable terminal_value_measurable
            output_factor_current]
        fst_conv snd_conv)
      apply (simp only: factor_both_tails)
      apply (simp only: tail_induction mult.assoc)
      done
  qed
  have swapped_head_measurable:
      "(\<lambda>(ya, x). nn_integral ?MT
        (\<lambda>xa. nn_integral lborel
          (\<lambda>terminal.
            slp_left_branch_positive_kernel_list R cutoff potential
                terminal_value
                (map (\<lambda>j. ((x(k := y)) j, (xa(k := ya)) j))
                  (k # ks)) origin terminal *
              ennreal (norm (output_factor
                (slp_left_branch_output
                  (map (\<lambda>j. ((x(k := y)) j, (xa(k := ya)) j))
                    (k # ks)) terminal))))))
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M ?MT)"
      for y
  proof -
    note raw = measurable_pair_swap[OF swap_integrand_measurable[of y]]
    show ?thesis
      using raw by (simp only: split_beta' fst_conv snd_conv)
  qed
  have scaled_head_measurable:
      "(\<lambda>ya. ?C * ?H y ya) \<in> borel_measurable lborel"
      for y
  proof -
    note raw = tail.borel_measurable_nn_integral_fst[OF
      swapped_head_measurable[of y]]
    show ?thesis
      using raw
      by (simp only: split_beta' fst_conv snd_conv updated_pairs
          head_tail_value)
  qed
  have C_positive: "0 < ?C"
    by simp
  have C_ne_zero: "?C \<noteq> 0"
    using C_positive by simp
  have C_ne_top: "?C \<noteq> top"
    by simp
  have head_integrand_measurable:
      "(\<lambda>ya. ?H y ya) \<in> borel_measurable lborel"
      for y
  proof -
    have divided:
        "(\<lambda>ya. (?C * ?H y ya) / ?C) \<in> borel_measurable lborel"
      using scaled_head_measurable[of y] by measurable
    have cancel:
        "(\<lambda>ya. (?C * ?H y ya) / ?C) = (\<lambda>ya. ?H y ya)"
      apply (rule ext)
      apply (subst mult.commute)
      apply (rule ennreal_mult_divide_eq[OF C_ne_zero C_ne_top])
      done
    show ?thesis
      using divided unfolding cancel .
  qed
  have extract_negative_head:
      "nn_integral lborel (\<lambda>ya. ?C * ?H y ya) =
        ?C * nn_integral lborel (\<lambda>ya. ?H y ya)"
      for y
    by (rule nn_integral_cmult[OF head_integrand_measurable])
  let ?YM = "(lborel :: slp_point measure) \<Otimes>\<^sub>M ?MT"
  have insert_union_again: "insert k (set ks) = set ks \<union> {k}"
    by simp
  have head_projection:
      "fst \<in> measurable ?YM (lborel :: slp_point measure)"
    by (rule measurable_fst)
  have tail_projection:
      "snd \<in> measurable ?YM ?MT"
    by (rule measurable_snd)
  have pos_update_joint:
      "(\<lambda>(y, x). x(k := y)) \<in> measurable ?YM ?MI"
  proof -
    note raw = measurable_fun_upd[
      where I="insert k (set ks)" and J="set ks" and i=k
        and M="\<lambda>_::nat. (lborel :: slp_point measure)"
        and f=snd and h=fst,
      OF insert_union_again tail_projection head_projection]
    show ?thesis
      using raw by (simp only: split_beta')
  qed
  have outer_after_update_joint:
      "(\<lambda>(y, x). nn_integral ?MI
        (\<lambda>neg. nn_integral lborel
          (\<lambda>terminal.
            slp_left_branch_positive_kernel_list R cutoff potential
                terminal_value
                (map (\<lambda>j. ((x(k := y)) j, neg j)) (k # ks))
                origin terminal *
              ennreal (norm (output_factor
                (slp_left_branch_output
                  (map (\<lambda>j. ((x(k := y)) j, neg j)) (k # ks))
                  terminal))))))
        \<in> borel_measurable ?YM"
    using measurable_compose[OF pos_update_joint outer_integrand_measurable]
    by (simp only: comp_def split_beta')
  have outer_head_value:
      "nn_integral ?MT
          (\<lambda>x. nn_integral ?MI
            (\<lambda>neg. nn_integral lborel
              (\<lambda>terminal.
                slp_left_branch_positive_kernel_list R cutoff potential
                    terminal_value
                    (map (\<lambda>j. ((x(k := y)) j, neg j)) (k # ks))
                    origin terminal *
                  ennreal (norm (output_factor
                    (slp_left_branch_output
                      (map (\<lambda>j. ((x(k := y)) j, neg j)) (k # ks))
                      terminal)))))) =
        nn_integral lborel (\<lambda>ya. ?C * ?H y ya)"
      for y
  proof -
    show ?thesis
      apply (subst product.product_nn_integral_insert_rev)
        apply (rule finite_tail)
       apply (rule head_not_tail)
      apply (rule negative_integrand_measurable)
      apply (subst swap_tail_head_negative)
      apply (simp only: updated_pairs head_tail_value)
      done
  qed
  have scaled_outer_measurable:
      "(\<lambda>y. ?C * nn_integral lborel (\<lambda>ya. ?H y ya))
        \<in> borel_measurable lborel"
  proof -
    note raw = tail.borel_measurable_nn_integral_fst[OF
      outer_after_update_joint]
    show ?thesis
      using raw
      by (simp only: split_beta' fst_conv snd_conv outer_head_value
          extract_negative_head)
  qed
  have outer_integrand_without_constant_measurable:
      "(\<lambda>y. nn_integral lborel (\<lambda>ya. ?H y ya))
        \<in> borel_measurable lborel"
  proof -
    have divided:
        "(\<lambda>y. (?C * nn_integral lborel (\<lambda>ya. ?H y ya)) / ?C)
          \<in> borel_measurable lborel"
      using scaled_outer_measurable by measurable
    have cancel:
        "(\<lambda>y. (?C * nn_integral lborel (\<lambda>ya. ?H y ya)) / ?C) =
          (\<lambda>y. nn_integral lborel (\<lambda>ya. ?H y ya))"
      apply (rule ext)
      apply (subst mult.commute)
      apply (rule ennreal_mult_divide_eq[OF C_ne_zero C_ne_top])
      done
    show ?thesis
      using divided unfolding cancel .
  qed
  have extract_positive_head:
      "nn_integral lborel
          (\<lambda>y. ?C * nn_integral lborel (\<lambda>ya. ?H y ya)) =
        ?C * nn_integral lborel
          (\<lambda>y. nn_integral lborel (\<lambda>ya. ?H y ya))"
    by (rule nn_integral_cmult[OF
          outer_integrand_without_constant_measurable])
  show ?case
    apply (simp only: list.set list.size)
    apply (subst product.product_nn_integral_insert_rev)
      apply (rule finite_tail)
     apply (rule head_not_tail)
    apply (rule outer_integrand_measurable)
    apply (subst product.product_nn_integral_insert_rev)
      apply (rule finite_tail)
     apply (rule head_not_tail)
    apply (rule negative_integrand_measurable)
    apply (subst swap_tail_head_negative)
    apply (simp only: updated_pairs)
    apply (simp only:
      slp_left_branch_positive_kernel_list_Suc_integral[
        OF cutoff_measurable potential_measurable terminal_value_measurable
          output_factor_current]
      fst_conv snd_conv)
    apply (simp only: factor_both_tails)
    apply (simp only: tail_induction)
    apply (simp only: mult.assoc)
    apply (simp only: extract_negative_head extract_positive_head)
    apply (simp only: add_Suc_right)
    apply (simp only: slp_positive_branch_functional.simps)
    apply (simp only: add_0_right)
    done
qed

theorem slp_left_branch_positive_kernel_list_integral_functional_natural:
  fixes branch_dummy :: "'i::finite itself"
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_value_measurable[measurable]:
      "terminal_value \<in> borel_measurable lborel"
    and output_factor_measurable[measurable]:
      "output_factor \<in> borel_measurable lborel"
  shows
    "nn_integral
        (PiM {..<CARD('i)}
          (\<lambda>_::nat. (lborel :: slp_point measure)))
        (\<lambda>pos. nn_integral
          (PiM {..<CARD('i)}
            (\<lambda>_::nat. (lborel :: slp_point measure)))
          (\<lambda>neg. nn_integral lborel
            (\<lambda>terminal.
              slp_left_branch_positive_kernel_list R cutoff potential
                  terminal_value
                  (map (\<lambda>k. (pos k, neg k)) [0..<CARD('i)])
                  origin terminal *
                ennreal (norm (output_factor
                  (slp_left_branch_output
                    (map (\<lambda>k. (pos k, neg k)) [0..<CARD('i)])
                    terminal)))))) =
      slp_positive_branch_functional R cutoff potential
        (\<lambda>x. ennreal (norm (terminal_value x))) CARD('i) origin
        (\<lambda>x. ennreal (norm (output_factor x)))"
proof -
  have distinct_indices: "distinct [0..<CARD('i)]"
    by (rule distinct_upt)
  note result =
    slp_left_branch_positive_kernel_list_integral_functional_distinct[
      where ks = "[0..<CARD('i)]" and R = R and cutoff = cutoff
        and potential = potential and terminal_value = terminal_value
        and output_factor = output_factor and origin = origin,
      OF distinct_indices cutoff_measurable potential_measurable
        terminal_value_measurable output_factor_measurable]
  show ?thesis
    using result
    by (simp only: set_upt atLeast0LessThan length_upt diff_zero)
qed

end
