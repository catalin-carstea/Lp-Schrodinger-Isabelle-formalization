theory Inverse_Schrodinger_Lp_Positive_Kernel_List_Fixed_Output_Integral
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Finite_Product_Pair_Insert_NN_Integral"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Positive_Kernel_List_Fixed_Output_Measurable"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Output_Density_Measurable"
begin

section \<open>Fixed-output positive list kernels integrate to output densities\<close>

theorem slp_left_branch_positive_kernel_list_fixed_output_integral_distinct:
  fixes ks :: "nat list"
  assumes distinct_ks: "distinct ks"
    and cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_value_measurable[measurable]:
      "terminal_value \<in> borel_measurable lborel"
  shows
    "nn_integral
        ((PiM (set ks)
            (\<lambda>_::nat. (lborel :: slp_point measure))) \<Otimes>\<^sub>M
          (PiM (set ks)
            (\<lambda>_::nat. (lborel :: slp_point measure))))
        (\<lambda>(pos, neg).
          slp_left_branch_positive_kernel_list_fixed_output R cutoff
            potential terminal_value (map (\<lambda>k. (pos k, neg k)) ks)
            origin target) =
      slp_positive_output_density R cutoff potential
        (\<lambda>x. ennreal (norm (terminal_value x))) (length ks) origin
        target"
  using distinct_ks
proof (induction ks arbitrary: origin target)
  case Nil
  interpret product:
    product_sigma_finite
      "\<lambda>_::nat. (lborel :: slp_point measure)"
    by standard
  let ?E = "PiM ({} :: nat set)
    (\<lambda>_::nat. (lborel :: slp_point measure))"
  interpret empty: sigma_finite_measure ?E
    by (rule product.sigma_finite) simp
  let ?K = "slp_left_branch_positive_kernel_list_fixed_output R cutoff
    potential terminal_value [] origin target"
  have integrand_measurable:
      "(\<lambda>(pos, neg). ?K) \<in> borel_measurable (?E \<Otimes>\<^sub>M ?E)"
    by measurable
  have split:
      "nn_integral (?E \<Otimes>\<^sub>M ?E) (\<lambda>(pos, neg). ?K) =
        nn_integral ?E (\<lambda>pos. nn_integral ?E (\<lambda>neg. ?K))"
  proof -
    note raw = empty.nn_integral_fst[OF integrand_measurable]
    show ?thesis
      using raw[symmetric] by (simp only: split_beta')
  qed
  have inner_empty:
      "nn_integral ?E (\<lambda>neg. ?K) = ?K"
    by (rule product.nn_integral_empty) simp
  have outer_empty:
      "nn_integral ?E (\<lambda>pos. nn_integral ?E (\<lambda>neg. ?K)) = ?K"
    by (simp only: inner_empty)
  show ?case
    using split outer_empty
    by (simp only: list.set list.map list.size
        slp_left_branch_positive_kernel_list_fixed_output_Nil)
next
  case (Cons k ks)
  interpret product:
    product_sigma_finite
      "\<lambda>_::nat. (lborel :: slp_point measure)"
    by standard
  have finite_tail: "finite (set ks)"
    by simp
  have head_not_tail: "k \<notin> set ks"
    using Cons.prems by simp
  have tail_distinct: "distinct ks"
    using Cons.prems by simp
  let ?M = "\<lambda>_::nat. (lborel :: slp_point measure)"
  let ?T = "PiM (set ks) ?M"
  let ?F = "PiM (insert k (set ks)) ?M"
  let ?P = "(lborel :: slp_point measure) \<Otimes>\<^sub>M lborel"
  let ?Q = "?T \<Otimes>\<^sub>M ?T"
  let ?U = "?F \<Otimes>\<^sub>M ?F"
  let ?H = "?P \<Otimes>\<^sub>M ?Q"
  let ?C = "ennreal (inverse (pi ^ 2))"
  let ?f = "\<lambda>(pos, neg).
    slp_left_branch_positive_kernel_list_fixed_output R cutoff potential
      terminal_value (map (\<lambda>j. (pos j, neg j)) (k # ks)) origin target"
  have pos_projection:
      "fst \<in> measurable ?U ?F"
    by (rule measurable_fst)
  have neg_projection:
      "snd \<in> measurable ?U ?F"
    by (rule measurable_snd)
  have pos_coordinate:
      "\<And>j. j \<in> insert k (set ks) \<Longrightarrow>
        (\<lambda>(pos, neg). pos j) \<in> measurable ?U lborel"
  proof -
    fix j
    assume j: "j \<in> insert k (set ks)"
    have component:
        "(\<lambda>pos. pos j) \<in> measurable ?F lborel"
      by (rule measurable_component_singleton[OF j])
    show "(\<lambda>(pos, neg). pos j) \<in> measurable ?U lborel"
      using measurable_compose[OF pos_projection component]
      by (simp only: comp_def split_beta')
  qed
  have neg_coordinate:
      "\<And>j. j \<in> insert k (set ks) \<Longrightarrow>
        (\<lambda>(pos, neg). neg j) \<in> measurable ?U lborel"
  proof -
    fix j
    assume j: "j \<in> insert k (set ks)"
    have component:
        "(\<lambda>neg. neg j) \<in> measurable ?F lborel"
      by (rule measurable_component_singleton[OF j])
    show "(\<lambda>(pos, neg). neg j) \<in> measurable ?U lborel"
      using measurable_compose[OF neg_projection component]
      by (simp only: comp_def split_beta')
  qed
  let ?full_pair_functions =
    "(map (\<lambda>j. \<lambda>(pos, neg). (pos j, neg j)) (k # ks) ::
      (((nat \<Rightarrow> slp_point) \<times> (nat \<Rightarrow> slp_point)) \<Rightarrow>
        slp_point \<times> slp_point) list)"
  have full_pair_first:
      "\<And>pair. pair \<in> set ?full_pair_functions \<Longrightarrow>
        (\<lambda>x. fst (pair x)) \<in> measurable ?U lborel"
  proof -
    fix pair
    assume "pair \<in> set ?full_pair_functions"
    then obtain j where j: "j \<in> insert k (set ks)"
      and pair: "pair = (\<lambda>(pos, neg). (pos j, neg j))"
      by auto
    show "(\<lambda>x. fst (pair x)) \<in> measurable ?U lborel"
      unfolding pair
      using pos_coordinate[OF j]
      by (simp only: split_beta' fst_conv)
  qed
  have full_pair_second:
      "\<And>pair. pair \<in> set ?full_pair_functions \<Longrightarrow>
        (\<lambda>x. snd (pair x)) \<in> measurable ?U lborel"
  proof -
    fix pair
    assume "pair \<in> set ?full_pair_functions"
    then obtain j where j: "j \<in> insert k (set ks)"
      and pair: "pair = (\<lambda>(pos, neg). (pos j, neg j))"
      by auto
    show "(\<lambda>x. snd (pair x)) \<in> measurable ?U lborel"
      unfolding pair
      using neg_coordinate[OF j]
      by (simp only: split_beta' snd_conv)
  qed
  have origin_constant:
      "(\<lambda>_::(nat \<Rightarrow> slp_point) \<times> (nat \<Rightarrow> slp_point).
        origin) \<in> measurable ?U lborel"
    by measurable
  have output_constant:
      "(\<lambda>_::(nat \<Rightarrow> slp_point) \<times> (nat \<Rightarrow> slp_point).
        target) \<in> measurable ?U lborel"
    by measurable
  have full_integrand_measurable:
      "?f \<in> borel_measurable ?U"
  proof -
    note raw =
      slp_left_branch_positive_kernel_list_fixed_output_param_measurable[
        where M = ?U and pair_functions = ?full_pair_functions,
        OF cutoff_measurable potential_measurable terminal_value_measurable
          origin_constant output_constant full_pair_first full_pair_second]
    show ?thesis
      using raw by (simp only: list.map map_map comp_def split_beta')
  qed
  have transported:
      "nn_integral ?U ?f =
        nn_integral ?H
          (\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)).
            ?f (pos_tail(k := pos_head), neg_tail(k := neg_head)))"
    by (rule product.slp_nn_integral_inserted_pair_heads_tails[OF
          finite_tail head_not_tail full_integrand_measurable])
  have updated_pairs:
      "\<And>pos_head neg_head pos_tail neg_tail.
        map (\<lambda>j. ((pos_tail(k := pos_head)) j,
          (neg_tail(k := neg_head)) j)) (k # ks) =
        (pos_head, neg_head) # map (\<lambda>j. (pos_tail j, neg_tail j)) ks"
  proof -
    fix pos_head neg_head pos_tail neg_tail
    have tail:
        "map (\<lambda>j. ((pos_tail(k := pos_head)) j,
          (neg_tail(k := neg_head)) j)) ks =
        map (\<lambda>j. (pos_tail j, neg_tail j)) ks"
      by (rule map_cong[OF refl]) (use head_not_tail in auto)
    show "map (\<lambda>j. ((pos_tail(k := pos_head)) j,
        (neg_tail(k := neg_head)) j)) (k # ks) =
      (pos_head, neg_head) # map (\<lambda>j. (pos_tail j, neg_tail j)) ks"
      by (simp only: list.map fun_upd_same tail)
  qed
  let ?W = "\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)).
    slp_left_branch_positive_kernel_list_fixed_output R cutoff potential
      terminal_value
      ((pos_head, neg_head) # map (\<lambda>j. (pos_tail j, neg_tail j)) ks)
      origin target"
  let ?V = "\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)).
    ?f (pos_tail(k := pos_head), neg_tail(k := neg_head))"
  have transported_integrand:
      "?V = ?W"
    by (rule ext)
      (simp only: split_beta' fst_conv snd_conv updated_pairs)
  have transported_W:
      "nn_integral ?U ?f = nn_integral ?H ?W"
    using transported by (simp only: transported_integrand)
  have tail_pos_projection:
      "(\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)). pos_tail)
        \<in> measurable ?H ?T"
  proof -
    have first: "snd \<in> measurable ?H ?Q"
      by (rule measurable_snd)
    have second: "fst \<in> measurable ?Q ?T"
      by (rule measurable_fst)
    have raw: "(\<lambda>x. fst (snd x)) \<in> measurable ?H ?T"
      by (rule measurable_compose[OF first second])
    show ?thesis
      using raw by (simp only: split_beta')
  qed
  have tail_neg_projection:
      "(\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)). neg_tail)
        \<in> measurable ?H ?T"
  proof -
    have first: "snd \<in> measurable ?H ?Q"
      by (rule measurable_snd)
    have second: "snd \<in> measurable ?Q ?T"
      by (rule measurable_snd)
    have raw: "(\<lambda>x. snd (snd x)) \<in> measurable ?H ?T"
      by (rule measurable_compose[OF first second])
    show ?thesis
      using raw by (simp only: split_beta')
  qed
  have tail_pos_coordinate:
      "\<And>j. j \<in> set ks \<Longrightarrow>
        (\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)). pos_tail j)
          \<in> measurable ?H lborel"
  proof -
    fix j
    assume j: "j \<in> set ks"
    have component: "(\<lambda>pos_tail. pos_tail j) \<in> measurable ?T lborel"
      by (rule measurable_component_singleton[OF j])
    show "(\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)). pos_tail j)
        \<in> measurable ?H lborel"
      using measurable_compose[OF tail_pos_projection component]
      by (simp only: comp_def split_beta')
  qed
  have tail_neg_coordinate:
      "\<And>j. j \<in> set ks \<Longrightarrow>
        (\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)). neg_tail j)
          \<in> measurable ?H lborel"
  proof -
    fix j
    assume j: "j \<in> set ks"
    have component: "(\<lambda>neg_tail. neg_tail j) \<in> measurable ?T lborel"
      by (rule measurable_component_singleton[OF j])
    show "(\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)). neg_tail j)
        \<in> measurable ?H lborel"
      using measurable_compose[OF tail_neg_projection component]
      by (simp only: comp_def split_beta')
  qed
  let ?tail_pair_functions =
    "(map (\<lambda>j. \<lambda>((pos_head, neg_head), (pos_tail, neg_tail)).
        (pos_tail j, neg_tail j)) ks ::
      (((slp_point \<times> slp_point) \<times>
          ((nat \<Rightarrow> slp_point) \<times> (nat \<Rightarrow> slp_point))) \<Rightarrow>
        slp_point \<times> slp_point) list)"
  have tail_pair_first:
      "\<And>pair. pair \<in> set ?tail_pair_functions \<Longrightarrow>
        (\<lambda>x. fst (pair x)) \<in> measurable ?H lborel"
  proof -
    fix pair
    assume "pair \<in> set ?tail_pair_functions"
    then obtain j where j: "j \<in> set ks"
      and pair:
        "pair = (\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)).
          (pos_tail j, neg_tail j))"
      by auto
    show "(\<lambda>x. fst (pair x)) \<in> measurable ?H lborel"
      unfolding pair
      using tail_pos_coordinate[OF j]
      by (simp only: split_beta' fst_conv)
  qed
  have tail_pair_second:
      "\<And>pair. pair \<in> set ?tail_pair_functions \<Longrightarrow>
        (\<lambda>x. snd (pair x)) \<in> measurable ?H lborel"
  proof -
    fix pair
    assume "pair \<in> set ?tail_pair_functions"
    then obtain j where j: "j \<in> set ks"
      and pair:
        "pair = (\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)).
          (pos_tail j, neg_tail j))"
      by auto
    show "(\<lambda>x. snd (pair x)) \<in> measurable ?H lborel"
      unfolding pair
      using tail_neg_coordinate[OF j]
      by (simp only: split_beta' snd_conv)
  qed
  have head_projection:
      "fst \<in> measurable ?H ?P"
    by (rule measurable_fst)
  have head_pos_raw[measurable]:
      "(\<lambda>x. fst (fst x)) \<in> measurable ?H lborel"
    by (rule measurable_compose[OF head_projection measurable_fst])
  have head_pos_coordinate[measurable]:
      "(\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)). pos_head)
        \<in> measurable ?H lborel"
  proof -
    show ?thesis
      using head_pos_raw by (simp only: split_beta')
  qed
  have head_neg_raw[measurable]:
      "(\<lambda>x. snd (fst x)) \<in> measurable ?H lborel"
    by (rule measurable_compose[OF head_projection measurable_snd])
  have head_neg_coordinate[measurable]:
      "(\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)). neg_head)
        \<in> measurable ?H lborel"
  proof -
    show ?thesis
      using head_neg_raw by (simp only: split_beta')
  qed
  have tail_origin[measurable]:
      "(\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)). neg_head)
        \<in> measurable ?H lborel"
    by (rule head_neg_coordinate)
  have tail_output[measurable]:
      "(\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)).
        target - pos_head + neg_head) \<in> measurable ?H lborel"
  proof -
    have raw:
        "(\<lambda>x. target - fst (fst x) + snd (fst x))
          \<in> measurable ?H lborel"
      by measurable
    show ?thesis
      using raw by (simp only: split_beta')
  qed
  let ?tail_kernel =
    "\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)).
      slp_left_branch_positive_kernel_list_fixed_output R cutoff potential
        terminal_value (map (\<lambda>j. (pos_tail j, neg_tail j)) ks)
        neg_head (target - pos_head + neg_head)"
  have tail_kernel_measurable[measurable]:
      "?tail_kernel \<in> borel_measurable ?H"
  proof -
    note raw =
      slp_left_branch_positive_kernel_list_fixed_output_param_measurable[
        where M = ?H and pair_functions = ?tail_pair_functions,
        OF cutoff_measurable potential_measurable terminal_value_measurable
          tail_origin tail_output tail_pair_first tail_pair_second]
    show ?thesis
      using raw by (simp only: list.map map_map comp_def split_beta')
  qed
  have block_measurable:
      "case_prod
        (slp_positive_branch_block_weight R cutoff potential origin)
        \<in> borel_measurable ?P"
    by (rule slp_positive_branch_block_weight_measurable[OF
          cutoff_measurable potential_measurable])
  let ?block_H =
    "\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)).
      slp_positive_branch_block_weight R cutoff potential origin pos_head
        neg_head"
  have block_on_H[measurable]:
      "?block_H \<in> borel_measurable ?H"
    using measurable_compose[OF head_projection block_measurable]
    by (simp only: comp_def split_beta')
  have factored_measurable:
      "(\<lambda>x. ?C * ?block_H x * ?tail_kernel x)
        \<in> borel_measurable ?H"
    by measurable
  have W_measurable:
      "?W \<in> borel_measurable ?H"
    using factored_measurable
    by (simp only:
        slp_left_branch_positive_kernel_list_fixed_output_Cons split_beta'
        fst_conv snd_conv)
  have T_sigma: "sigma_finite_measure ?T"
    by (rule product.sigma_finite[OF finite_tail])
  interpret T: sigma_finite_measure ?T
    by (rule T_sigma)
  interpret tail_pair: pair_sigma_finite ?T ?T ..
  have split_tail:
      "nn_integral ?H ?W =
        nn_integral ?P
          (\<lambda>head. nn_integral ?Q (\<lambda>tail. ?W (head, tail)))"
  proof -
    note raw = tail_pair.nn_integral_fst[OF W_measurable]
    show ?thesis
      using raw[symmetric] by (simp only: split_beta')
  qed
  have tail_kernel_slice_measurable:
      "(\<lambda>(pos_tail, neg_tail).
        slp_left_branch_positive_kernel_list_fixed_output R cutoff potential
          terminal_value (map (\<lambda>j. (pos_tail j, neg_tail j)) ks)
          neg_head (target - pos_head + neg_head))
        \<in> borel_measurable ?Q"
      for pos_head neg_head
  proof -
    have head_space: "(pos_head, neg_head) \<in> space ?P"
      by (simp only: space_pair_measure space_lborel space_borel
          mem_Times_iff fst_conv snd_conv UNIV_I)
    note raw = measurable_Pair2[OF tail_kernel_measurable head_space]
    show ?thesis
      using raw by (simp only: split_beta' fst_conv snd_conv)
  qed
  have inner_tail:
      "nn_integral ?Q
          (\<lambda>tail. ?W ((pos_head, neg_head), tail)) =
        ?C *
          (slp_positive_branch_block_weight R cutoff potential origin
            pos_head neg_head *
           slp_positive_output_density R cutoff potential
            (\<lambda>x. ennreal (norm (terminal_value x))) (length ks)
            neg_head (target - pos_head + neg_head))"
      for pos_head neg_head
  proof -
    have slice_measurable:
        "(\<lambda>(pos_tail, neg_tail).
          slp_left_branch_positive_kernel_list_fixed_output R cutoff potential
            terminal_value (map (\<lambda>j. (pos_tail j, neg_tail j)) ks)
            neg_head (target - pos_head + neg_head))
          \<in> borel_measurable ?Q"
      by (rule tail_kernel_slice_measurable)
    note pull_scalar = nn_integral_cmult[
      OF slice_measurable,
      where c = "?C *
        slp_positive_branch_block_weight R cutoff potential origin
          pos_head neg_head"]
    show ?thesis
      using pull_scalar Cons.IH[OF tail_distinct]
      by (simp only:
        slp_left_branch_positive_kernel_list_fixed_output_Cons split_beta'
        fst_conv snd_conv mult.assoc)
  qed
  have inner_tail_normalized:
      "nn_integral ?Q
          (\<lambda>tail.
            slp_left_branch_positive_kernel_list_fixed_output R cutoff
              potential terminal_value
              ((pos_head, neg_head) #
                map (\<lambda>j. (fst tail j, snd tail j)) ks)
              origin target) =
        ?C *
          (slp_positive_branch_block_weight R cutoff potential origin
            pos_head neg_head *
           slp_positive_output_density R cutoff potential
            (\<lambda>x. ennreal (norm (terminal_value x))) (length ks)
            neg_head (target - pos_head + neg_head))"
      for pos_head neg_head
    using inner_tail
    by (simp only: split_beta' fst_conv snd_conv case_prod_conv)
  let ?G = "\<lambda>(pos_head, neg_head).
    slp_positive_branch_block_weight R cutoff potential origin pos_head
      neg_head *
    slp_positive_output_density R cutoff potential
      (\<lambda>x. ennreal (norm (terminal_value x))) (length ks) neg_head
      (target - pos_head + neg_head)"
  have terminal_weight_measurable[measurable]:
      "(\<lambda>x. ennreal (norm (terminal_value x)))
        \<in> borel_measurable lborel"
    by measurable
  have density_measurable:
      "case_prod
        (slp_positive_output_density R cutoff potential
          (\<lambda>x. ennreal (norm (terminal_value x))) (length ks))
        \<in> borel_measurable ?P"
    by (rule slp_positive_output_density_joint_measurable[OF
          cutoff_measurable potential_measurable terminal_weight_measurable])
  have density_arguments:
      "(\<lambda>(pos_head, neg_head).
        (neg_head, target - pos_head + neg_head)) \<in> measurable ?P ?P"
    by measurable
  have density_on_head[measurable]:
      "(\<lambda>(pos_head, neg_head).
        slp_positive_output_density R cutoff potential
          (\<lambda>x. ennreal (norm (terminal_value x))) (length ks)
          neg_head (target - pos_head + neg_head))
        \<in> borel_measurable ?P"
    using measurable_compose[OF density_arguments density_measurable]
    by (simp only: comp_def split_beta' fst_conv snd_conv)
  have G_measurable:
      "?G \<in> borel_measurable ?P"
    using block_measurable density_on_head
    by (simp only: case_prod_unfold; measurable)
  have head_value:
      "nn_integral ?P
          (\<lambda>head. nn_integral ?Q (\<lambda>tail. ?W (head, tail))) =
        nn_integral ?P (\<lambda>head. ?C * ?G head)"
  proof (rule nn_integral_cong)
    fix head_coordinates :: "slp_point \<times> slp_point"
    assume "head_coordinates \<in> space ?P"
    obtain pos_value neg_value where head_coordinates:
        "head_coordinates = (pos_value, neg_value)"
      by (cases head_coordinates)
    show "nn_integral ?Q (\<lambda>tail. ?W (head_coordinates, tail)) =
        ?C * ?G head_coordinates"
      unfolding head_coordinates
      apply (simp only: split_beta' fst_conv snd_conv case_prod_conv)
      apply (rule inner_tail_normalized)
      done
  qed
  have factor_head:
      "nn_integral ?P (\<lambda>head. ?C * ?G head) =
        ?C * nn_integral ?P ?G"
    by (rule nn_integral_cmult[OF G_measurable])
  have split_head:
      "nn_integral ?P ?G =
        nn_integral lborel
          (\<lambda>pos_head. nn_integral lborel (\<lambda>neg_head.
            ?G (pos_head, neg_head)))"
  proof -
    note raw = lborel.nn_integral_fst[OF G_measurable]
    show ?thesis
      using raw[symmetric] by (simp only: split_beta')
  qed
  have combined:
      "nn_integral ?U ?f =
        ?C * nn_integral lborel
          (\<lambda>pos_head. nn_integral lborel (\<lambda>neg_head.
            ?G (pos_head, neg_head)))"
    using transported_W split_tail head_value factor_head split_head by simp
  show ?case
    using combined
    by (simp only: list.set list.size add_Suc_right add_0_right
        slp_positive_output_density.simps
        slp_positive_branch_block_weight_def mult.assoc case_prod_conv)
qed

end
