theory Inverse_Schrodinger_Lp_Finite_Product_Flatten
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Finite_Product_Componentwise_Transport"
begin

section \<open>Flattening a finite nested product measure\<close>

lemma slp_distr_PiM_nested_flatten:
  fixes I :: "'i set"
    and J :: "'j set"
    and M :: "('i \<times> 'j) \<Rightarrow> 'a measure"
  assumes component_sigma:
      "\<And>ij. sigma_finite_measure (M ij)"
    and finite_I: "finite I"
    and finite_J: "finite J"
  shows
    "distr
        (PiM I (\<lambda>i. PiM J (\<lambda>j. M (i,j))))
        (PiM (I \<times> J) M)
        (\<lambda>omega. \<lambda>ij\<in>I \<times> J.
          omega (fst ij) (snd ij)) =
      PiM (I \<times> J) M"
proof -
  interpret component: sigma_finite_measure "M ij" for ij
    by (rule component_sigma)
  interpret target: product_sigma_finite M
    by standard
  interpret inner_product:
    product_sigma_finite "\<lambda>j. M (i,j)" for i
    by standard
  have inner_sigma:
    "sigma_finite_measure (PiM J (\<lambda>j. M (i,j)))"
    for i
  proof -
    interpret inner:
      finite_product_sigma_finite "\<lambda>j. M (i,j)" J
      by standard (rule finite_J)
    show ?thesis
      by standard
  qed
  interpret inner_measure:
    sigma_finite_measure "PiM J (\<lambda>j. M (i,j))" for i
    by (rule inner_sigma)
  interpret nested:
    product_sigma_finite "\<lambda>i. PiM J (\<lambda>j. M (i,j))"
    by standard

  let ?Nested = "PiM I (\<lambda>i. PiM J (\<lambda>j. M (i,j)))"
  let ?Flat = "PiM (I \<times> J) M"
  let ?F = "\<lambda>omega. \<lambda>ij\<in>I \<times> J.
    omega (fst ij) (snd ij)"

  have map_measurable: "?F \<in> measurable ?Nested ?Flat"
  proof (rule measurable_PiM_single')
    fix ij
    assume ij_in: "ij \<in> I \<times> J"
    have outer_component:
      "(\<lambda>omega. omega (fst ij)) \<in>
        measurable ?Nested (PiM J (\<lambda>j. M (fst ij,j)))"
      by (rule measurable_component_singleton)
        (use ij_in in auto)
    have inner_component:
      "(\<lambda>eta. eta (snd ij)) \<in>
        measurable (PiM J (\<lambda>j. M (fst ij,j))) (M ij)"
    proof -
      have raw:
        "(\<lambda>eta. eta (snd ij)) \<in>
          measurable (PiM J (\<lambda>j. M (fst ij,j)))
            (M (fst ij, snd ij))"
        by (rule measurable_component_singleton)
          (use ij_in in auto)
      show ?thesis
        using raw by (simp only: prod.collapse)
    qed
    have composed:
      "(\<lambda>omega. omega (fst ij) (snd ij)) \<in>
        measurable ?Nested (M ij)"
      using measurable_compose[OF outer_component inner_component]
      by (simp only: comp_def prod.collapse)
    show "(\<lambda>omega. ?F omega ij) \<in> measurable ?Nested (M ij)"
      using composed ij_in by simp
  next
    show "?F \<in> space ?Nested \<rightarrow>
      PiE (I \<times> J) (\<lambda>ij. space (M ij))"
      using inner_sigma
      by (auto simp: space_PiM PiE_iff)
  qed

  show ?thesis
  proof (rule target.PiM_eqI)
    show "finite (I \<times> J)"
      by (rule finite_cartesian_product[OF finite_I finite_J])
    fix A
    assume A_sets:
      "\<And>ij. ij \<in> I \<times> J \<Longrightarrow> A ij \<in> sets (M ij)"
    have target_rectangle:
      "PiE (I \<times> J) A \<in> sets ?Flat"
      by (rule sets_PiM_I_finite)
        (rule finite_cartesian_product[OF finite_I finite_J], rule A_sets)
    have A_space:
      "A (i,j) \<subseteq> space (M (i,j))"
      if "i \<in> I" "j \<in> J"
      for i j
      by (rule sets.sets_into_space)
        (rule A_sets, use that in auto)
    have preimage:
      "?F -` PiE (I \<times> J) A \<inter> space ?Nested =
        PiE I (\<lambda>i. PiE J (\<lambda>j. A (i,j)))"
    proof (rule set_eqI)
      fix omega
      show "omega \<in> ?F -` PiE (I \<times> J) A \<inter> space ?Nested \<longleftrightarrow>
          omega \<in> PiE I (\<lambda>i. PiE J (\<lambda>j. A (i,j)))"
      proof
        assume omega_left:
          "omega \<in> ?F -` PiE (I \<times> J) A \<inter> space ?Nested"
        have mapped: "?F omega \<in> PiE (I \<times> J) A"
          using IntD1[OF omega_left]
          unfolding vimage_def by simp
        have source_nested:
          "omega \<in> PiE I
            (\<lambda>i. PiE J (\<lambda>j. space (M (i,j))))"
          using IntD2[OF omega_left] unfolding space_PiM .
        show "omega \<in> PiE I (\<lambda>i. PiE J (\<lambda>j. A (i,j)))"
        proof (rule PiE_I)
          fix i
          assume i_in: "i \<in> I"
          have source_i:
            "omega i \<in> PiE J (\<lambda>j. space (M (i,j)))"
            by (rule PiE_mem[OF source_nested i_in])
          show "omega i \<in> PiE J (\<lambda>j. A (i,j))"
          proof (rule PiE_I)
            fix j
            assume j_in: "j \<in> J"
            have pair_in: "(i,j) \<in> I \<times> J"
              using i_in j_in
              by (simp only: mem_Times_iff fst_conv snd_conv)
            have mapped_value: "?F omega (i,j) \<in> A (i,j)"
              by (rule PiE_mem[OF mapped pair_in])
            have restrict_value: "?F omega (i,j) = omega i j"
              using pair_in
              by (simp only: restrict_apply if_True fst_conv snd_conv)
            show "omega i j \<in> A (i,j)"
              using mapped_value by (simp only: restrict_value)
          next
            fix j
            assume j_not: "j \<notin> J"
            have inner_ext: "omega i \<in> extensional J"
              using source_i by (simp only: PiE_iff)
            show "omega i j = undefined"
              by (rule extensional_arb[OF inner_ext j_not])
          qed
        next
          fix i
          assume i_not: "i \<notin> I"
          have outer_ext: "omega \<in> extensional I"
            using source_nested by (simp only: PiE_iff)
          show "omega i = undefined"
            by (rule extensional_arb[OF outer_ext i_not])
        qed
      next
        assume omega_right:
          "omega \<in> PiE I (\<lambda>i. PiE J (\<lambda>j. A (i,j)))"
        have inner_subset:
          "PiE J (\<lambda>j. A (i,j)) \<subseteq>
            space (PiM J (\<lambda>j. M (i,j)))"
          if "i \<in> I"
          for i
          unfolding space_PiM
          by (rule PiE_mono) (rule A_space[OF that])
        have outer_subset:
          "PiE I (\<lambda>i. PiE J (\<lambda>j. A (i,j))) \<subseteq>
            space ?Nested"
          unfolding space_PiM
        proof (rule PiE_mono)
          fix i
          assume i_in: "i \<in> I"
          show "PiE J (\<lambda>j. A (i,j)) \<subseteq>
              PiE J (\<lambda>j. space (M (i,j)))"
            using inner_subset[OF i_in]
            by (simp only: space_PiM)
        qed
        have omega_space: "omega \<in> space ?Nested"
          by (rule subsetD[OF outer_subset omega_right])
        have mapped: "?F omega \<in> PiE (I \<times> J) A"
        proof (rule PiE_I)
          fix ij
          assume ij_in: "ij \<in> I \<times> J"
          have fst_in: "fst ij \<in> I"
            using ij_in by (simp only: mem_Times_iff)
          have snd_in: "snd ij \<in> J"
            using ij_in by (simp only: mem_Times_iff)
          have outer_value:
            "omega (fst ij) \<in>
              PiE J (\<lambda>j. A (fst ij,j))"
            by (rule PiE_mem[OF omega_right fst_in])
          have inner_value:
            "omega (fst ij) (snd ij) \<in> A (fst ij, snd ij)"
            by (rule PiE_mem[OF outer_value snd_in])
          have restrict_value:
            "?F omega ij = omega (fst ij) (snd ij)"
            using ij_in
            by (simp only: restrict_apply if_True)
          show "?F omega ij \<in> A ij"
            using inner_value restrict_value
            by (simp only: prod.collapse)
        next
          fix ij
          assume ij_not: "ij \<notin> I \<times> J"
          show "?F omega ij = undefined"
            by (simp only: restrict_apply if_False ij_not)
        qed
        show "omega \<in> ?F -` PiE (I \<times> J) A \<inter> space ?Nested"
        proof (rule IntI)
          show "omega \<in> ?F -` PiE (I \<times> J) A"
            unfolding vimage_def using mapped by simp
          show "omega \<in> space ?Nested"
            by (rule omega_space)
        qed
      qed
    qed
    have inner_rectangle_sets:
      "PiE J (\<lambda>j. A (i,j)) \<in>
        sets (PiM J (\<lambda>j. M (i,j)))"
      if "i \<in> I"
      for i
    proof (rule sets_PiM_I_finite[OF finite_J])
      fix j
      assume j_in: "j \<in> J"
      have pair_in: "(i,j) \<in> I \<times> J"
        using that j_in
        by (simp only: mem_Times_iff fst_conv snd_conv)
      show "A (i,j) \<in> sets (M (i,j))"
        by (rule A_sets[OF pair_in])
    qed
    have distr_rectangle:
      "emeasure (distr ?Nested ?Flat ?F) (PiE (I \<times> J) A) =
        emeasure ?Nested
          (PiE I (\<lambda>i. PiE J (\<lambda>j. A (i,j))))"
      by (subst emeasure_distr[OF map_measurable target_rectangle])
        (simp only: preimage)
    have outer_rectangle:
      "emeasure ?Nested
          (PiE I (\<lambda>i. PiE J (\<lambda>j. A (i,j)))) =
        (\<Prod>i\<in>I.
          emeasure (PiM J (\<lambda>j. M (i,j)))
            (PiE J (\<lambda>j. A (i,j))))"
      by (rule nested.emeasure_PiM[OF finite_I])
        (rule inner_rectangle_sets)
    have inner_rectangle:
      "emeasure (PiM J (\<lambda>j. M (i,j)))
          (PiE J (\<lambda>j. A (i,j))) =
        (\<Prod>j\<in>J. emeasure (M (i,j)) (A (i,j)))"
      if "i \<in> I"
      for i
    proof (rule inner_product.emeasure_PiM[OF finite_J])
      fix j
      assume j_in: "j \<in> J"
      have pair_in: "(i,j) \<in> I \<times> J"
        using that j_in
        by (simp only: mem_Times_iff fst_conv snd_conv)
      show "A (i,j) \<in> sets (M (i,j))"
        by (rule A_sets[OF pair_in])
    qed
    have nested_product:
      "(\<Prod>i\<in>I.
          emeasure (PiM J (\<lambda>j. M (i,j)))
            (PiE J (\<lambda>j. A (i,j)))) =
        (\<Prod>i\<in>I. \<Prod>j\<in>J.
          emeasure (M (i,j)) (A (i,j)))"
      by (rule prod.cong) (simp_all add: inner_rectangle)
    have flat_product:
      "(\<Prod>i\<in>I. \<Prod>j\<in>J.
          emeasure (M (i,j)) (A (i,j))) =
        (\<Prod>ij\<in>I \<times> J. emeasure (M ij) (A ij))"
      by (simp only: prod.cartesian_product case_prod_unfold prod.collapse)
    show
      "emeasure (distr ?Nested ?Flat ?F) (PiE (I \<times> J) A) =
        (\<Prod>ij\<in>I \<times> J. emeasure (M ij) (A ij))"
      by (rule trans[OF distr_rectangle])
        (rule trans[OF outer_rectangle trans[OF nested_product flat_product]])
  qed simp_all
qed

end
