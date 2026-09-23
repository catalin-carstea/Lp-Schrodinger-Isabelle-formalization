theory Inverse_Schrodinger_Lp_Finite_Product_Sum_Merge
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Finite_Product_Flatten"
begin

section \<open>Merging two finite products on a disjoint sum carrier\<close>

lemma slp_distr_PiM_sum_merge:
  fixes I :: "'i set"
    and J :: "'j set"
    and M :: "('i + 'j) \<Rightarrow> 'a measure"
  assumes component_sigma:
      "\<And>k. sigma_finite_measure (M k)"
    and finite_I: "finite I"
    and finite_J: "finite J"
  shows
    "distr
        (PiM I (\<lambda>i. M (Inl i)) \<Otimes>\<^sub>M
          PiM J (\<lambda>j. M (Inr j)))
        (PiM (Inl ` I \<union> Inr ` J) M)
        (\<lambda>(omega, eta). \<lambda>k\<in>Inl ` I \<union> Inr ` J.
          case k of Inl i \<Rightarrow> omega i | Inr j \<Rightarrow> eta j) =
      PiM (Inl ` I \<union> Inr ` J) M"
proof -
  interpret component: sigma_finite_measure "M k" for k
    by (rule component_sigma)
  interpret left_product: product_sigma_finite "\<lambda>i. M (Inl i)"
    by standard
  interpret right_product: product_sigma_finite "\<lambda>j. M (Inr j)"
    by standard
  have left_sigma:
    "sigma_finite_measure (PiM I (\<lambda>i. M (Inl i)))"
  proof -
    interpret left:
      finite_product_sigma_finite "\<lambda>i. M (Inl i)" I
      by standard (rule finite_I)
    show ?thesis
      by standard
  qed
  have right_sigma:
    "sigma_finite_measure (PiM J (\<lambda>j. M (Inr j)))"
  proof -
    interpret right:
      finite_product_sigma_finite "\<lambda>j. M (Inr j)" J
      by standard (rule finite_J)
    show ?thesis
      by standard
  qed
  interpret target: product_sigma_finite M
    by standard

  let ?K = "Inl ` I \<union> Inr ` J"
  let ?Left = "PiM I (\<lambda>i. M (Inl i))"
  let ?Right = "PiM J (\<lambda>j. M (Inr j))"
  let ?Source = "?Left \<Otimes>\<^sub>M ?Right"
  let ?Target = "PiM ?K M"
  let ?F = "\<lambda>(omega, eta). \<lambda>k\<in>?K.
    case k of Inl i \<Rightarrow> omega i | Inr j \<Rightarrow> eta j"

  have map_measurable: "?F \<in> measurable ?Source ?Target"
  proof (rule measurable_PiM_single')
    fix k
    assume k_in: "k \<in> ?K"
    show "(\<lambda>x. ?F x k) \<in> measurable ?Source (M k)"
    proof (cases k)
      case (Inl i)
      have i_in: "i \<in> I"
        using k_in Inl by auto
      have fst_measurable:
        "fst \<in> measurable ?Source ?Left"
        by measurable
      have component_measurable:
        "(\<lambda>omega. omega i) \<in> measurable ?Left (M (Inl i))"
        by (rule measurable_component_singleton[OF i_in])
      have composed:
        "(\<lambda>x. fst x i) \<in> measurable ?Source (M (Inl i))"
        using measurable_compose[OF fst_measurable component_measurable]
        by (simp only: comp_def)
      have component_eq:
        "(\<lambda>x. ?F x (Inl i)) = (\<lambda>x. fst x i)"
        apply (rule ext)
        apply (case_tac x)
        using i_in
        apply simp
        done
      show ?thesis
        apply (subst Inl)
        apply (subst component_eq)
        apply (subst Inl)
        apply (rule composed)
        done
    next
      case (Inr j)
      have j_in: "j \<in> J"
        using k_in Inr by auto
      have snd_measurable:
        "snd \<in> measurable ?Source ?Right"
        by measurable
      have component_measurable:
        "(\<lambda>eta. eta j) \<in> measurable ?Right (M (Inr j))"
        by (rule measurable_component_singleton[OF j_in])
      have composed:
        "(\<lambda>x. snd x j) \<in> measurable ?Source (M (Inr j))"
        using measurable_compose[OF snd_measurable component_measurable]
        by (simp only: comp_def)
      have component_eq:
        "(\<lambda>x. ?F x (Inr j)) = (\<lambda>x. snd x j)"
        apply (rule ext)
        apply (case_tac x)
        using j_in
        apply simp
        done
      show ?thesis
        apply (subst Inr)
        apply (subst component_eq)
        apply (subst Inr)
        apply (rule composed)
        done
    qed
  next
    show "?F \<in> space ?Source \<rightarrow> PiE ?K (\<lambda>k. space (M k))"
    proof (rule funcsetI)
      fix x
      assume x_space: "x \<in> space ?Source"
      obtain omega eta where x_pair: "x = (omega, eta)"
        by (cases x)
      have omega_space: "omega \<in> space ?Left"
        using x_space by (simp add: x_pair space_pair_measure)
      have eta_space: "eta \<in> space ?Right"
        using x_space by (simp add: x_pair space_pair_measure)
      show "?F x \<in> PiE ?K (\<lambda>k. space (M k))"
      proof (rule PiE_I)
        fix k
        assume k_in: "k \<in> ?K"
        show "?F x k \<in> space (M k)"
        proof (cases k)
          case (Inl i)
          have i_in: "i \<in> I"
            using k_in Inl by auto
          have omega_i: "omega i \<in> space (M (Inl i))"
            using omega_space i_in
            by (simp add: space_PiM PiE_iff)
          show ?thesis
            using i_in omega_i Inl by (simp add: x_pair)
        next
          case (Inr j)
          have j_in: "j \<in> J"
            using k_in Inr by auto
          have eta_j: "eta j \<in> space (M (Inr j))"
            using eta_space j_in
            by (simp add: space_PiM PiE_iff)
          show ?thesis
            using j_in eta_j Inr by (simp add: x_pair)
        qed
      next
        fix k
        assume k_not: "k \<notin> ?K"
        show "?F x k = undefined"
          using k_not by (simp add: x_pair)
      qed
    qed
  qed

  show ?thesis
  proof (rule target.PiM_eqI)
    show "finite ?K"
      using finite_I finite_J by simp
    fix A
    assume A_sets: "\<And>k. k \<in> ?K \<Longrightarrow> A k \<in> sets (M k)"
    have target_rectangle: "PiE ?K A \<in> sets ?Target"
      by (rule sets_PiM_I_finite)
        (use finite_I finite_J A_sets in auto)
    have A_space: "A k \<subseteq> space (M k)" if "k \<in> ?K" for k
      by (rule sets.sets_into_space[OF A_sets[OF that]])
    have preimage:
      "?F -` PiE ?K A \<inter> space ?Source =
        PiE I (\<lambda>i. A (Inl i)) \<times> PiE J (\<lambda>j. A (Inr j))"
    proof (rule set_eqI)
      fix x :: "('i \<Rightarrow> 'a) \<times> ('j \<Rightarrow> 'a)"
      obtain omega eta where x_pair: "x = (omega, eta)"
        by (cases x)
      show "x \<in> ?F -` PiE ?K A \<inter> space ?Source \<longleftrightarrow>
          x \<in> PiE I (\<lambda>i. A (Inl i)) \<times>
            PiE J (\<lambda>j. A (Inr j))"
      proof
        assume x_left:
          "x \<in> ?F -` PiE ?K A \<inter> space ?Source"
        have mapped: "?F x \<in> PiE ?K A"
          using IntD1[OF x_left] unfolding vimage_def by simp
        have omega_source:
          "omega \<in> PiE I (\<lambda>i. space (M (Inl i)))"
          using IntD2[OF x_left]
          by (simp add: x_pair space_pair_measure space_PiM)
        have eta_source:
          "eta \<in> PiE J (\<lambda>j. space (M (Inr j)))"
          using IntD2[OF x_left]
          by (simp add: x_pair space_pair_measure space_PiM)
        have omega_A: "omega \<in> PiE I (\<lambda>i. A (Inl i))"
        proof (rule PiE_I)
          fix i
          assume i_in: "i \<in> I"
          have inl_in: "Inl i \<in> ?K"
            using i_in by simp
          have mapped_i: "?F x (Inl i) \<in> A (Inl i)"
            by (rule PiE_mem[OF mapped inl_in])
          show "omega i \<in> A (Inl i)"
            using mapped_i i_in by (simp add: x_pair)
        next
          fix i
          assume i_not: "i \<notin> I"
          have omega_ext: "omega \<in> extensional I"
            using omega_source by (simp only: PiE_iff)
          show "omega i = undefined"
            by (rule extensional_arb[OF omega_ext i_not])
        qed
        have eta_A: "eta \<in> PiE J (\<lambda>j. A (Inr j))"
        proof (rule PiE_I)
          fix j
          assume j_in: "j \<in> J"
          have inr_in: "Inr j \<in> ?K"
            using j_in by simp
          have mapped_j: "?F x (Inr j) \<in> A (Inr j)"
            by (rule PiE_mem[OF mapped inr_in])
          show "eta j \<in> A (Inr j)"
            using mapped_j j_in by (simp add: x_pair)
        next
          fix j
          assume j_not: "j \<notin> J"
          have eta_ext: "eta \<in> extensional J"
            using eta_source by (simp only: PiE_iff)
          show "eta j = undefined"
            by (rule extensional_arb[OF eta_ext j_not])
        qed
        show "x \<in> PiE I (\<lambda>i. A (Inl i)) \<times>
            PiE J (\<lambda>j. A (Inr j))"
          using omega_A eta_A by (simp add: x_pair)
      next
        assume x_right:
          "x \<in> PiE I (\<lambda>i. A (Inl i)) \<times>
            PiE J (\<lambda>j. A (Inr j))"
        have omega_A: "omega \<in> PiE I (\<lambda>i. A (Inl i))"
          using x_right by (simp add: x_pair)
        have eta_A: "eta \<in> PiE J (\<lambda>j. A (Inr j))"
          using x_right by (simp add: x_pair)
        have omega_source:
          "omega \<in> PiE I (\<lambda>i. space (M (Inl i)))"
        proof (rule PiE_I)
          fix i
          assume i_in: "i \<in> I"
          have omega_i: "omega i \<in> A (Inl i)"
            by (rule PiE_mem[OF omega_A i_in])
          have inl_in: "Inl i \<in> ?K"
            using i_in by simp
          show "omega i \<in> space (M (Inl i))"
            by (rule subsetD[OF A_space[OF inl_in] omega_i])
        next
          fix i
          assume i_not: "i \<notin> I"
          have omega_ext: "omega \<in> extensional I"
            using omega_A by (simp only: PiE_iff)
          show "omega i = undefined"
            by (rule extensional_arb[OF omega_ext i_not])
        qed
        have eta_source:
          "eta \<in> PiE J (\<lambda>j. space (M (Inr j)))"
        proof (rule PiE_I)
          fix j
          assume j_in: "j \<in> J"
          have eta_j: "eta j \<in> A (Inr j)"
            by (rule PiE_mem[OF eta_A j_in])
          have inr_in: "Inr j \<in> ?K"
            using j_in by simp
          show "eta j \<in> space (M (Inr j))"
            by (rule subsetD[OF A_space[OF inr_in] eta_j])
        next
          fix j
          assume j_not: "j \<notin> J"
          have eta_ext: "eta \<in> extensional J"
            using eta_A by (simp only: PiE_iff)
          show "eta j = undefined"
            by (rule extensional_arb[OF eta_ext j_not])
        qed
        have x_source: "x \<in> space ?Source"
          using omega_source eta_source
          by (simp add: x_pair space_pair_measure space_PiM)
        have mapped: "?F x \<in> PiE ?K A"
        proof (rule PiE_I)
          fix k
          assume k_in: "k \<in> ?K"
          show "?F x k \<in> A k"
          proof (cases k)
            case (Inl i)
            have i_in: "i \<in> I"
              using k_in Inl by auto
            have omega_i: "omega i \<in> A (Inl i)"
              by (rule PiE_mem[OF omega_A i_in])
            show ?thesis
              using omega_i i_in Inl by (simp add: x_pair)
          next
            case (Inr j)
            have j_in: "j \<in> J"
              using k_in Inr by auto
            have eta_j: "eta j \<in> A (Inr j)"
              by (rule PiE_mem[OF eta_A j_in])
            show ?thesis
              using eta_j j_in Inr by (simp add: x_pair)
          qed
        next
          fix k
          assume k_not: "k \<notin> ?K"
          show "?F x k = undefined"
            using k_not by (simp add: x_pair)
        qed
        show "x \<in> ?F -` PiE ?K A \<inter> space ?Source"
        proof (rule IntI)
          show "x \<in> ?F -` PiE ?K A"
            unfolding vimage_def using mapped by simp
          show "x \<in> space ?Source"
            by (rule x_source)
        qed
      qed
    qed
    have left_rectangle:
      "PiE I (\<lambda>i. A (Inl i)) \<in> sets ?Left"
      by (rule sets_PiM_I_finite[OF finite_I])
        (use A_sets in auto)
    have right_rectangle:
      "PiE J (\<lambda>j. A (Inr j)) \<in> sets ?Right"
      by (rule sets_PiM_I_finite[OF finite_J])
        (use A_sets in auto)
    have left_measure:
      "emeasure ?Left (PiE I (\<lambda>i. A (Inl i))) =
        (\<Prod>i\<in>I. emeasure (M (Inl i)) (A (Inl i)))"
      by (rule left_product.emeasure_PiM[OF finite_I])
        (use A_sets in auto)
    have right_measure:
      "emeasure ?Right (PiE J (\<lambda>j. A (Inr j))) =
        (\<Prod>j\<in>J. emeasure (M (Inr j)) (A (Inr j)))"
      by (rule right_product.emeasure_PiM[OF finite_J])
        (use A_sets in auto)
    have source_rectangle:
      "emeasure ?Source
          (PiE I (\<lambda>i. A (Inl i)) \<times>
            PiE J (\<lambda>j. A (Inr j))) =
        emeasure ?Left (PiE I (\<lambda>i. A (Inl i))) *
          emeasure ?Right (PiE J (\<lambda>j. A (Inr j)))"
      by (rule sigma_finite_measure.emeasure_pair_measure_Times)
        (rule right_sigma, rule left_rectangle, rule right_rectangle)
    have left_inj: "inj_on Inl I"
      by (rule inj_onI) simp
    have right_inj: "inj_on Inr J"
      by (rule inj_onI) simp
    have disjoint: "Inl ` I \<inter> Inr ` J = {}"
      by auto
    have target_product:
      "(\<Prod>i\<in>I. emeasure (M (Inl i)) (A (Inl i))) *
          (\<Prod>j\<in>J. emeasure (M (Inr j)) (A (Inr j))) =
        (\<Prod>k\<in>?K. emeasure (M k) (A k))"
      using finite_I finite_J disjoint
      by (simp add: prod.union_disjoint prod.reindex[OF left_inj]
          prod.reindex[OF right_inj])
    show
      "emeasure (distr ?Source ?Target ?F) (PiE ?K A) =
        (\<Prod>k\<in>?K. emeasure (M k) (A k))"
      by (subst emeasure_distr[OF map_measurable target_rectangle])
        (simp add: preimage source_rectangle
          left_rectangle right_rectangle left_measure right_measure
          target_product)
  qed simp_all
qed

end
