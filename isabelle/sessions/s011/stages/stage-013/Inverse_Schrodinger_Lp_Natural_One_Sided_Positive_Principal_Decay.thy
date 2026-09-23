theory Inverse_Schrodinger_Lp_Natural_One_Sided_Positive_Principal_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_One_Sided_Principal_Integrability"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_One_Sided_Active_Phase"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Finite_Product_Pair_Insert_Integrable"
begin

section \<open>Sigma-finite product association\<close>

lemma slp_product_assoc_integrable_iff:
  fixes M :: "'a measure" and N :: "'b measure" and P :: "'c measure"
    and f :: "(('a \<times> 'b) \<times> 'c) \<Rightarrow>
      'd::{banach, second_countable_topology}"
  assumes M_sigma: "sigma_finite_measure M"
    and N_sigma: "sigma_finite_measure N"
    and P_sigma: "sigma_finite_measure P"
  shows "integrable ((M \<Otimes>\<^sub>M N) \<Otimes>\<^sub>M P) f \<longleftrightarrow>
    integrable (M \<Otimes>\<^sub>M (N \<Otimes>\<^sub>M P))
      (\<lambda>(x, (y, z)). f ((x, y), z))"
proof -
  let ?L = "(M \<Otimes>\<^sub>M N) \<Otimes>\<^sub>M P"
  let ?R = "M \<Otimes>\<^sub>M (N \<Otimes>\<^sub>M P)"
  let ?g = "\<lambda>(x, (y, z)). f ((x, y), z)"
  interpret M: sigma_finite_measure M by (rule M_sigma)
  interpret N: sigma_finite_measure N by (rule N_sigma)
  interpret P: sigma_finite_measure P by (rule P_sigma)
  interpret MN: pair_sigma_finite M N ..
  interpret NP: pair_sigma_finite N P ..
  have assoc_measurable:
    "(\<lambda>(x, (y, z)). ((x, y), z)) \<in> measurable ?R ?L"
    by measurable
  have unassoc_measurable:
    "(\<lambda>((x, y), z). (x, (y, z))) \<in> measurable ?L ?R"
  proof -
    have raw:
      "(\<lambda>w. (fst (fst w), (snd (fst w), snd w)))
        \<in> measurable ?L ?R"
      by (rule measurable_Pair; measurable)
    show ?thesis using raw by (simp only: split_beta')
  qed
  have measurable_iff:
    "f \<in> borel_measurable ?L \<longleftrightarrow> ?g \<in> borel_measurable ?R"
  proof
    assume f_measurable: "f \<in> borel_measurable ?L"
    have "f \<circ> (\<lambda>(x, (y, z)). ((x, y), z))
        \<in> borel_measurable ?R"
      by (rule measurable_comp[OF assoc_measurable f_measurable])
    then show "?g \<in> borel_measurable ?R"
      by (simp only: comp_def split_beta')
  next
    assume g_measurable: "?g \<in> borel_measurable ?R"
    have "?g \<circ> (\<lambda>((x, y), z). (x, (y, z)))
        \<in> borel_measurable ?L"
      by (rule measurable_comp[OF unassoc_measurable g_measurable])
    moreover have
      "?g \<circ> (\<lambda>((x, y), z). (x, (y, z))) = f"
      by (rule ext) (auto split: prod.split)
    ultimately show "f \<in> borel_measurable ?L" by simp
  qed
  have mass_eq:
    "nn_integral ?L (\<lambda>w. ennreal (norm (f w))) =
      nn_integral ?R (\<lambda>w. ennreal (norm (?g w)))"
    if f_measurable: "f \<in> borel_measurable ?L"
  proof -
    have f_norm_measurable:
      "(\<lambda>w. ennreal (norm (f w))) \<in> borel_measurable ?L"
      using f_measurable by measurable
    have g_measurable: "?g \<in> borel_measurable ?R"
      using measurable_iff f_measurable by blast
    have g_norm_measurable:
      "(\<lambda>w. ennreal (norm (?g w))) \<in> borel_measurable ?R"
      using g_measurable by measurable
    have left_once:
      "nn_integral ?L (\<lambda>w. ennreal (norm (f w))) =
        (\<integral>\<^sup>+xy. \<integral>\<^sup>+z. ennreal (norm (f (xy, z))) \<partial>P
          \<partial>(M \<Otimes>\<^sub>M N))"
      using P.nn_integral_fst[OF f_norm_measurable, symmetric]
      by (simp only: split_beta')
    have left_inner_measurable:
      "(\<lambda>xy. \<integral>\<^sup>+z. ennreal (norm (f (xy, z))) \<partial>P)
        \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
      by (rule P.borel_measurable_nn_integral) (use f_norm_measurable in measurable)
    have left_twice:
      "(\<integral>\<^sup>+xy. \<integral>\<^sup>+z. ennreal (norm (f (xy, z))) \<partial>P
          \<partial>(M \<Otimes>\<^sub>M N)) =
        (\<integral>\<^sup>+x. \<integral>\<^sup>+y. \<integral>\<^sup>+z.
          ennreal (norm (f ((x, y), z))) \<partial>P \<partial>N \<partial>M)"
      using N.nn_integral_fst[OF left_inner_measurable]
      by (simp only: split_beta')
    have right_once:
      "nn_integral ?R (\<lambda>w. ennreal (norm (?g w))) =
        (\<integral>\<^sup>+x. \<integral>\<^sup>+yz.
          ennreal (norm (?g (x, yz))) \<partial>(N \<Otimes>\<^sub>M P) \<partial>M)"
      using NP.nn_integral_fst[OF g_norm_measurable, symmetric]
      by (simp only: split_beta')
    have right_inner:
      "(\<integral>\<^sup>+yz. ennreal (norm (?g (x, yz))) \<partial>(N \<Otimes>\<^sub>M P)) =
        (\<integral>\<^sup>+y. \<integral>\<^sup>+z. ennreal (norm (f ((x, y), z))) \<partial>P \<partial>N)"
      if x_space: "x \<in> space M" for x
    proof -
      have fiber_measurable:
        "(\<lambda>yz. ennreal (norm (?g (x, yz))))
          \<in> borel_measurable (N \<Otimes>\<^sub>M P)"
        by (rule measurable_Pair2[OF g_norm_measurable x_space])
      have raw:
        "(\<integral>\<^sup>+y. \<integral>\<^sup>+z. ennreal (norm (?g (x, (y, z)))) \<partial>P \<partial>N) =
          (\<integral>\<^sup>+yz. ennreal (norm (?g (x, yz))) \<partial>(N \<Otimes>\<^sub>M P))"
        by (rule P.nn_integral_fst[OF fiber_measurable])
      show ?thesis using raw by (simp add: case_prod_unfold)
    qed
    have right_twice:
      "(\<integral>\<^sup>+x. \<integral>\<^sup>+yz.
          ennreal (norm (?g (x, yz))) \<partial>(N \<Otimes>\<^sub>M P) \<partial>M) =
        (\<integral>\<^sup>+x. \<integral>\<^sup>+y. \<integral>\<^sup>+z.
          ennreal (norm (f ((x, y), z))) \<partial>P \<partial>N \<partial>M)"
      by (rule nn_integral_cong) (rule right_inner)
    show ?thesis
      using left_once left_twice right_once right_twice by simp
  qed
  show ?thesis
  proof
    assume f_integrable: "integrable ?L f"
    have f_measurable: "f \<in> borel_measurable ?L"
      using f_integrable by measurable
    have f_mass: "nn_integral ?L (\<lambda>w. ennreal (norm (f w))) < top_class.top"
      using f_integrable by (simp add: integrable_iff_bounded)
    have g_measurable: "?g \<in> borel_measurable ?R"
      using measurable_iff f_measurable by blast
    have g_mass: "nn_integral ?R (\<lambda>w. ennreal (norm (?g w))) < top_class.top"
      using mass_eq[OF f_measurable] f_mass by simp
    show "integrable ?R ?g"
      using g_measurable g_mass by (simp add: integrable_iff_bounded)
  next
    assume g_integrable: "integrable ?R ?g"
    have g_measurable: "?g \<in> borel_measurable ?R"
      using g_integrable by measurable
    have f_measurable: "f \<in> borel_measurable ?L"
      using measurable_iff g_measurable by blast
    have g_mass: "nn_integral ?R (\<lambda>w. ennreal (norm (?g w))) < top_class.top"
      using g_integrable by (simp add: integrable_iff_bounded)
    have f_mass: "nn_integral ?L (\<lambda>w. ennreal (norm (f w))) < top_class.top"
      using mass_eq[OF f_measurable] g_mass by simp
    show "integrable ?L f"
      using f_measurable f_mass by (simp add: integrable_iff_bounded)
  qed
qed

lemma slp_product_assoc_integral:
  fixes M :: "'a measure" and N :: "'b measure" and P :: "'c measure"
    and f :: "(('a \<times> 'b) \<times> 'c) \<Rightarrow>
      'd::{banach, second_countable_topology}"
  assumes M_sigma: "sigma_finite_measure M"
    and N_sigma: "sigma_finite_measure N"
    and P_sigma: "sigma_finite_measure P"
    and f_integrable: "integrable ((M \<Otimes>\<^sub>M N) \<Otimes>\<^sub>M P) f"
  shows "integral\<^sup>L ((M \<Otimes>\<^sub>M N) \<Otimes>\<^sub>M P) f =
    integral\<^sup>L (M \<Otimes>\<^sub>M (N \<Otimes>\<^sub>M P))
      (\<lambda>(x, (y, z)). f ((x, y), z))"
proof -
  let ?L = "(M \<Otimes>\<^sub>M N) \<Otimes>\<^sub>M P"
  let ?R = "M \<Otimes>\<^sub>M (N \<Otimes>\<^sub>M P)"
  let ?g = "\<lambda>(x, (y, z)). f ((x, y), z)"
  interpret M: sigma_finite_measure M by (rule M_sigma)
  interpret N: sigma_finite_measure N by (rule N_sigma)
  interpret P: sigma_finite_measure P by (rule P_sigma)
  interpret MN: pair_sigma_finite M N ..
  interpret NP: pair_sigma_finite N P ..
  interpret MN_P: pair_sigma_finite "M \<Otimes>\<^sub>M N" P ..
  interpret M_NP: pair_sigma_finite M "N \<Otimes>\<^sub>M P" ..
  have g_integrable: "integrable ?R ?g"
    using slp_product_assoc_integrable_iff[OF M_sigma N_sigma P_sigma,
      of f] f_integrable by blast
  let ?H = "\<lambda>xy. integral\<^sup>L P (\<lambda>z. f (xy, z))"
  have H_integrable: "integrable (M \<Otimes>\<^sub>M N) ?H"
    by (rule MN_P.integrable_fst'[OF f_integrable])
  have left_nested:
    "integral\<^sup>L ?L f =
      (\<integral>x. \<integral>y. \<integral>z. f ((x, y), z) \<partial>P \<partial>N \<partial>M)"
  proof -
    have outer:
      "(\<integral>xy. ?H xy \<partial>(M \<Otimes>\<^sub>M N)) = integral\<^sup>L ?L f"
      by (rule MN_P.integral_fst'[OF f_integrable])
    have inner:
      "(\<integral>x. \<integral>y. ?H (x, y) \<partial>N \<partial>M) =
        (\<integral>xy. ?H xy \<partial>(M \<Otimes>\<^sub>M N))"
      by (rule MN.integral_fst'[OF H_integrable])
    show ?thesis using outer inner by (simp only: split_beta')
  qed
  have right_outer:
    "(\<integral>x. integral\<^sup>L (N \<Otimes>\<^sub>M P) (\<lambda>yz. ?g (x, yz)) \<partial>M) =
      integral\<^sup>L ?R ?g"
    by (rule M_NP.integral_fst'[OF g_integrable])
  have fiber_integrable:
    "AE x in M. integrable (N \<Otimes>\<^sub>M P) (\<lambda>yz. ?g (x, yz))"
    by (rule M_NP.AE_integrable_fst'[OF g_integrable])
  have right_outer_integrable:
    "integrable M
      (\<lambda>x. integral\<^sup>L (N \<Otimes>\<^sub>M P) (\<lambda>yz. ?g (x, yz)))"
    by (rule M_NP.integrable_fst'[OF g_integrable])
  have triple_outer_integrable:
    "integrable M (\<lambda>x. \<integral>y. \<integral>z. f ((x, y), z) \<partial>P \<partial>N)"
    using MN.integrable_fst'[OF H_integrable]
    by (simp only: split_beta')
  have fiber_eq:
    "AE x in M. integral\<^sup>L (N \<Otimes>\<^sub>M P) (\<lambda>yz. ?g (x, yz)) =
      (\<integral>y. \<integral>z. f ((x, y), z) \<partial>P \<partial>N)"
    using fiber_integrable
  proof eventually_elim
    fix x
    assume x_integrable:
      "integrable (N \<Otimes>\<^sub>M P) (\<lambda>yz. ?g (x, yz))"
    show "integral\<^sup>L (N \<Otimes>\<^sub>M P) (\<lambda>yz. ?g (x, yz)) =
        (\<integral>y. \<integral>z. f ((x, y), z) \<partial>P \<partial>N)"
      using NP.integral_fst'[OF x_integrable, symmetric]
      by (simp add: case_prod_unfold)
  qed
  have right_nested:
    "integral\<^sup>L ?R ?g =
      (\<integral>x. \<integral>y. \<integral>z. f ((x, y), z) \<partial>P \<partial>N \<partial>M)"
  proof -
    have outer_eq:
      "(\<integral>x. integral\<^sup>L (N \<Otimes>\<^sub>M P) (\<lambda>yz. ?g (x, yz)) \<partial>M) =
        (\<integral>x. \<integral>y. \<integral>z. f ((x, y), z) \<partial>P \<partial>N \<partial>M)"
    proof (rule Bochner_Integration.integral_cong_AE)
      show "(\<lambda>x. integral\<^sup>L (N \<Otimes>\<^sub>M P) (\<lambda>yz. ?g (x, yz)))
        \<in> borel_measurable M"
        using right_outer_integrable by measurable
      show "(\<lambda>x. \<integral>y. \<integral>z. f ((x, y), z) \<partial>P \<partial>N)
        \<in> borel_measurable M"
        using triple_outer_integrable by measurable
      show "AE x in M. integral\<^sup>L (N \<Otimes>\<^sub>M P) (\<lambda>yz. ?g (x, yz)) =
        (\<integral>y. \<integral>z. f ((x, y), z) \<partial>P \<partial>N)"
        by (rule fiber_eq)
    qed
    show ?thesis using right_outer outer_eq by simp
  qed
  show ?thesis using left_nested right_nested by simp
qed

section \<open>The first negative natural coordinate as the active variable\<close>

theorem slp_natural_pair_heads_negative_active_transport:
  fixes n :: nat
    and F :: "((((nat \<Rightarrow> slp_point) \<times> (nat \<Rightarrow> slp_point)) \<times>
      slp_point) \<times> slp_point) \<Rightarrow> complex"
  assumes F_integrable:
    "integrable
      ((((PiM {..<Suc n} (\<lambda>_::nat. (lborel :: slp_point measure)))
          \<Otimes>\<^sub>M
        (PiM {..<Suc n} (\<lambda>_::nat. (lborel :: slp_point measure))))
          \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M lborel) F"
  shows "let Tail = PiM {1..<Suc n}
               (\<lambda>_::nat. (lborel :: slp_point measure));
             R = (lborel :: slp_point measure) \<Otimes>\<^sub>M lborel;
             A = (lborel :: slp_point measure) \<Otimes>\<^sub>M Tail;
             M = Tail \<Otimes>\<^sub>M (R \<Otimes>\<^sub>M A);
             G = (\<lambda>(c, eta).
               let neg_tail = fst c;
                   r = fst (snd c);
                   pos = snd (snd c)
               in F ((((snd pos)(0 := fst pos), neg_tail(0 := eta)), fst r), snd r))
    in integrable (M \<Otimes>\<^sub>M lborel) G \<and>
       integral\<^sup>L
        ((((PiM {..<Suc n} (\<lambda>_::nat. (lborel :: slp_point measure)))
            \<Otimes>\<^sub>M
          (PiM {..<Suc n} (\<lambda>_::nat. (lborel :: slp_point measure))))
            \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M lborel) F =
       integral\<^sup>L (M \<Otimes>\<^sub>M lborel) G"
proof -
  let ?L = "lborel :: slp_point measure"
  let ?Tail = "PiM {1..<Suc n} (\<lambda>_::nat. ?L)"
  let ?Full = "PiM {..<Suc n} (\<lambda>_::nat. ?L)"
  let ?Source = "?L \<Otimes>\<^sub>M ?Tail"
  let ?Arrays = "?Full \<Otimes>\<^sub>M ?Full"
  let ?SplitArrays = "?Source \<Otimes>\<^sub>M ?Source"
  let ?R = "?L \<Otimes>\<^sub>M ?L"
  let ?Original = "(?Arrays \<Otimes>\<^sub>M ?L) \<Otimes>\<^sub>M ?L"
  let ?Balanced = "?Arrays \<Otimes>\<^sub>M ?R"
  let ?Split = "?SplitArrays \<Otimes>\<^sub>M ?R"
  let ?Passive = "?Tail \<Otimes>\<^sub>M (?R \<Otimes>\<^sub>M ?Source)"
  let ?Active = "?Passive \<Otimes>\<^sub>M ?L"
  let ?update = "\<lambda>(head, tail). tail(0 := head)"
  let ?pair_update = "\<lambda>(positive, negative).
    (?update positive, ?update negative)"
  let ?whole_update = "\<lambda>(arrays, r). (?pair_update arrays, r)"
  let ?FB = "\<lambda>(arrays, (terminal, root)). F ((arrays, terminal), root)"
  let ?G0 = "\<lambda>(arrays, r). ?FB (?pair_update arrays, r)"
  let ?G1 = "\<lambda>(positive, (negative, r)). ?G0 ((positive, negative), r)"
  let ?G2 = "\<lambda>((negative, r), positive). ?G1 (positive, (negative, r))"
  let ?G3 = "\<lambda>(negative, (r, positive)). ?G2 ((negative, r), positive)"
  let ?G4 = "\<lambda>(neg_head, (neg_tail, (r, positive))).
    ?G3 ((neg_head, neg_tail), (r, positive))"
  let ?G5 = "\<lambda>((neg_tail, (r, positive)), neg_head).
    ?G4 (neg_head, (neg_tail, (r, positive)))"
  have finite_tail: "finite {1..<Suc n}" by simp
  have zero_not_tail: "0 \<notin> {1..<Suc n}" by simp
  have interval_insert: "insert 0 {1..<Suc n} = {..<Suc n}" by auto
  interpret natural: product_sigma_finite
    "(\<lambda>_::nat. (lborel :: slp_point measure))" by standard
  have Tail_sigma: "sigma_finite_measure ?Tail"
    by (rule natural.sigma_finite[OF finite_tail])
  have Full_sigma: "sigma_finite_measure ?Full"
    by (rule natural.sigma_finite) simp
  have L_sigma: "sigma_finite_measure ?L" by standard
  interpret Tail: sigma_finite_measure ?Tail by (rule Tail_sigma)
  interpret Full: sigma_finite_measure ?Full by (rule Full_sigma)
  interpret L: sigma_finite_measure ?L by (rule L_sigma)
  interpret Source: pair_sigma_finite ?L ?Tail ..
  interpret Arrays: pair_sigma_finite ?Full ?Full ..
  interpret SplitArrays: pair_sigma_finite ?Source ?Source ..
  interpret R: pair_sigma_finite ?L ?L ..
  have Source_sigma: "sigma_finite_measure ?Source" by standard
  have Arrays_sigma: "sigma_finite_measure ?Arrays" by standard
  have SplitArrays_sigma: "sigma_finite_measure ?SplitArrays" by standard
  have R_sigma: "sigma_finite_measure ?R" by standard
  have Source_R_sigma: "sigma_finite_measure (?Source \<Otimes>\<^sub>M ?R)"
    by (rule sigma_finite_pair_measure[OF Source_sigma R_sigma])
  have R_Source_sigma: "sigma_finite_measure (?R \<Otimes>\<^sub>M ?Source)"
    by (rule sigma_finite_pair_measure[OF R_sigma Source_sigma])
  have Tail_R_Source_sigma:
    "sigma_finite_measure (?Tail \<Otimes>\<^sub>M (?R \<Otimes>\<^sub>M ?Source))"
    by (rule sigma_finite_pair_measure[OF Tail_sigma R_Source_sigma])
  have update_measurable: "?update \<in> measurable ?Source ?Full"
  proof -
    have swap_measurable:
      "(\<lambda>(head, tail). (tail, head))
        \<in> measurable ?Source (?Tail \<Otimes>\<^sub>M ?L)"
      by (rule measurable_pair_swap')
    have add_measurable:
      "(\<lambda>(tail, head). tail(0 := head))
        \<in> measurable (?Tail \<Otimes>\<^sub>M ?L) ?Full"
    proof -
      have raw:
        "(\<lambda>(tail, head). tail(0 := head))
          \<in> measurable (?Tail \<Otimes>\<^sub>M ?L)
            (PiM (insert 0 {1..<Suc n}) (\<lambda>_::nat. ?L))"
        by (rule measurable_add_dim)
      show ?thesis using raw by (simp only: interval_insert)
    qed
    have composed:
      "(\<lambda>(tail, head). tail(0 := head)) \<circ>
          (\<lambda>(head, tail). (tail, head))
        \<in> measurable ?Source ?Full"
      by (rule measurable_comp[OF swap_measurable add_measurable])
    have comp_eq:
      "(\<lambda>(tail, head). tail(0 := head)) \<circ>
          (\<lambda>(head, tail). (tail, head)) = ?update"
      by (rule ext) (auto split: prod.split)
    show ?thesis
      by (subst comp_eq[symmetric]) (rule composed)
  qed
  have update_distribution: "distr ?Source ?Full ?update = ?Full"
  proof -
    have raw:
      "distr ?Source
          (PiM (insert 0 {1..<Suc n}) (\<lambda>_::nat. ?L)) ?update =
        PiM (insert 0 {1..<Suc n}) (\<lambda>_::nat. ?L)"
      by (rule natural.slp_distr_product_insert_head[OF
        finite_tail zero_not_tail])
    show ?thesis using raw by (simp only: interval_insert)
  qed
  have pair_update_measurable:
    "?pair_update \<in> measurable ?SplitArrays ?Arrays"
  proof -
    have positive:
      "?update \<circ> fst \<in> measurable ?SplitArrays ?Full"
      by (rule measurable_comp[OF measurable_fst update_measurable])
    have negative:
      "?update \<circ> snd \<in> measurable ?SplitArrays ?Full"
      by (rule measurable_comp[OF measurable_snd update_measurable])
    have raw:
      "(\<lambda>w. ((?update \<circ> fst) w, (?update \<circ> snd) w))
        \<in> measurable ?SplitArrays ?Arrays"
      by (rule measurable_Pair[OF positive negative])
    show ?thesis using raw by (simp only: comp_apply split_beta')
  qed
  have pair_update_distribution:
    "distr ?SplitArrays ?Arrays ?pair_update = ?Arrays"
  proof -
    have raw:
      "distr ?Source ?Full ?update \<Otimes>\<^sub>M
          distr ?Source ?Full ?update =
        distr ?SplitArrays ?Arrays
          (\<lambda>(positive, negative).
            (?update positive, ?update negative))"
      by (rule pair_measure_distr[OF update_measurable update_measurable])
        (use Full_sigma update_distribution in simp)
    show ?thesis using raw update_distribution by (simp only: split_beta')
  qed
  have whole_update_measurable:
    "?whole_update \<in> measurable ?Split ?Balanced"
  proof -
    have arrays:
      "?pair_update \<circ> fst \<in> measurable ?Split ?Arrays"
      by (rule measurable_comp[OF measurable_fst pair_update_measurable])
    have raw:
      "(\<lambda>w. ((?pair_update \<circ> fst) w, snd w))
        \<in> measurable ?Split ?Balanced"
      by (rule measurable_Pair[OF arrays measurable_snd])
    show ?thesis using raw by (simp only: comp_apply split_beta')
  qed
  have whole_update_distribution:
    "distr ?Split ?Balanced ?whole_update = ?Balanced"
  proof -
    have id_measurable: "id \<in> measurable ?R ?R"
      unfolding id_def by measurable
    have id_distribution: "distr ?R ?R id = ?R"
      unfolding id_def by (rule distr_id)
    have id_sigma: "sigma_finite_measure (distr ?R ?R id)"
      using R_sigma id_distribution by simp
    have raw:
      "distr ?SplitArrays ?Arrays ?pair_update \<Otimes>\<^sub>M
          distr ?R ?R id =
        distr ?Split ?Balanced
          (\<lambda>(arrays, r). (?pair_update arrays, id r))"
      by (rule pair_measure_distr[OF
        pair_update_measurable id_measurable id_sigma])
    show ?thesis
      using raw pair_update_distribution id_distribution
      by (simp only: id_apply split_beta')
  qed
  have balanced_integrable: "integrable ?Balanced ?FB"
    using slp_product_assoc_integrable_iff[OF Arrays_sigma L_sigma L_sigma,
      of F] F_integrable by blast
  have balanced_integral:
    "integral\<^sup>L ?Original F = integral\<^sup>L ?Balanced ?FB"
    by (rule slp_product_assoc_integral[OF
      Arrays_sigma L_sigma L_sigma F_integrable])
  have FB_measurable: "?FB \<in> borel_measurable ?Balanced"
    using balanced_integrable by measurable
  have G0_integrable: "integrable ?Split ?G0"
  proof -
    have transported:
      "integrable (distr ?Split ?Balanced ?whole_update) ?FB"
      using whole_update_distribution balanced_integrable by simp
    have composed:
      "integrable ?Split (\<lambda>x. ?FB (?whole_update x))"
      by (rule integrable_distr[OF whole_update_measurable transported])
    show ?thesis using composed by (simp only: split_beta')
  qed
  have split_integral:
    "integral\<^sup>L ?Balanced ?FB = integral\<^sup>L ?Split ?G0"
  proof -
    have raw:
      "integral\<^sup>L (distr ?Split ?Balanced ?whole_update) ?FB =
        integral\<^sup>L ?Split (\<lambda>x. ?FB (?whole_update x))"
      by (rule integral_distr[OF whole_update_measurable FB_measurable])
    show ?thesis
      using raw whole_update_distribution by (simp only: split_beta')
  qed
  have G1_integrable:
    "integrable (?Source \<Otimes>\<^sub>M (?Source \<Otimes>\<^sub>M ?R)) ?G1"
    using slp_product_assoc_integrable_iff[OF
      Source_sigma Source_sigma R_sigma, of ?G0] G0_integrable by blast
  have integral_01:
    "integral\<^sup>L ?Split ?G0 =
      integral\<^sup>L (?Source \<Otimes>\<^sub>M (?Source \<Otimes>\<^sub>M ?R)) ?G1"
    by (rule slp_product_assoc_integral[OF
      Source_sigma Source_sigma R_sigma G0_integrable])
  interpret Source_SR: pair_sigma_finite
    ?Source "?Source \<Otimes>\<^sub>M ?R"
    by (rule pair_sigma_finite.intro; fact)
  have swap_12_eq:
    "(\<lambda>(negative_r, positive). ?G1 (positive, negative_r)) = ?G2"
    by (rule ext) (auto split: prod.split)
  have G2_integrable:
    "integrable ((?Source \<Otimes>\<^sub>M ?R) \<Otimes>\<^sub>M ?Source) ?G2"
  proof -
    have raw:
      "integrable ((?Source \<Otimes>\<^sub>M ?R) \<Otimes>\<^sub>M ?Source)
        (\<lambda>(negative_r, positive). ?G1 (positive, negative_r))"
      by (rule Source_SR.integrable_product_swap[OF G1_integrable])
    show ?thesis by (subst swap_12_eq[symmetric]) (rule raw)
  qed
  have integral_12:
    "integral\<^sup>L (?Source \<Otimes>\<^sub>M (?Source \<Otimes>\<^sub>M ?R)) ?G1 =
      integral\<^sup>L ((?Source \<Otimes>\<^sub>M ?R) \<Otimes>\<^sub>M ?Source) ?G2"
  proof -
    have G1_measurable:
      "?G1 \<in> borel_measurable
        (?Source \<Otimes>\<^sub>M (?Source \<Otimes>\<^sub>M ?R))"
      using G1_integrable by measurable
    have raw:
      "integral\<^sup>L ((?Source \<Otimes>\<^sub>M ?R) \<Otimes>\<^sub>M ?Source)
          (\<lambda>(negative_r, positive). ?G1 (positive, negative_r)) =
        integral\<^sup>L (?Source \<Otimes>\<^sub>M (?Source \<Otimes>\<^sub>M ?R)) ?G1"
      by (rule Source_SR.integral_product_swap[OF G1_measurable])
    have reversed:
      "integral\<^sup>L (?Source \<Otimes>\<^sub>M (?Source \<Otimes>\<^sub>M ?R)) ?G1 =
        integral\<^sup>L ((?Source \<Otimes>\<^sub>M ?R) \<Otimes>\<^sub>M ?Source)
          (\<lambda>(negative_r, positive). ?G1 (positive, negative_r))"
      using raw by simp
    show ?thesis by (subst swap_12_eq[symmetric]) (rule reversed)
  qed
  have G3_integrable:
    "integrable (?Source \<Otimes>\<^sub>M (?R \<Otimes>\<^sub>M ?Source)) ?G3"
    using slp_product_assoc_integrable_iff[OF
      Source_sigma R_sigma Source_sigma, of ?G2] G2_integrable by blast
  have integral_23:
    "integral\<^sup>L ((?Source \<Otimes>\<^sub>M ?R) \<Otimes>\<^sub>M ?Source) ?G2 =
      integral\<^sup>L (?Source \<Otimes>\<^sub>M (?R \<Otimes>\<^sub>M ?Source)) ?G3"
    by (rule slp_product_assoc_integral[OF
      Source_sigma R_sigma Source_sigma G2_integrable])
  have assoc_34_eq:
    "(\<lambda>(head, (tail, rest)). ?G3 ((head, tail), rest)) = ?G4"
    by (rule ext) (auto split: prod.split)
  have G4_integrable:
    "integrable (?L \<Otimes>\<^sub>M (?Tail \<Otimes>\<^sub>M (?R \<Otimes>\<^sub>M ?Source))) ?G4"
  proof -
    have raw:
      "integrable
        (?L \<Otimes>\<^sub>M (?Tail \<Otimes>\<^sub>M (?R \<Otimes>\<^sub>M ?Source)))
        (\<lambda>(head, (tail, rest)). ?G3 ((head, tail), rest))"
      using slp_product_assoc_integrable_iff[OF
        L_sigma Tail_sigma R_Source_sigma, of ?G3] G3_integrable by blast
    show ?thesis by (subst assoc_34_eq[symmetric]) (rule raw)
  qed
  have integral_34:
    "integral\<^sup>L (?Source \<Otimes>\<^sub>M (?R \<Otimes>\<^sub>M ?Source)) ?G3 =
      integral\<^sup>L (?L \<Otimes>\<^sub>M (?Tail \<Otimes>\<^sub>M (?R \<Otimes>\<^sub>M ?Source))) ?G4"
  proof -
    have raw:
      "integral\<^sup>L (?Source \<Otimes>\<^sub>M (?R \<Otimes>\<^sub>M ?Source)) ?G3 =
        integral\<^sup>L
          (?L \<Otimes>\<^sub>M (?Tail \<Otimes>\<^sub>M (?R \<Otimes>\<^sub>M ?Source)))
          (\<lambda>(head, (tail, rest)). ?G3 ((head, tail), rest))"
      by (rule slp_product_assoc_integral[OF
        L_sigma Tail_sigma R_Source_sigma G3_integrable])
    show ?thesis by (subst assoc_34_eq[symmetric]) (rule raw)
  qed
  interpret L_Passive: pair_sigma_finite ?L ?Passive
    by (rule pair_sigma_finite.intro; fact)
  have swap_45_eq:
    "(\<lambda>(passive, head). ?G4 (head, passive)) = ?G5"
    by (rule ext) (auto split: prod.split)
  have G5_integrable: "integrable ?Active ?G5"
  proof -
    have raw:
      "integrable ?Active (\<lambda>(passive, head). ?G4 (head, passive))"
      by (rule L_Passive.integrable_product_swap[OF G4_integrable])
    show ?thesis by (subst swap_45_eq[symmetric]) (rule raw)
  qed
  have integral_45:
    "integral\<^sup>L (?L \<Otimes>\<^sub>M ?Passive) ?G4 =
      integral\<^sup>L ?Active ?G5"
  proof -
    have G4_measurable: "?G4 \<in> borel_measurable (?L \<Otimes>\<^sub>M ?Passive)"
      using G4_integrable by measurable
    have raw:
      "integral\<^sup>L ?Active (\<lambda>(passive, head). ?G4 (head, passive)) =
        integral\<^sup>L (?L \<Otimes>\<^sub>M ?Passive) ?G4"
      by (rule L_Passive.integral_product_swap[OF G4_measurable])
    have reversed:
      "integral\<^sup>L (?L \<Otimes>\<^sub>M ?Passive) ?G4 =
        integral\<^sup>L ?Active (\<lambda>(passive, head). ?G4 (head, passive))"
      using raw by simp
    show ?thesis by (subst swap_45_eq[symmetric]) (rule reversed)
  qed
  have final_integral:
    "integral\<^sup>L ?Original F = integral\<^sup>L ?Active ?G5"
    using balanced_integral split_integral integral_01 integral_12
      integral_23 integral_34 integral_45 by simp
  show ?thesis
    unfolding Let_def
    using G5_integrable final_integral
    by (simp only: split_beta' prod.sel)
qed

context aim_planar_riesz_hls_cauchy
begin

section \<open>Positive-order one-sided principal decay\<close>

theorem slp_natural_one_sided_positive_principal_decay:
  fixes n :: nat and R C p :: real and X :: "slp_point set"
    and cutoff q Q phi :: slp_scalar_field
    and orientation :: slp_cauchy_orientation
  assumes stationary:
      "hormander_quadratic_stationary_phase_decay_claim TYPE(2)"
    and density: "evans_compact_smooth_l1_density_claim TYPE(2)"
    and R_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and cutoff_measurable[measurable]: "cutoff \<in> borel_measurable lborel"
    and q_lp: "aim_complex_lp_on_plane p q"
    and Q_lp: "aim_complex_lp_on_plane p Q"
    and Q_outside: "\<And>x. x \<notin> X \<Longrightarrow> Q x = 0"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and Q_support: "\<And>x. Q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and q_support: "\<And>x. q x \<noteq> 0 \<Longrightarrow> norm x \<le> R"
    and phi_test: "slp_test_function_on UNIV phi"
  shows "let A = slp_cauchy_transform orientation q;
             P = PiM {..<Suc n} (\<lambda>_::nat. (lborel :: slp_point measure));
             MJ = ((P \<Otimes>\<^sub>M P) \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M lborel;
             ps = (\<lambda>z. map (\<lambda>k.
               (fst (fst (fst z)) k, snd (fst (fst z)) k)) [0..<Suc n]);
             residual = (\<lambda>z. slp_left_branch_residual (ps z) (snd (fst z)))
    in ((\<lambda>omega::real. integral\<^sup>L MJ
      (\<lambda>z. exp (\<i> * of_real (omega * residual z)) *
        (slp_natural_one_sided_weighted_amplitude (Suc n) Q cutoff q A phi z -
         slp_natural_one_sided_weighted_amplitude (Suc n) Q cutoff q (\<lambda>_. 1)
           (\<lambda>u. phi u * A u) z))) \<longlongrightarrow> 0) at_top"
proof -
  let ?L = "lborel :: slp_point measure"
  let ?Tail = "PiM {1..<Suc n} (\<lambda>_::nat. ?L)"
  let ?Full = "PiM {..<Suc n} (\<lambda>_::nat. ?L)"
  let ?Rcarrier = "?L \<Otimes>\<^sub>M ?L"
  let ?Source = "?L \<Otimes>\<^sub>M ?Tail"
  let ?M = "?Tail \<Otimes>\<^sub>M (?Rcarrier \<Otimes>\<^sub>M ?Source)"
  let ?Original = "((?Full \<Otimes>\<^sub>M ?Full) \<Otimes>\<^sub>M ?L) \<Otimes>\<^sub>M ?L"
  let ?A = "slp_cauchy_transform orientation q"
  let ?one = "\<lambda>_::slp_point. (1::complex)"
  let ?phiA = "\<lambda>u. phi u * ?A u"
  let ?W = "\<lambda>T H.
    slp_natural_one_sided_weighted_amplitude (Suc n) Q cutoff q T H"
  let ?B = "\<lambda>z. ?W ?A phi z - ?W ?one ?phiA z"
  let ?ps = "\<lambda>z. map (\<lambda>k.
    (fst (fst (fst z)) k, snd (fst (fst z)) k)) [0..<Suc n]"
  let ?residual = "\<lambda>z. slp_left_branch_residual (?ps z) (snd (fst z))"
  let ?neg_tail = "\<lambda>c. fst c"
  let ?terminal = "\<lambda>c. fst (fst (snd c))"
  let ?root = "\<lambda>c. snd (fst (snd c))"
  let ?lam = "\<lambda>c. fst (snd (snd c))"
  let ?pos_tail = "\<lambda>c. snd (snd (snd c))"
  let ?pack = "\<lambda>c eta.
    ((((?pos_tail c)(0 := ?lam c), (?neg_tail c)(0 := eta)), ?terminal c), ?root c)"
  let ?pairs = "\<lambda>c. map (\<lambda>k.
    (?pos_tail c (Suc k), ?neg_tail c (Suc k))) [0..<n]"
  let ?F = "\<lambda>c eta. ?B (?pack c eta)"
  have L_sigma: "sigma_finite_measure ?L" by standard
  interpret L: sigma_finite_measure ?L by (rule L_sigma)
  interpret natural: product_sigma_finite
    "(\<lambda>_::nat. (lborel :: slp_point measure))" by standard
  have Tail_sigma: "sigma_finite_measure ?Tail"
    by (rule natural.sigma_finite) simp
  have R_sigma: "sigma_finite_measure ?Rcarrier"
    by (rule sigma_finite_pair_measure[OF L_sigma L_sigma])
  have Source_sigma: "sigma_finite_measure ?Source"
    by (rule sigma_finite_pair_measure[OF L_sigma Tail_sigma])
  have R_Source_sigma: "sigma_finite_measure (?Rcarrier \<Otimes>\<^sub>M ?Source)"
    by (rule sigma_finite_pair_measure[OF R_sigma Source_sigma])
  have M_sigma: "sigma_finite_measure ?M"
    by (rule sigma_finite_pair_measure[OF Tail_sigma R_Source_sigma])
  have neg_tail_measurable: "?neg_tail \<in> measurable ?M ?Tail"
    by measurable
  have pos_tail_measurable: "?pos_tail \<in> measurable ?M ?Tail"
    by measurable
  have lam_measurable: "?lam \<in> borel_measurable ?M"
    by measurable
  have terminal_map: "?terminal \<in> measurable ?M ?L"
    by measurable
  have terminal_measurable: "?terminal \<in> borel_measurable ?M"
    using terminal_map by (simp only: measurable_lborel1)
  have pos_component:
    "(\<lambda>c. ?pos_tail c k) \<in> borel_measurable ?M"
    if k_in: "k \<in> {1..<Suc n}" for k
  proof -
    have evaluation:
      "(\<lambda>f::nat \<Rightarrow> slp_point. f k) \<in> measurable ?Tail ?L"
      by (rule measurable_component_singleton[OF k_in])
    show ?thesis
      using measurable_compose[OF pos_tail_measurable evaluation]
      by (simp only: measurable_lborel1 comp_def)
  qed
  have neg_component:
    "(\<lambda>c. ?neg_tail c k) \<in> borel_measurable ?M"
    if k_in: "k \<in> {1..<Suc n}" for k
  proof -
    have evaluation:
      "(\<lambda>f::nat \<Rightarrow> slp_point. f k) \<in> measurable ?Tail ?L"
      by (rule measurable_component_singleton[OF k_in])
    show ?thesis
      using measurable_compose[OF neg_tail_measurable evaluation]
      by (simp only: measurable_lborel1 comp_def)
  qed
  have output_tail_eq:
    "slp_left_branch_output (?pairs c) (?terminal c) =
      ?terminal c + (\<Sum>k\<in>{..<n}.
        ?pos_tail c (Suc k) - ?neg_tail c (Suc k))" for c
    by (simp add: slp_left_branch_output_def slp_branch_increment_def
        map_map comp_def sum_list_distinct_conv_sum_set atLeast0LessThan)
  have increment_measurable[measurable]:
    "(\<lambda>c. \<Sum>k\<in>{..<n}.
      ?pos_tail c (Suc k) - ?neg_tail c (Suc k))
      \<in> borel_measurable ?M"
  proof (rule borel_measurable_sum)
    fix k assume k_in: "k \<in> {..<n}"
    have shifted_in: "Suc k \<in> {1..<Suc n}" using k_in by auto
    show "(\<lambda>c. ?pos_tail c (Suc k) - ?neg_tail c (Suc k))
      \<in> borel_measurable ?M"
      using pos_component[OF shifted_in] neg_component[OF shifted_in] by measurable
  qed
  have output_measurable:
    "(\<lambda>c. slp_left_branch_output (?pairs c) (?terminal c))
      \<in> borel_measurable ?M"
    by (simp only: output_tail_eq; measurable)
  have quadratic_compose:
    "(\<lambda>c. slp_point_quadratic_value (f c)) \<in> borel_measurable ?M"
    if f_measurable: "f \<in> borel_measurable ?M"
    for f :: "_ \<Rightarrow> slp_point"
  proof -
    have nth[measurable]: "(\<lambda>c. f c $ i) \<in> borel_measurable ?M" for i :: 2
      using measurable_comp[OF f_measurable borel_measurable_nth[of i]]
      by (simp only: comp_def)
    show ?thesis unfolding slp_point_quadratic_value_def by measurable
  qed
  have quadratic_sum_measurable[measurable]:
    "(\<lambda>c. \<Sum>k\<in>{..<n}.
      slp_point_quadratic_value (?pos_tail c (Suc k)) -
      slp_point_quadratic_value (?neg_tail c (Suc k))) \<in> borel_measurable ?M"
  proof (rule borel_measurable_sum)
    fix k assume k_in: "k \<in> {..<n}"
    have shifted_in: "Suc k \<in> {1..<Suc n}" using k_in by auto
    show "(\<lambda>c. slp_point_quadratic_value (?pos_tail c (Suc k)) -
      slp_point_quadratic_value (?neg_tail c (Suc k))) \<in> borel_measurable ?M"
      using quadratic_compose[OF pos_component[OF shifted_in]]
        quadratic_compose[OF neg_component[OF shifted_in]] by measurable
  qed
  have residual_tail_eq:
    "slp_left_branch_residual (?pairs c) (?terminal c) =
      (\<Sum>k\<in>{..<n}.
        slp_point_quadratic_value (?pos_tail c (Suc k)) -
        slp_point_quadratic_value (?neg_tail c (Suc k))) +
      slp_point_quadratic_value (?terminal c) -
      slp_point_quadratic_value
        (slp_left_branch_output (?pairs c) (?terminal c))" for c
    by (simp add: slp_left_branch_residual_def slp_branch_residual_def
        map_map comp_def sum_list_distinct_conv_sum_set atLeast0LessThan)
  have terminal_quadratic_measurable[measurable]:
    "(\<lambda>c. slp_point_quadratic_value (?terminal c))
      \<in> borel_measurable ?M"
    by (rule quadratic_compose[OF terminal_measurable])
  have output_quadratic_measurable[measurable]:
    "(\<lambda>c. slp_point_quadratic_value
      (slp_left_branch_output (?pairs c) (?terminal c)))
      \<in> borel_measurable ?M"
    by (rule quadratic_compose[OF output_measurable])
  have residual_measurable:
    "(\<lambda>c. slp_left_branch_residual (?pairs c) (?terminal c))
      \<in> borel_measurable ?M"
    by (simp only: residual_tail_eq; measurable)
  have interval_list: "0 # map Suc [0..<n] = [0..<Suc n]"
    by (induction n) simp_all
  have pack_pairs:
    "?ps (?pack c eta) = (?lam c, eta) # ?pairs c" for c eta
  proof -
    show ?thesis
      by (subst interval_list[symmetric])
        simp
  qed
  have residual_pack:
    "?residual (?pack c eta) =
      slp_left_branch_residual ((?lam c, eta) # ?pairs c) (?terminal c)"
    for c eta
    using pack_pairs[of c eta]
    by (simp only: prod.sel)
  have original_zero: "integrable ?Original ?B"
  proof -
    note raw = slp_natural_one_sided_principal_components_integrable[
      OF R_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable q_lp Q_lp Q_outside cutoff_bound C_nonnegative
        Q_support cutoff_support q_support phi_test,
      where n = "Suc n" and omega = 0 and orientation = orientation]
    show ?thesis
      using raw
      by (simp add: Let_def)
  qed
  have active_integrable:
    "integrable (?M \<Otimes>\<^sub>M ?L) (case_prod ?F)"
  proof -
    note transported = slp_natural_pair_heads_negative_active_transport[
      OF original_zero]
    show ?thesis
      using transported by (simp only: Let_def split_beta' prod.sel)
  qed
  have active_decay:
    "((\<lambda>omega::real. integral\<^sup>L (?M \<Otimes>\<^sub>M ?L)
      (\<lambda>(c,eta). exp (\<i> * of_real (omega *
        slp_left_branch_residual ((?lam c, eta) # ?pairs c) (?terminal c))) *
        ?F c eta)) \<longlongrightarrow> 0) at_top"
    by (rule slp_left_branch_residual_first_negative_decay_measure[
      OF stationary density M_sigma lam_measurable output_measurable
        residual_measurable active_integrable])
  have original_integrable:
    "integrable ?Original
      (\<lambda>z. exp (\<i> * of_real (omega * ?residual z)) * ?B z)" for omega
  proof -
    note raw = slp_natural_one_sided_principal_components_integrable[
      OF R_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable q_lp Q_lp Q_outside cutoff_bound C_nonnegative
        Q_support cutoff_support q_support phi_test,
      where n = "Suc n" and omega = omega and orientation = orientation]
    show ?thesis using raw by (simp add: Let_def)
  qed
  have integral_transport:
    "integral\<^sup>L ?Original
        (\<lambda>z. exp (\<i> * of_real (omega * ?residual z)) * ?B z) =
      integral\<^sup>L (?M \<Otimes>\<^sub>M ?L)
        (\<lambda>(c,eta). exp (\<i> * of_real (omega *
          slp_left_branch_residual ((?lam c, eta) # ?pairs c) (?terminal c))) *
          ?F c eta)" for omega
  proof -
    note transported = slp_natural_pair_heads_negative_active_transport[
      OF original_integrable[of omega]]
    have raw:
      "integral\<^sup>L ?Original
          (\<lambda>z. exp (\<i> * of_real (omega * ?residual z)) * ?B z) =
        integral\<^sup>L (?M \<Otimes>\<^sub>M ?L)
          (\<lambda>(c,eta). exp (\<i> * of_real (omega * ?residual (?pack c eta))) *
            ?B (?pack c eta))"
      using transported by (simp only: Let_def split_beta' prod.sel)
    show ?thesis
      using raw by (simp only: residual_pack)
  qed
  have function_eq:
    "(\<lambda>omega::real. integral\<^sup>L ?Original
      (\<lambda>z. exp (\<i> * of_real (omega * ?residual z)) * ?B z)) =
     (\<lambda>omega::real. integral\<^sup>L (?M \<Otimes>\<^sub>M ?L)
      (\<lambda>(c,eta). exp (\<i> * of_real (omega *
        slp_left_branch_residual ((?lam c, eta) # ?pairs c) (?terminal c))) *
        ?F c eta))"
    by (rule ext) (rule integral_transport)
  show ?thesis
    unfolding Let_def
    using active_decay function_eq by simp
qed

end

end
