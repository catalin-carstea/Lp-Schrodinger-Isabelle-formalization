theory Inverse_Schrodinger_Lp_Cartesian_Sum_Merge
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Finite_Product_Sum_Merge"
begin

section \<open>Merging two Cartesian Lebesgue vectors\<close>

definition slp_cartesian_sum_merge ::
    "(real^'i::finite) \<times> (real^'j::finite) \<Rightarrow> real^('i + 'j)"
where
  "slp_cartesian_sum_merge xy =
    (\<chi> k. case k of Inl i \<Rightarrow> fst xy $ i | Inr j \<Rightarrow> snd xy $ j)"

lemma slp_cartesian_sum_merge_linear:
  "linear (slp_cartesian_sum_merge ::
    ((real^'i::finite) \<times> (real^'j::finite)) \<Rightarrow> real^('i + 'j))"
  by (rule linearI)
    (simp_all add: slp_cartesian_sum_merge_def vec_eq_iff
      split: sum.splits)

lemma slp_cartesian_sum_merge_measurable:
  "(slp_cartesian_sum_merge ::
      ((real^'i::finite) \<times> (real^'j::finite)) \<Rightarrow> real^('i + 'j))
    \<in> measurable (lborel \<Otimes>\<^sub>M lborel) lborel"
proof -
  have bounded:
    "bounded_linear (slp_cartesian_sum_merge ::
      ((real^'i) \<times> (real^'j)) \<Rightarrow> real^('i + 'j))"
    using slp_cartesian_sum_merge_linear
    by (simp add: linear_conv_bounded_linear)
  have continuous:
    "continuous_on UNIV (slp_cartesian_sum_merge ::
      ((real^'i) \<times> (real^'j)) \<Rightarrow> real^('i + 'j))"
    by (rule linear_continuous_on[OF bounded])
  have borel:
    "(slp_cartesian_sum_merge ::
      ((real^'i) \<times> (real^'j)) \<Rightarrow> real^('i + 'j))
      \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF continuous])
  show ?thesis
    using borel
    by (simp only: lborel_prod measurable_lborel1 measurable_lborel2)
qed

theorem slp_cartesian_sum_merge_distr_lborel:
  "distr
      ((lborel :: (real^'i::finite) measure) \<Otimes>\<^sub>M
        (lborel :: (real^'j::finite) measure))
      (lborel :: (real^('i + 'j)) measure)
      slp_cartesian_sum_merge =
    (lborel :: (real^('i + 'j)) measure)"
proof -
  let ?MI = "PiM (UNIV::'i set) (\<lambda>_. (lborel :: real measure))"
  let ?MJ = "PiM (UNIV::'j set) (\<lambda>_. (lborel :: real measure))"
  let ?MK = "PiM (UNIV::('i + 'j) set) (\<lambda>_. (lborel :: real measure))"
  let ?VI = "\<lambda>f::'i \<Rightarrow> real. \<chi> i. f i"
  let ?VJ = "\<lambda>f::'j \<Rightarrow> real. \<chi> j. f j"
  let ?VK = "\<lambda>f::('i + 'j) \<Rightarrow> real. \<chi> k. f k"
  let ?P = "\<lambda>(omega, eta). (?VI omega, ?VJ eta)"
  let ?G = "\<lambda>x. \<lambda>k. case k of
    Inl i \<Rightarrow> fst x i | Inr j \<Rightarrow> snd x j"
  let ?F = "slp_cartesian_sum_merge ::
    ((real^'i) \<times> (real^'j)) \<Rightarrow> real^('i + 'j)"

  have VI_measurable: "?VI \<in> measurable ?MI borel"
    by (rule slp_cartesian_vector_constructor_measurable)
  have VJ_measurable: "?VJ \<in> measurable ?MJ borel"
    by (rule slp_cartesian_vector_constructor_measurable)
  have VK_measurable: "?VK \<in> measurable ?MK borel"
    by (rule slp_cartesian_vector_constructor_measurable)
  have P_measurable:
    "?P \<in> measurable (?MI \<Otimes>\<^sub>M ?MJ) (borel \<Otimes>\<^sub>M borel)"
  proof -
    have fst_measurable:
      "fst \<in> measurable (?MI \<Otimes>\<^sub>M ?MJ) ?MI"
      by (rule measurable_fst)
    have snd_measurable:
      "snd \<in> measurable (?MI \<Otimes>\<^sub>M ?MJ) ?MJ"
      by (rule measurable_snd)
    have left:
      "(\<lambda>x. ?VI (fst x)) \<in> measurable (?MI \<Otimes>\<^sub>M ?MJ) borel"
      using measurable_compose[OF fst_measurable VI_measurable]
      by (simp only: comp_def)
    have right:
      "(\<lambda>x. ?VJ (snd x)) \<in> measurable (?MI \<Otimes>\<^sub>M ?MJ) borel"
      using measurable_compose[OF snd_measurable VJ_measurable]
      by (simp only: comp_def)
    have pair_explicit:
      "(\<lambda>x. (?VI (fst x), ?VJ (snd x))) \<in>
        measurable (?MI \<Otimes>\<^sub>M ?MJ) (borel \<Otimes>\<^sub>M borel)"
      by (rule measurable_Pair[OF left right])
    have P_eq: "?P = (\<lambda>x. (?VI (fst x), ?VJ (snd x)))"
    proof (rule ext)
      fix x
      show "?P x = (?VI (fst x), ?VJ (snd x))"
        by (cases x) simp
    qed
    show ?thesis
      unfolding P_eq
      by (rule pair_explicit)
  qed
  have G_measurable:
    "?G \<in> measurable (?MI \<Otimes>\<^sub>M ?MJ) ?MK"
  proof (rule measurable_PiM_single')
    fix k
    assume "k \<in> (UNIV::('i + 'j) set)"
    show "(\<lambda>x. ?G x k) \<in>
      measurable (?MI \<Otimes>\<^sub>M ?MJ) (lborel :: real measure)"
    proof (cases k)
      case (Inl i)
      have fst_measurable:
        "fst \<in> measurable (?MI \<Otimes>\<^sub>M ?MJ) ?MI"
        by (rule measurable_fst)
      have coordinate_measurable:
        "(\<lambda>omega. omega i) \<in> measurable ?MI (lborel :: real measure)"
        by (rule measurable_component_singleton) simp
      have component:
        "(\<lambda>x. fst x i) \<in>
          measurable (?MI \<Otimes>\<^sub>M ?MJ) (lborel :: real measure)"
        using measurable_compose[
          OF fst_measurable coordinate_measurable]
        by (simp only: comp_def)
      show ?thesis
        using component Inl by simp
    next
      case (Inr j)
      have snd_measurable:
        "snd \<in> measurable (?MI \<Otimes>\<^sub>M ?MJ) ?MJ"
        by (rule measurable_snd)
      have coordinate_measurable:
        "(\<lambda>eta. eta j) \<in> measurable ?MJ (lborel :: real measure)"
        by (rule measurable_component_singleton) simp
      have component:
        "(\<lambda>x. snd x j) \<in>
          measurable (?MI \<Otimes>\<^sub>M ?MJ) (lborel :: real measure)"
        using measurable_compose[
          OF snd_measurable coordinate_measurable]
        by (simp only: comp_def)
      show ?thesis
        using component Inr by simp
    qed
  next
    show "?G \<in> space (?MI \<Otimes>\<^sub>M ?MJ) \<rightarrow>
      PiE (UNIV::('i + 'j) set) (\<lambda>_. space (lborel :: real measure))"
      by simp
  qed
  have F_measurable:
    "?F \<in> measurable (borel \<Otimes>\<^sub>M borel) borel"
  proof -
    have bounded:
      "bounded_linear ?F"
      using slp_cartesian_sum_merge_linear
      by (simp add: linear_conv_bounded_linear)
    have continuous: "continuous_on UNIV ?F"
      by (rule linear_continuous_on[OF bounded])
    have borel_measurable: "?F \<in> borel_measurable borel"
      by (rule borel_measurable_continuous_onI[OF continuous])
    show ?thesis
      using borel_measurable
      by (simp only: borel_prod)
  qed
  have source_pair:
    "(lborel :: (real^'i) measure) \<Otimes>\<^sub>M
        (lborel :: (real^'j) measure) =
      distr (?MI \<Otimes>\<^sub>M ?MJ) (borel \<Otimes>\<^sub>M borel) ?P"
  proof -
    have target_sigma:
      "sigma_finite_measure (distr ?MJ borel ?VJ)"
      by (simp only: slp_lborel_cartesian_vector_product[symmetric]) standard
    note pair_distr = pair_measure_distr[
      OF VI_measurable VJ_measurable target_sigma]
    show ?thesis
      using pair_distr
      by (simp only: slp_lborel_cartesian_vector_product)
  qed
  have product_merge:
    "distr (?MI \<Otimes>\<^sub>M ?MJ) ?MK ?G = ?MK"
  proof -
    have component_sigma:
      "\<And>k::('i + 'j). sigma_finite_measure (lborel :: real measure)"
      by standard
    have finite_I: "finite (UNIV::'i set)"
      by simp
    have finite_J: "finite (UNIV::'j set)"
      by simp
    note generic_merge = slp_distr_PiM_sum_merge[
      OF component_sigma finite_I finite_J]
    have raw:
      "distr
          (?MI \<Otimes>\<^sub>M ?MJ)
          (PiM (Inl ` (UNIV::'i set) \<union> Inr ` (UNIV::'j set))
            (\<lambda>_. (lborel :: real measure)))
          (\<lambda>(omega, eta). \<lambda>k\<in>Inl ` (UNIV::'i set) \<union>
              Inr ` (UNIV::'j set).
            case k of Inl i \<Rightarrow> omega i | Inr j \<Rightarrow> eta j) =
        PiM (Inl ` (UNIV::'i set) \<union> Inr ` (UNIV::'j set))
          (\<lambda>_. (lborel :: real measure))"
      using generic_merge
      by simp
    have merge_map_eq:
      "(\<lambda>(omega, eta). \<lambda>k\<in>Inl ` (UNIV::'i set) \<union>
          Inr ` (UNIV::'j set).
        case k of Inl i \<Rightarrow> omega i | Inr j \<Rightarrow> eta j) = ?G"
      by (simp add: UNIV_sum fun_eq_iff split: prod.splits sum.splits)
    show ?thesis
      using raw
      by (simp only: merge_map_eq UNIV_sum)
  qed
  have composition: "?F \<circ> ?P = ?VK \<circ> ?G"
  proof (rule ext)
    fix x :: "('i \<Rightarrow> real) \<times> ('j \<Rightarrow> real)"
    obtain omega eta where x_pair: "x = (omega, eta)"
      by (cases x)
    show "(?F \<circ> ?P) x = (?VK \<circ> ?G) x"
      unfolding x_pair
      by (simp add: slp_cartesian_sum_merge_def vec_eq_iff
          split: sum.splits)
  qed
  have target_change:
    "distr
        ((lborel :: (real^'i) measure) \<Otimes>\<^sub>M
          (lborel :: (real^'j) measure))
        (lborel :: (real^('i + 'j)) measure) ?F =
      distr
        ((lborel :: (real^'i) measure) \<Otimes>\<^sub>M
          (lborel :: (real^'j) measure))
        borel ?F"
  proof (rule distr_cong)
    show "((lborel :: (real^'i) measure) \<Otimes>\<^sub>M
        (lborel :: (real^'j) measure)) = lborel \<Otimes>\<^sub>M lborel"
      by (rule refl)
    show "sets (lborel :: (real^('i + 'j)) measure) = sets borel"
      by (rule sets_lborel)
    show "?F x = ?F x"
      for x :: "(real^'i) \<times> (real^'j)"
      by (rule refl)
  qed

  have "distr
      ((lborel :: (real^'i) measure) \<Otimes>\<^sub>M
        (lborel :: (real^'j) measure))
      (lborel :: (real^('i + 'j)) measure) ?F =
    distr
      ((lborel :: (real^'i) measure) \<Otimes>\<^sub>M
        (lborel :: (real^'j) measure))
      borel ?F"
    by (rule target_change)
  also have "... =
    distr
      (distr (?MI \<Otimes>\<^sub>M ?MJ) (borel \<Otimes>\<^sub>M borel) ?P)
      borel ?F"
    by (simp only: source_pair)
  also have "... = distr (?MI \<Otimes>\<^sub>M ?MJ) borel (?F \<circ> ?P)"
    by (rule distr_distr[OF F_measurable P_measurable])
  also have "... = distr (?MI \<Otimes>\<^sub>M ?MJ) borel (?VK \<circ> ?G)"
    by (simp only: composition)
  also have "... = distr (distr (?MI \<Otimes>\<^sub>M ?MJ) ?MK ?G) borel ?VK"
    by (rule distr_distr[OF VK_measurable G_measurable, symmetric])
  also have "... = distr ?MK borel ?VK"
    by (simp only: product_merge)
  also have "... = (lborel :: (real^('i + 'j)) measure)"
    by (rule slp_lborel_cartesian_vector_product[symmetric])
  finally show ?thesis .
qed

end
