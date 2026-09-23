theory Inverse_Schrodinger_Lp_Born_Left_Complex_Kernel_Measurable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Left_Complex_Kernel_Finite"
begin

section \<open>Joint measurability of finite complex left-branch kernels\<close>

lemma slp_cauchy_kernel_compose_measurable:
  assumes left[measurable]: "left \<in> borel_measurable M"
    and right[measurable]: "right \<in> borel_measurable M"
  shows
    "(\<lambda>x. slp_cauchy_kernel orientation (left x) (right x))
      \<in> borel_measurable M"
proof -
  have left_complex:
      "(\<lambda>x. slp_point_as_complex (left x)) \<in> borel_measurable M"
    using measurable_compose[OF left
        slp_point_as_complex_borel_measurable]
    unfolding comp_def .
  have right_complex:
      "(\<lambda>x. slp_point_as_complex (right x)) \<in> borel_measurable M"
    using measurable_compose[OF right
        slp_point_as_complex_borel_measurable]
    unfolding comp_def .
  have difference_measurable:
      "(\<lambda>x. slp_point_as_complex (left x) -
          slp_point_as_complex (right x)) \<in> borel_measurable M"
    by (rule borel_measurable_diff[OF left_complex right_complex])
  show ?thesis
  proof (cases orientation)
    case SLP_Partial_Inverse
    have conjugate_continuous: "continuous_on UNIV cnj"
      by (rule continuous_on_cnj[OF continuous_on_id])
    have conjugate_measurable:
        "(\<lambda>x. cnj (slp_point_as_complex (left x) -
            slp_point_as_complex (right x))) \<in> borel_measurable M"
      by (rule borel_measurable_continuous_on[OF
            conjugate_continuous difference_measurable])
    show ?thesis
      using borel_measurable_inverse[OF conjugate_measurable]
      by (simp only: slp_cauchy_kernel_def slp_cauchy_denominator_def
          slp_cauchy_orientation.simps SLP_Partial_Inverse)
  next
    case SLP_Dbar_Inverse
    show ?thesis
      using borel_measurable_inverse[OF difference_measurable]
      by (simp only: slp_cauchy_kernel_def slp_cauchy_denominator_def
          slp_cauchy_orientation.simps SLP_Dbar_Inverse)
  qed
qed

lemma slp_left_branch_complex_terminal_compose_measurable:
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and terminal_value_measurable[measurable]:
      "terminal_value \<in> borel_measurable lborel"
    and origin_measurable[measurable]:
      "origin \<in> borel_measurable M"
    and terminal_measurable[measurable]:
      "terminal \<in> borel_measurable M"
  shows
    "(\<lambda>x. slp_left_branch_complex_terminal cutoff terminal_value
        (origin x) (terminal x)) \<in> borel_measurable M"
  unfolding slp_left_branch_complex_terminal_def
  using slp_cauchy_kernel_compose_measurable[OF origin_measurable
      terminal_measurable]
  by measurable

lemma slp_left_branch_complex_block_compose_measurable:
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and origin_measurable[measurable]:
      "origin \<in> borel_measurable M"
    and pos_measurable[measurable]: "pos \<in> borel_measurable M"
    and neg_measurable[measurable]: "neg \<in> borel_measurable M"
  shows
    "(\<lambda>x. slp_left_branch_complex_block cutoff potential
        (origin x) (pos x) (neg x)) \<in> borel_measurable M"
  unfolding slp_left_branch_complex_block_def
  using slp_cauchy_kernel_compose_measurable[OF origin_measurable
      pos_measurable]
    slp_cauchy_kernel_compose_measurable[OF pos_measurable neg_measurable]
  by measurable

lemma slp_left_branch_complex_kernel_list_compose_measurable:
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_value_measurable[measurable]:
      "terminal_value \<in> borel_measurable lborel"
    and origin_measurable[measurable]:
      "origin \<in> borel_measurable M"
    and pos_measurable[measurable]:
      "\<And>k. pos k \<in> borel_measurable M"
    and neg_measurable[measurable]:
      "\<And>k. neg k \<in> borel_measurable M"
    and terminal_measurable[measurable]:
      "terminal \<in> borel_measurable M"
  shows
    "(\<lambda>x. slp_left_branch_complex_kernel_list cutoff potential
        terminal_value (map (\<lambda>k. (pos k x, neg k x)) ks)
        (origin x) (terminal x)) \<in> borel_measurable M"
  using origin_measurable
proof (induction ks arbitrary: origin)
  case Nil
  show ?case
    unfolding list.map(1) slp_left_branch_complex_kernel_list.simps
    by (rule slp_left_branch_complex_terminal_compose_measurable)
      (use Nil.prems in measurable)
next
  case (Cons k ks)
  have tail_measurable[measurable]:
      "(\<lambda>x. slp_left_branch_complex_kernel_list cutoff potential
          terminal_value (map (\<lambda>n. (pos n x, neg n x)) ks)
          (neg k x) (terminal x)) \<in> borel_measurable M"
    by (rule Cons.IH)
      (use neg_measurable in measurable)
  have block_measurable[measurable]:
      "(\<lambda>x. slp_left_branch_complex_block cutoff potential
          (origin x) (pos k x) (neg k x)) \<in> borel_measurable M"
    by (rule slp_left_branch_complex_block_compose_measurable)
      (use Cons.prems pos_measurable neg_measurable in measurable)
  show ?case
    unfolding list.map(2) slp_left_branch_complex_kernel_list.simps
      fst_conv snd_conv
    by measurable
qed

type_synonym 'i slp_left_branch_finite_coordinates =
  "slp_point \<times> (((slp_point^'i) \<times>
    (slp_point^'i)) \<times> slp_point)"

definition slp_left_branch_complex_kernel_joint ::
    "(slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      'i::finite slp_left_branch_finite_coordinates \<Rightarrow> complex"
where
  "slp_left_branch_complex_kernel_joint cutoff potential terminal_value
      coordinates =
    slp_left_branch_complex_kernel_finite cutoff potential terminal_value
      (\<lambda>i. fst (fst (snd coordinates)) $ i)
      (\<lambda>i. snd (fst (snd coordinates)) $ i)
      (fst coordinates) (snd (snd coordinates))"

theorem slp_left_branch_complex_kernel_joint_measurable:
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_value_measurable[measurable]:
      "terminal_value \<in> borel_measurable lborel"
  shows
    "(slp_left_branch_complex_kernel_joint cutoff potential terminal_value ::
      'i::finite slp_left_branch_finite_coordinates \<Rightarrow> complex)
      \<in> borel_measurable lborel"
proof -
  have origin_measurable:
      "(\<lambda>x::'i slp_left_branch_finite_coordinates. fst x)
        \<in> borel_measurable lborel"
    apply (simp only: measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have pos_measurable:
      "\<And>i. (\<lambda>x::'i slp_left_branch_finite_coordinates.
          fst (fst (snd x)) $ i) \<in> borel_measurable lborel"
    apply (simp only: measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have neg_measurable:
      "\<And>i. (\<lambda>x::'i slp_left_branch_finite_coordinates.
          snd (fst (snd x)) $ i) \<in> borel_measurable lborel"
    apply (simp only: measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have terminal_measurable:
      "(\<lambda>x::'i slp_left_branch_finite_coordinates. snd (snd x))
        \<in> borel_measurable lborel"
    apply (simp only: measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  show ?thesis
    unfolding slp_left_branch_complex_kernel_joint_def
      slp_left_branch_complex_kernel_finite_def
      slp_finite_branch_pair_list_def
    by (rule slp_left_branch_complex_kernel_list_compose_measurable[OF
          cutoff_measurable potential_measurable terminal_value_measurable
          origin_measurable pos_measurable neg_measurable
          terminal_measurable])
qed

end
