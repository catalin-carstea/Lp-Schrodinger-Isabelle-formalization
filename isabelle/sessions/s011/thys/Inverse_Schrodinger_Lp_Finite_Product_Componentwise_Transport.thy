theory Inverse_Schrodinger_Lp_Finite_Product_Componentwise_Transport
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cartesian_Euclidean_Product"
begin

section \<open>Componentwise transport of finite product measures\<close>

context product_sigma_finite
begin

lemma slp_distr_PiM_componentwise:
  fixes I :: "'i set"
    and N :: "'i \<Rightarrow> 'b measure"
    and f :: "'i \<Rightarrow> 'a \<Rightarrow> 'b"
  assumes finite_I: "finite I"
    and target_sigma: "\<And>i. sigma_finite_measure (N i)"
    and f_measurable:
      "\<And>i. i \<in> I \<Longrightarrow> f i \<in> measurable (M i) (N i)"
    and f_transport:
      "\<And>i. i \<in> I \<Longrightarrow> distr (M i) (N i) (f i) = N i"
  shows
    "distr (PiM I M) (PiM I N)
        (\<lambda>omega. \<lambda>i\<in>I. f i (omega i)) =
      PiM I N"
proof -
  interpret target_component: sigma_finite_measure "N i" for i
    by (rule target_sigma)
  interpret target: product_sigma_finite N
    by standard
  have map_measurable:
    "(\<lambda>omega. \<lambda>i\<in>I. f i (omega i)) \<in>
      measurable (PiM I M) (PiM I N)"
  proof (rule measurable_PiM_single')
    fix i
    assume i_in: "i \<in> I"
    have component:
      "(\<lambda>omega. omega i) \<in> measurable (PiM I M) (M i)"
      by (rule measurable_component_singleton[OF i_in])
    have composed:
      "(\<lambda>omega. f i (omega i)) \<in>
        measurable (PiM I M) (N i)"
      using measurable_compose[OF component f_measurable[OF i_in]]
      by (simp only: comp_def)
    show "(\<lambda>omega. (\<lambda>i\<in>I. f i (omega i)) i) \<in>
      measurable (PiM I M) (N i)"
      using composed i_in by simp
  next
    show "(\<lambda>omega i. (\<lambda>i\<in>I. f i (omega i)) i) \<in>
      space (PiM I M) \<rightarrow> PiE I (\<lambda>i. space (N i))"
      using f_measurable
      by (auto simp: space_PiM PiE_iff intro: measurable_space)
  qed
  show ?thesis
  proof (rule target.PiM_eqI)
    show "finite I"
      by (rule finite_I)
    fix A
    assume A_sets: "\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets (N i)"
    have preimage:
      "(\<lambda>omega. \<lambda>i\<in>I. f i (omega i)) -` PiE I A \<inter>
          space (PiM I M) =
        PiE I (\<lambda>i. f i -` A i \<inter> space (M i))"
      using A_sets f_measurable
      by (auto simp: space_PiM PiE_iff dest: measurable_space)
    have preimage_sets:
      "f i -` A i \<inter> space (M i) \<in> sets (M i)"
      if "i \<in> I"
      for i
      using measurable_sets[OF f_measurable[OF that] A_sets[OF that]] .
    have target_rectangle:
      "PiE I A \<in> sets (PiM I N)"
      by (rule sets_PiM_I_finite[OF finite_I])
        (rule A_sets)
    have distr_rectangle:
      "emeasure
          (distr (PiM I M) (PiM I N)
            (\<lambda>omega. \<lambda>i\<in>I. f i (omega i)))
          (PiE I A) =
        emeasure (PiM I M)
          (PiE I (\<lambda>i. f i -` A i \<inter> space (M i)))"
      by (subst emeasure_distr[OF map_measurable target_rectangle])
        (simp only: preimage)
    have source_rectangle:
      "emeasure (PiM I M)
          (PiE I (\<lambda>i. f i -` A i \<inter> space (M i))) =
        (\<Prod>i\<in>I. emeasure (M i)
          (f i -` A i \<inter> space (M i)))"
      by (rule emeasure_PiM[OF finite_I])
        (rule preimage_sets)
    have component_measure:
      "emeasure (M i) (f i -` A i \<inter> space (M i)) =
        emeasure (N i) (A i)"
      if "i \<in> I"
      for i
    proof -
      have
        "emeasure (N i) (A i) =
          emeasure (M i) (f i -` A i \<inter> space (M i))"
        using emeasure_distr[
          OF f_measurable[OF that] A_sets[OF that]]
        by (simp only: f_transport[OF that])
      then show ?thesis
        by (rule sym)
    qed
    have product_measure:
      "(\<Prod>i\<in>I. emeasure (M i)
          (f i -` A i \<inter> space (M i))) =
        (\<Prod>i\<in>I. emeasure (N i) (A i))"
      by (rule prod.cong)
        (simp_all add: component_measure)
    show
      "emeasure
          (distr (PiM I M) (PiM I N)
            (\<lambda>omega. \<lambda>i\<in>I. f i (omega i)))
          (PiE I A) =
        (\<Prod>i\<in>I. emeasure (N i) (A i))"
      by (rule trans[OF distr_rectangle])
        (rule trans[OF source_rectangle product_measure])
  qed simp
qed

end

end
