theory Inverse_Schrodinger_Lp_Natural_One_Sided_Born_Identity
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Natural_One_Sided_Root_Integration"
begin

hide_const (open) Commutative_Ring.norm

section \<open>The original natural one-sided Born functional\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_natural_one_sided_born_bracket_identity:
  fixes n :: nat and R C p :: real and X :: "slp_point set"
    and tau :: real and phi :: slp_scalar_field
    and cutoff q Q :: slp_scalar_field
    and orientation :: slp_cauchy_orientation
  assumes R_nonnegative: "0 \<le> R"
    and p_lower: "1 < p" and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel" and X_bounded: "bounded X"
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
  shows "let P = PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure));
             MJ = ((P \<Otimes>\<^sub>M P) \<Otimes>\<^sub>M lborel) \<Otimes>\<^sub>M lborel;
             ps = (\<lambda>z. map (\<lambda>k. (fst (fst (fst z)) k,
               snd (fst (fst z)) k)) [0..<n]);
             s = (\<lambda>z. snd (fst z));
             output = (\<lambda>z. slp_left_branch_output (ps z) (s z));
             phase = (\<lambda>z. slp_left_branch_residual (ps z) (s z));
             A = slp_cauchy_transform orientation q;
             a = slp_natural_one_sided_weighted_amplitude n Q cutoff q
               (\<lambda>_. 1) (\<lambda>_. 1);
             I = (\<lambda>z. exp (\<i> * of_real (tau * phase z)) * a z *
               slp_one_sided_center_average_bracket tau phi A (output z) (s z));
             r = (\<lambda>y x. Q x *
               slp_left_neumann_iterate n tau y cutoff q orientation x)
    in (\<forall>y. integrable lborel (r y)) \<and>
       integrable lborel (\<lambda>y. phi y * integral\<^sup>L lborel (r y)) \<and>
       integrable MJ I \<and>
       slp_left_born_functional n tau phi Q cutoff q orientation =
         integral\<^sup>L MJ I"
proof -
  let ?P = "PiM {..<n} (\<lambda>_::nat. (lborel :: slp_point measure))"
  let ?B = "(?P \<Otimes>\<^sub>M ?P) \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?MJ = "?B \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?ps = "\<lambda>z. map (\<lambda>k.
    (fst (fst (fst z)) k, snd (fst (fst z)) k)) [0..<n]"
  let ?s = "\<lambda>z. snd (fst z)"
  let ?output = "\<lambda>z. slp_left_branch_output (?ps z) (?s z)"
  let ?phase = "\<lambda>z. slp_left_branch_residual (?ps z) (?s z)"
  let ?one = "\<lambda>_::slp_point. (1::complex)"
  let ?A = "slp_cauchy_transform orientation q"
  let ?a = "slp_natural_one_sided_weighted_amplitude n Q cutoff q ?one ?one"
  let ?e = "\<lambda>z. exp (\<i> * of_real (tau * ?phase z))"
  let ?F = "\<lambda>z y. ?e z * ?a z * slp_center_kernel tau (?output z) y *
    (?A (?s z) - ?A y)"
  let ?G = "\<lambda>z y. ?F z y * phi y"
  let ?I = "\<lambda>z. ?e z * ?a z *
    slp_one_sided_center_average_bracket tau phi ?A (?output z) (?s z)"
  let ?r = "\<lambda>y x. Q x *
    slp_left_neumann_iterate n tau y cutoff q orientation x"
  let ?scale = "of_real (tau / pi) :: complex"
  note bracket = slp_natural_one_sided_preaverage_fubini[
    OF R_nonnegative p_lower p_upper X_measurable X_bounded
      cutoff_measurable q_lp Q_lp Q_outside cutoff_bound C_nonnegative
      Q_support cutoff_support q_support phi_test,
    where n=n and orientation=orientation and tau=tau]
  have I_integrable: "integrable ?MJ ?I"
    using bracket by (auto simp only: Let_def)
  have outer_integrable:
    "integrable lborel (\<lambda>y. integral\<^sup>L ?MJ (\<lambda>z. ?G z y))"
    using bracket by (auto simp only: Let_def)
  have preaverage: "?scale * integral\<^sup>L lborel
      (\<lambda>y. integral\<^sup>L ?MJ (\<lambda>z. ?G z y)) = integral\<^sup>L ?MJ ?I"
    using bracket by (auto simp only: Let_def)
  have root_data:
    "integrable lborel (?r y) \<and>
      integral\<^sup>L ?MJ (\<lambda>z. ?F z y) = integral\<^sup>L lborel (?r y)" for y
    using slp_natural_one_sided_preaverage_root_integral[
      OF R_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable q_lp Q_lp Q_outside cutoff_bound C_nonnegative
        Q_support cutoff_support q_support,
      where n=n and orientation=orientation and tau=tau and y=y]
    by (auto simp only: Let_def)
  have root_integrable: "integrable lborel (?r y)" for y
    using root_data[of y] by (rule conjunct1)
  have root_value:
    "integral\<^sup>L ?MJ (\<lambda>z. ?F z y) = integral\<^sup>L lborel (?r y)" for y
    using root_data[of y] by (rule conjunct2)
  have original_inner:
    "integral\<^sup>L ?MJ (\<lambda>z. ?G z y) =
      phi y * integral\<^sup>L lborel (?r y)" for y
    by (simp only: Bochner_Integration.integral_mult_left_zero root_value;
        simp only: mult.commute)
  have original_integrable:
    "integrable lborel (\<lambda>y. phi y * integral\<^sup>L lborel (?r y))"
    using outer_integrable by (simp only: original_inner)
  have normalization:
    "(of_real tau :: complex) * inverse (of_real pi) = of_real (tau / pi)"
    by (simp add: divide_inverse)
  have exact:
    "slp_left_born_functional n tau phi Q cutoff q orientation =
      integral\<^sup>L ?MJ ?I"
    using preaverage unfolding slp_left_born_functional_def
    by (simp only: original_inner normalization)
  show ?thesis unfolding Let_def
    using root_integrable original_integrable I_integrable exact by blast
qed

end

end
