theory Inverse_Schrodinger_Lp_Cauchy_Local_Lp_Two
  imports Inverse_Schrodinger_Lp_Cauchy_Local_Lp_Below_Two
begin

section \<open>Global exponent descent for bounded-support fields\<close>

lemma slp_nonzero_set_measurable:
  assumes f_measurable: "f \<in> borel_measurable lborel"
  shows "{x. f x \<noteq> (0::complex)} \<in> sets lborel"
proof -
  have zero_preimage:
    "f -` {0} \<inter> space lborel \<in> sets lborel"
    using f_measurable by measurable
  have "{x. f x \<noteq> 0} = space lborel - (f -` {0} \<inter> space lborel)"
    by auto
  then show ?thesis
    using zero_preimage by simp
qed

lemma slp_restrict_field_nonzero_set [simp]:
  "slp_restrict_field {x. f x \<noteq> 0} f = f"
  by (rule ext) (simp add: slp_restrict_field_def)

lemma aim_complex_lp_on_plane_mono_exponent_bounded_support:
  assumes p_positive: "0 < p"
    and exponent_order: "p \<le> q"
    and f_support: "bounded {x. f x \<noteq> 0}"
    and f_lp: "aim_complex_lp_on_plane q f"
  shows "aim_complex_lp_on_plane p f"
proof -
  have f_measurable: "f \<in> borel_measurable lborel"
    using f_lp unfolding aim_complex_lp_on_plane_def by auto
  have nonzero_measurable: "{x. f x \<noteq> 0} \<in> sets lborel"
    by (rule slp_nonzero_set_measurable[OF f_measurable])
  have restricted_q:
    "slp_complex_lp_on q {x. f x \<noteq> 0} f"
    unfolding slp_complex_lp_on_def
    using f_lp by simp
  have restricted_lp:
    "slp_complex_lp_on p {x. f x \<noteq> 0} f"
    by (rule slp_complex_lp_on_mono_exponent_bounded[OF
          p_positive exponent_order nonzero_measurable f_support])
       (rule restricted_q)
  show ?thesis
    using restricted_lp
    unfolding slp_complex_lp_on_def by simp
qed

section \<open>The endpoint local zero-order term\<close>

lemma slp_hls_target_exponent_three_halves:
  "aim_hls_target_exponent (3 / 2) = (6::real)"
  unfolding aim_hls_target_exponent_def
  by simp

context aim_planar_hls_cauchy
begin

theorem slp_both_cauchy_local_lp_two:
  assumes f_lp: "aim_complex_lp_on_plane (2::real) f"
    and f_support: "bounded {x. f x \<noteq> 0}"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
  shows "slp_complex_lp_on 2 X (slp_dbar_inverse f) \<and>
    slp_complex_lp_on 2 X (slp_partial_inverse f)"
proof -
  have input_descent:
    "aim_complex_lp_on_plane (3 / 2) f"
    by (rule aim_complex_lp_on_plane_mono_exponent_bounded_support)
       (use f_support f_lp in simp_all)
  have target_memberships:
    "slp_complex_lp_on 6 X (slp_dbar_inverse f) \<and>
      slp_complex_lp_on 6 X (slp_partial_inverse f)"
    using slp_both_cauchy_hls_sum_on_measurable input_descent
      X_measurable slp_hls_target_exponent_three_halves
    by force
  have dbar_local: "slp_complex_lp_on 2 X (slp_dbar_inverse f)"
    by (rule slp_complex_lp_on_mono_exponent_bounded[
          where p = 2 and q = 6, OF _ _ X_measurable X_bounded])
       (use target_memberships in simp_all)
  have partial_local: "slp_complex_lp_on 2 X (slp_partial_inverse f)"
    by (rule slp_complex_lp_on_mono_exponent_bounded[
          where p = 2 and q = 6, OF _ _ X_measurable X_bounded])
       (use target_memberships in simp_all)
  show ?thesis
    using dbar_local partial_local by blast
qed

end

end
