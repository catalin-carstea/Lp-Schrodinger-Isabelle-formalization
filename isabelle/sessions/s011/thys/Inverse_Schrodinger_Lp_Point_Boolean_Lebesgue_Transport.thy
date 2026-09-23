theory Inverse_Schrodinger_Lp_Point_Boolean_Lebesgue_Transport
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cartesian_Lebesgue_Reindex"
begin

section \<open>Planar point coordinates as Boolean Cartesian coordinates\<close>

definition slp_bool_to_point_index :: "bool \<Rightarrow> 2"
where
  "slp_bool_to_point_index b = (if b then 1 else 0)"

lemma slp_bool_to_point_index_bij:
  "bij slp_bool_to_point_index"
proof (rule bijI)
  show "inj slp_bool_to_point_index"
  proof (rule injI)
    fix x y :: bool
    show "slp_bool_to_point_index x = slp_bool_to_point_index y \<Longrightarrow> x = y"
      by (cases x; cases y)
        (simp_all add: slp_bool_to_point_index_def)
  qed
  show "surj slp_bool_to_point_index"
  proof (rule surjI[where f = "\<lambda>k::2. k = 1"])
    fix k :: 2
    have k_cases: "k = 1 \<or> k = 2"
      by (rule exhaust_2)
    from k_cases show "slp_bool_to_point_index (k = 1) = k"
    proof
      assume "k = 1"
      then show ?thesis
        by (simp add: slp_bool_to_point_index_def)
    next
      assume "k = 2"
      then show ?thesis
        by (simp add: slp_bool_to_point_index_def)
    qed
  qed
qed

lemma slp_point_boolean_coordinate_reindex:
  "(\<lambda>x. slp_complex_coordinate_pack (slp_point_as_complex x)) =
    (\<lambda>x::slp_point. \<chi> b. x $ slp_bool_to_point_index b)"
proof (rule ext)
  fix x :: slp_point
  show "slp_complex_coordinate_pack (slp_point_as_complex x) =
      (\<chi> b. x $ slp_bool_to_point_index b)"
    unfolding vec_eq_iff
  proof
    fix b :: bool
    show "slp_complex_coordinate_pack (slp_point_as_complex x) $ b =
        (\<chi> b. x $ slp_bool_to_point_index b) $ b"
      by (cases b)
        (simp_all only: slp_complex_coordinate_pack_def
          slp_point_as_complex_def slp_bool_to_point_index_def
          vec_lambda_beta bool.distinct refl if_True if_False complex.sel)
  qed
qed

theorem slp_point_boolean_distr_lborel:
  "distr (lborel :: slp_point measure) (lborel :: (real^bool) measure)
      (\<lambda>x. slp_complex_coordinate_pack (slp_point_as_complex x)) =
    (lborel :: (real^bool) measure)"
proof -
  have reindex:
    "distr (lborel :: slp_point measure) borel
        (\<lambda>x::slp_point. \<chi> b. x $ slp_bool_to_point_index b) =
      (lborel :: (real^bool) measure)"
    by (rule slp_lborel_cartesian_coordinate_reindex)
      (rule slp_bool_to_point_index_bij)
  have target_change:
    "distr (lborel :: slp_point measure) (lborel :: (real^bool) measure)
        (\<lambda>x. slp_complex_coordinate_pack (slp_point_as_complex x)) =
      distr (lborel :: slp_point measure) borel
        (\<lambda>x. slp_complex_coordinate_pack (slp_point_as_complex x))"
  proof (rule distr_cong)
    show "(lborel :: slp_point measure) = lborel"
      by (rule refl)
    show "sets (lborel :: (real^bool) measure) = sets borel"
      by (rule sets_lborel)
    show "slp_complex_coordinate_pack (slp_point_as_complex x) =
        slp_complex_coordinate_pack (slp_point_as_complex x)"
      for x :: slp_point
      by (rule refl)
  qed
  show ?thesis
    using target_change reindex
    by (simp only: slp_point_boolean_coordinate_reindex)
qed

end
