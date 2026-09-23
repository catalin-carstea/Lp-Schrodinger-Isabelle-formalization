theory Inverse_Schrodinger_Lp_Beurling_Lp
  imports
    Inverse_Schrodinger_Lp_Cauchy_HLS_Conjugate
    "Paper_ISLP_AIM_Planar_Beurling_Lp.AIM_Planar_Beurling_Lp_Interface"
begin

section \<open>Two orientations of the planar Beurling transform\<close>

definition slp_beurling_pv_exists ::
  "aim_planar_field \<Rightarrow> aim_planar_point \<Rightarrow> bool"
where
  "slp_beurling_pv_exists f z \<longleftrightarrow>
    aim_planar_beurling_pv_exists f z"

definition slp_beurling_transform ::
  "aim_planar_field \<Rightarrow> aim_planar_field"
where
  "slp_beurling_transform f = aim_planar_beurling_transform f"

definition slp_opposite_beurling_pv_exists ::
  "aim_planar_field \<Rightarrow> aim_planar_point \<Rightarrow> bool"
where
  "slp_opposite_beurling_pv_exists f z \<longleftrightarrow>
    slp_beurling_pv_exists (\<lambda>y. cnj (f y)) z"

definition slp_opposite_beurling_transform ::
  "aim_planar_field \<Rightarrow> aim_planar_field"
where
  "slp_opposite_beurling_transform f =
    (\<lambda>z. cnj (slp_beurling_transform (\<lambda>y. cnj (f y)) z))"

context aim_planar_beurling_lp
begin

theorem slp_both_beurling_lp:
  "\<forall>p::real. 1 < p \<longrightarrow>
    (\<exists>S_p::real. 0 < S_p \<and>
      (\<forall>f. aim_complex_lp_on_plane p f \<longrightarrow>
        (AE z in lborel. slp_beurling_pv_exists f z) \<and>
        aim_complex_lp_on_plane p (slp_beurling_transform f) \<and>
        aim_complex_lp_norm p (slp_beurling_transform f)
          \<le> S_p * aim_complex_lp_norm p f \<and>
        (AE z in lborel. slp_opposite_beurling_pv_exists f z) \<and>
        aim_complex_lp_on_plane p (slp_opposite_beurling_transform f) \<and>
        aim_complex_lp_norm p (slp_opposite_beurling_transform f)
          \<le> S_p * aim_complex_lp_norm p f))"
proof (intro allI impI)
  fix p :: real
  assume p_range: "1 < p"
  obtain S_p :: real where S_p_positive: "0 < S_p"
    and S_p_bound:
      "\<And>f. aim_complex_lp_on_plane p f \<Longrightarrow>
        (AE z in lborel. aim_planar_beurling_pv_exists f z) \<and>
        aim_complex_lp_on_plane p (aim_planar_beurling_transform f) \<and>
        aim_complex_lp_norm p (aim_planar_beurling_transform f)
          \<le> S_p * aim_complex_lp_norm p f"
    using aim_planar_beurling_lp p_range
    unfolding aim_planar_beurling_lp_claim_def
    by blast
  have all_bound:
    "\<forall>f. aim_complex_lp_on_plane p f \<longrightarrow>
        (AE z in lborel. slp_beurling_pv_exists f z) \<and>
        aim_complex_lp_on_plane p (slp_beurling_transform f) \<and>
        aim_complex_lp_norm p (slp_beurling_transform f)
          \<le> S_p * aim_complex_lp_norm p f \<and>
        (AE z in lborel. slp_opposite_beurling_pv_exists f z) \<and>
        aim_complex_lp_on_plane p (slp_opposite_beurling_transform f) \<and>
        aim_complex_lp_norm p (slp_opposite_beurling_transform f)
          \<le> S_p * aim_complex_lp_norm p f"
  proof (intro allI impI)
    fix f
    assume f_lp: "aim_complex_lp_on_plane p f"
    have forward_result:
      "(AE z in lborel. slp_beurling_pv_exists f z) \<and>
        aim_complex_lp_on_plane p (slp_beurling_transform f) \<and>
        aim_complex_lp_norm p (slp_beurling_transform f)
          \<le> S_p * aim_complex_lp_norm p f"
      using S_p_bound[OF f_lp]
      by (simp only: slp_beurling_pv_exists_def
          slp_beurling_transform_def)
    have conjugated_f_lp:
      "aim_complex_lp_on_plane p (\<lambda>y. cnj (f y))"
      using f_lp by simp
    have opposite_source_result:
      "(AE z in lborel.
          aim_planar_beurling_pv_exists (\<lambda>y. cnj (f y)) z) \<and>
        aim_complex_lp_on_plane p
          (aim_planar_beurling_transform (\<lambda>y. cnj (f y))) \<and>
        aim_complex_lp_norm p
            (aim_planar_beurling_transform (\<lambda>y. cnj (f y)))
          \<le> S_p * aim_complex_lp_norm p (\<lambda>y. cnj (f y))"
      by (rule S_p_bound[OF conjugated_f_lp])
    have opposite_result:
      "(AE z in lborel. slp_opposite_beurling_pv_exists f z) \<and>
        aim_complex_lp_on_plane p (slp_opposite_beurling_transform f) \<and>
        aim_complex_lp_norm p (slp_opposite_beurling_transform f)
          \<le> S_p * aim_complex_lp_norm p f"
      using opposite_source_result
      by (simp only: slp_opposite_beurling_pv_exists_def
          slp_opposite_beurling_transform_def
          slp_beurling_pv_exists_def slp_beurling_transform_def
          aim_complex_lp_on_plane_cnj_iff aim_complex_lp_norm_cnj)
    show "(AE z in lborel. slp_beurling_pv_exists f z) \<and>
        aim_complex_lp_on_plane p (slp_beurling_transform f) \<and>
        aim_complex_lp_norm p (slp_beurling_transform f)
          \<le> S_p * aim_complex_lp_norm p f \<and>
        (AE z in lborel. slp_opposite_beurling_pv_exists f z) \<and>
        aim_complex_lp_on_plane p (slp_opposite_beurling_transform f) \<and>
        aim_complex_lp_norm p (slp_opposite_beurling_transform f)
          \<le> S_p * aim_complex_lp_norm p f"
      using forward_result opposite_result by blast
  qed
  show "\<exists>T::real. 0 < T \<and>
      (\<forall>f. aim_complex_lp_on_plane p f \<longrightarrow>
        (AE z in lborel. slp_beurling_pv_exists f z) \<and>
        aim_complex_lp_on_plane p (slp_beurling_transform f) \<and>
        aim_complex_lp_norm p (slp_beurling_transform f)
          \<le> T * aim_complex_lp_norm p f \<and>
        (AE z in lborel. slp_opposite_beurling_pv_exists f z) \<and>
        aim_complex_lp_on_plane p (slp_opposite_beurling_transform f) \<and>
        aim_complex_lp_norm p (slp_opposite_beurling_transform f)
          \<le> T * aim_complex_lp_norm p f)"
  proof (rule exI[where x = S_p])
    show "0 < S_p \<and>
        (\<forall>f. aim_complex_lp_on_plane p f \<longrightarrow>
          (AE z in lborel. slp_beurling_pv_exists f z) \<and>
          aim_complex_lp_on_plane p (slp_beurling_transform f) \<and>
          aim_complex_lp_norm p (slp_beurling_transform f)
            \<le> S_p * aim_complex_lp_norm p f \<and>
          (AE z in lborel. slp_opposite_beurling_pv_exists f z) \<and>
          aim_complex_lp_on_plane p (slp_opposite_beurling_transform f) \<and>
          aim_complex_lp_norm p (slp_opposite_beurling_transform f)
            \<le> S_p * aim_complex_lp_norm p f)"
      by (rule conjI[OF S_p_positive all_bound])
  qed
qed

end

end
