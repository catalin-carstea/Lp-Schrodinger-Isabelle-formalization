theory Inverse_Schrodinger_Lp_Fixed_One_Sided_Cancellations
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Born_Finite_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Right_Born_Finite_Decay"
begin

section \<open>Fixed one-sided Born cancellations\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_fixed_one_sided_born_cancellations:
  fixes left_dummy :: "'i::finite itself"
    and right_dummy :: "'j::finite itself"
    and B C p :: real
    and X :: "slp_point set"
    and cutoff left_potential right_potential phi ::
      "slp_point \<Rightarrow> complex"
    and left_orientation right_orientation :: slp_cauchy_orientation
  assumes stationary_left:
      "hormander_quadratic_stationary_phase_decay_claim
        TYPE(('i + 'i) \<times> bool)"
    and density_left:
      "evans_compact_smooth_l1_density_claim TYPE(('i + 'i) \<times> bool)"
    and stationary_right:
      "hormander_quadratic_stationary_phase_decay_claim
        TYPE(('j + 'j) \<times> bool)"
    and density_right:
      "evans_compact_smooth_l1_density_claim TYPE(('j + 'j) \<times> bool)"
    and B_nonnegative: "0 \<le> B"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and left_potential_lp: "aim_complex_lp_on_plane p left_potential"
    and right_potential_lp: "aim_complex_lp_on_plane p right_potential"
    and left_potential_outside:
      "\<And>x. x \<notin> X \<Longrightarrow> left_potential x = 0"
    and right_potential_outside:
      "\<And>x. x \<notin> X \<Longrightarrow> right_potential x = 0"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and left_potential_support:
      "\<And>x. left_potential x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and right_potential_support:
      "\<And>x. right_potential x \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm x \<le> B"
    and phi_test: "slp_test_function_on UNIV phi"
    and uniform_convergence:
      "uniform_limit UNIV (\<lambda>tau. slp_center_average tau phi) phi at_top"
    and left_source_l2:
      "aim_complex_lp_on_plane 2
        (\<lambda>u. phi u *
          slp_cauchy_transform left_orientation left_potential u)"
    and right_source_l2:
      "aim_complex_lp_on_plane 2
        (\<lambda>u. phi u *
          slp_cauchy_transform right_orientation right_potential u)"
    and left_center_average_l2:
      "\<And>tau. aim_complex_lp_on_plane 2
        (slp_center_average tau
          (\<lambda>u. phi u *
            slp_cauchy_transform left_orientation left_potential u))"
    and right_center_average_l2:
      "\<And>tau. aim_complex_lp_on_plane 2
        (slp_center_average tau
          (\<lambda>u. phi u *
            slp_cauchy_transform right_orientation right_potential u))"
    and left_center_average_error_square_decay:
      "((\<lambda>tau. \<integral>\<^sup>+x.
          ennreal (Real_Vector_Spaces.norm
            (slp_center_average tau
                (\<lambda>u. phi u *
                  slp_cauchy_transform left_orientation left_potential u)
                x -
              phi x *
                slp_cauchy_transform left_orientation left_potential x)) ^ 2
          \<partial>lborel) \<longlongrightarrow> 0) at_top"
    and right_center_average_error_square_decay:
      "((\<lambda>tau. \<integral>\<^sup>+x.
          ennreal (Real_Vector_Spaces.norm
            (slp_center_average tau
                (\<lambda>u. phi u *
                  slp_cauchy_transform right_orientation right_potential u)
                x -
              phi x *
                slp_cauchy_transform right_orientation right_potential x)) ^ 2
          \<partial>lborel) \<longlongrightarrow> 0) at_top"
  shows
    "((\<lambda>tau.
        slp_left_born_functional CARD('i) tau phi left_potential cutoff
          left_potential left_orientation)
      \<longlongrightarrow> 0) at_top \<and>
     ((\<lambda>tau.
        slp_right_born_functional CARD('j) tau phi right_potential cutoff
          right_potential right_orientation)
      \<longlongrightarrow> 0) at_top"
proof
  show
    "((\<lambda>tau.
        slp_left_born_functional CARD('i) tau phi left_potential cutoff
          left_potential left_orientation)
      \<longlongrightarrow> 0) at_top"
    by (rule slp_left_born_functional_finite_decay[
          where B = B and C = C and p = p and X = X,
          OF stationary_left density_left B_nonnegative p_lower p_upper
            X_measurable X_bounded left_potential_lp left_potential_outside
            cutoff_measurable cutoff_bound C_nonnegative cutoff_support
            left_potential_support phi_test uniform_convergence left_source_l2
            left_center_average_l2 left_center_average_error_square_decay])
  show
    "((\<lambda>tau.
        slp_right_born_functional CARD('j) tau phi right_potential cutoff
          right_potential right_orientation)
      \<longlongrightarrow> 0) at_top"
    by (rule slp_right_born_functional_finite_decay[
          where B = B and C = C and p = p and X = X,
          OF stationary_right density_right B_nonnegative p_lower p_upper
            X_measurable X_bounded right_potential_lp right_potential_outside
            cutoff_measurable cutoff_bound C_nonnegative cutoff_support
            right_potential_support phi_test uniform_convergence
            right_source_l2 right_center_average_l2
            right_center_average_error_square_decay])
qed

end

end
