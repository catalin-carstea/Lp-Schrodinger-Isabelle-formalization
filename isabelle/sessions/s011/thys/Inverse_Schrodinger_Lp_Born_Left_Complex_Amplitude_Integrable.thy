theory Inverse_Schrodinger_Lp_Born_Left_Complex_Amplitude_Integrable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Left_Complex_Amplitude_Support"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_One_Sided_Passive_Root_Decay"
begin

section \<open>Finite positive mass controls the exact packed amplitude\<close>

lemma slp_left_branch_complex_amplitude_packed_le_positive:
  fixes branch_coord :: "real^((unit + ('i::finite + 'i)) \<times> bool)"
  assumes B_nonnegative: "0 \<le> B"
    and root_support: "\<And>x. root_weight x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and potential_support: "\<And>x. potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
  shows
    "ennreal (norm (slp_left_branch_complex_amplitude_packed root_weight
        cutoff potential terminal_value output_factor root_coord
        branch_coord)) \<le>
      slp_left_branch_positive_amplitude_packed (2 * B) root_weight cutoff
        potential terminal_value output_factor root_coord branch_coord"
proof (cases "slp_left_branch_complex_amplitude_packed root_weight cutoff
    potential terminal_value output_factor root_coord branch_coord = 0")
  case True
  show ?thesis
    by (simp add: True)
next
  case False
  have chain:
      "slp_left_branch_radius_chain_packed (2 * B) root_coord branch_coord"
    by (rule slp_left_branch_complex_amplitude_packed_support_chain[OF
          B_nonnegative root_support cutoff_support potential_support False])
  have equality:
      "ennreal (norm (slp_left_branch_complex_amplitude_packed root_weight
          cutoff potential terminal_value output_factor root_coord
          branch_coord)) =
        slp_left_branch_positive_amplitude_packed (2 * B) root_weight cutoff
          potential terminal_value output_factor root_coord branch_coord"
    by (rule slp_left_branch_complex_amplitude_packed_positive_weight[OF chain])
  show ?thesis
    by (simp only: equality order_refl)
qed

theorem slp_left_branch_complex_amplitude_packed_integrable:
  fixes branch_dummy :: "'i::finite itself"
  assumes B_nonnegative: "0 \<le> B"
    and root_support: "\<And>x. root_weight x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and potential_support: "\<And>x. potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
    and terminal_value_measurable:
      "terminal_value \<in> borel_measurable lborel"
    and output_factor_measurable:
      "output_factor \<in> borel_measurable lborel"
    and majorant_finite:
      "(\<integral>\<^sup>+ coordinates.
        case_prod (slp_left_branch_positive_amplitude_packed (2 * B)
          root_weight cutoff potential terminal_value output_factor)
          coordinates \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
            (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) <
        \<infinity>"
  shows
    "integrable ((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
        (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))
      (case_prod (slp_left_branch_complex_amplitude_packed root_weight cutoff
        potential terminal_value output_factor) ::
          (real^bool) \<times>
            (real^((unit + ('i + 'i)) \<times> bool)) \<Rightarrow> complex)"
proof (unfold integrable_iff_bounded, intro conjI)
  show
    "(case_prod (slp_left_branch_complex_amplitude_packed root_weight cutoff
        potential terminal_value output_factor) ::
          (real^bool) \<times>
            (real^((unit + ('i + 'i)) \<times> bool)) \<Rightarrow> complex)
      \<in> borel_measurable ((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
        (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))"
    by (rule slp_left_branch_complex_amplitude_packed_measurable[OF
          root_weight_measurable cutoff_measurable potential_measurable
          terminal_value_measurable output_factor_measurable])
  have pointwise:
      "\<And>coordinates :: (real^bool) \<times>
          (real^((unit + ('i + 'i)) \<times> bool)).
        ennreal (norm (case_prod
          (slp_left_branch_complex_amplitude_packed root_weight cutoff
            potential terminal_value output_factor) coordinates)) \<le>
        case_prod (slp_left_branch_positive_amplitude_packed (2 * B)
          root_weight cutoff potential terminal_value output_factor)
          coordinates"
  proof -
    fix coordinates :: "(real^bool) \<times>
      (real^((unit + ('i + 'i)) \<times> bool))"
    obtain root_coord branch_coord where coordinates:
        "coordinates = (root_coord, branch_coord)"
      by (cases coordinates)
    show
      "ennreal (norm (case_prod
          (slp_left_branch_complex_amplitude_packed root_weight cutoff
            potential terminal_value output_factor) coordinates)) \<le>
        case_prod (slp_left_branch_positive_amplitude_packed (2 * B)
          root_weight cutoff potential terminal_value output_factor)
          coordinates"
      unfolding coordinates case_prod_conv
      by (rule slp_left_branch_complex_amplitude_packed_le_positive[OF
            B_nonnegative root_support cutoff_support potential_support])
  qed
  have mass_bound:
      "(\<integral>\<^sup>+ coordinates.
        ennreal (norm (case_prod
          (slp_left_branch_complex_amplitude_packed root_weight cutoff
            potential terminal_value output_factor) coordinates))
          \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
            (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) \<le>
       (\<integral>\<^sup>+ coordinates.
        case_prod (slp_left_branch_positive_amplitude_packed (2 * B)
          root_weight cutoff potential terminal_value output_factor)
          coordinates \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
            (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure)))"
  proof (rule nn_integral_mono_AE)
    show
      "AE coordinates in ((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
          (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure)).
        ennreal (norm (case_prod
          (slp_left_branch_complex_amplitude_packed root_weight cutoff
            potential terminal_value output_factor) coordinates)) \<le>
        case_prod (slp_left_branch_positive_amplitude_packed (2 * B)
          root_weight cutoff potential terminal_value output_factor)
          coordinates"
      by (rule always_eventually) (rule allI, rule pointwise)
  qed
  show
    "(\<integral>\<^sup>+ coordinates.
      ennreal (norm (case_prod
        (slp_left_branch_complex_amplitude_packed root_weight cutoff
          potential terminal_value output_factor) coordinates))
        \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
          (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) <
      \<infinity>"
    by (rule le_less_trans[OF mass_bound majorant_finite])
qed

theorem slp_left_branch_complex_amplitude_packed_residual_decay:
  fixes branch_dummy :: "'i::finite itself"
  assumes stationary_phase:
      "hormander_quadratic_stationary_phase_decay_claim
        TYPE(('i + 'i) \<times> bool)"
    and density:
      "evans_compact_smooth_l1_density_claim TYPE(('i + 'i) \<times> bool)"
    and B_nonnegative: "0 \<le> B"
    and root_support: "\<And>x. root_weight x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and potential_support: "\<And>x. potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
    and terminal_value_measurable:
      "terminal_value \<in> borel_measurable lborel"
    and output_factor_measurable:
      "output_factor \<in> borel_measurable lborel"
    and majorant_finite:
      "(\<integral>\<^sup>+ coordinates.
        case_prod (slp_left_branch_positive_amplitude_packed (2 * B)
          root_weight cutoff potential terminal_value output_factor)
          coordinates \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
            (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) <
        \<infinity>"
  shows
    "((\<lambda>omega. integral\<^sup>L
      ((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
        (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))
      (\<lambda>(root, branch). exp (\<i> * of_real
        (omega * slp_one_sided_packed_residual branch)) *
        slp_left_branch_complex_amplitude_packed root_weight cutoff potential
          terminal_value output_factor root branch))
      \<longlongrightarrow> 0) at_top"
proof -
  have amplitude_integrable:
    "integrable ((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
        (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))
      (case_prod (slp_left_branch_complex_amplitude_packed root_weight cutoff
        potential terminal_value output_factor) ::
          (real^bool) \<times>
            (real^((unit + ('i + 'i)) \<times> bool)) \<Rightarrow> complex)"
    by (rule slp_left_branch_complex_amplitude_packed_integrable[OF
          B_nonnegative root_support cutoff_support potential_support
          root_weight_measurable cutoff_measurable potential_measurable
          terminal_value_measurable output_factor_measurable majorant_finite])
  have decay:
      "((\<lambda>omega. integral\<^sup>L
        ((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
          (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))
        (\<lambda>(root, branch). exp (\<i> * of_real
          (omega * slp_one_sided_packed_residual branch)) *
          slp_left_branch_complex_amplitude_packed root_weight cutoff potential
            terminal_value output_factor root branch))
        \<longlongrightarrow> 0) at_top"
    by (rule slp_one_sided_packed_residual_passive_root_decay[where
          F = "(slp_left_branch_complex_amplitude_packed root_weight cutoff
            potential terminal_value output_factor ::
              (real^bool) \<Rightarrow>
                (real^((unit + ('i + 'i)) \<times> bool)) \<Rightarrow> complex)", OF
          stationary_phase density amplitude_integrable])
  show ?thesis
    by (rule decay)
qed

end
