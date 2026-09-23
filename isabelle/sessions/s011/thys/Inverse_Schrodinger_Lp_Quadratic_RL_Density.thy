theory Inverse_Schrodinger_Lp_Quadratic_RL_Density
  imports
    Inverse_Schrodinger_Lp_Quadratic_RL_Closure
    "Paper_ISLP_Evans_Compact_Smooth_L1_Density.Evans_Compact_Smooth_L1_Density_Interface"
begin

section \<open>Quadratic decay for arbitrary integrable amplitudes\<close>

context hormander_quadratic_stationary_phase_decay
begin

lemma slp_quadratic_decay_integrable:
  fixes A :: "real^'n::finite^'n"
    and F :: "real^'n \<Rightarrow> complex"
  assumes density:
      "evans_compact_smooth_l1_density_claim TYPE('n)"
    and symmetric: "hormander_real_symmetric_matrix A"
    and nondegenerate: "hormander_real_nondegenerate_matrix A"
    and F_integrable: "integrable lborel F"
  shows
    "((\<lambda>omega. hormander_quadratic_oscillatory_integral A F omega)
      \<longlongrightarrow> 0) at_top"
proof (rule slp_quadratic_decay_of_l1_approximation[
    OF symmetric nondegenerate F_integrable])
  fix epsilon :: real
  assume epsilon_positive: "0 < epsilon"
  show "\<exists>u. hormander_compact_smooth_amplitude u \<and>
      integral\<^sup>L lborel (\<lambda>x. norm (F x - u x)) < epsilon"
    using density F_integrable epsilon_positive
    unfolding evans_compact_smooth_l1_density_claim_def
    by blast
qed

end

end
