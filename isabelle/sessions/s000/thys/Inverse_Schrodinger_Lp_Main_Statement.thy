theory Inverse_Schrodinger_Lp_Main_Statement
  imports Inverse_Schrodinger_Lp_Setup
begin

section \<open>Principal statement\<close>

text \<open>
  This predicate preserves the theorem's global parameter order.  Isabelle's
  real exponent is always finite, so @{term "1 < p"} represents the source
  condition @{text "1 < p < infinity"}.  The equality premise compares the
  complex-bilinear weak Dirichlet-to-Neumann forms on quotient traces, and the
  conclusion is equality of the two potential representatives almost
  everywhere on the domain.
\<close>

definition slp_main_uniqueness_claim ::
  "real \<Rightarrow> slp_point set \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_scalar_field \<Rightarrow> bool"
where
  "slp_main_uniqueness_claim p Omega V V_tilde \<longleftrightarrow>
    (1 < p \<and>
     slp_bounded_smooth_domain Omega \<and>
     slp_complex_lp_on p Omega V \<and>
     slp_complex_lp_on p Omega V_tilde \<and>
     slp_zero_not_dirichlet_eigenvalue Omega V \<and>
     slp_zero_not_dirichlet_eigenvalue Omega V_tilde \<and>
     slp_weak_dn_equal Omega V V_tilde)
    \<longrightarrow> slp_potential_ae_equal Omega V V_tilde"

end
