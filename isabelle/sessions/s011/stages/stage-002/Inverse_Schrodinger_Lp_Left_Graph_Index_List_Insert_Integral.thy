theory Inverse_Schrodinger_Lp_Left_Graph_Index_List_Insert_Integral
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Left_Graph_Index_List_Kernel"
begin

section \<open>Inserted-head transport for an index-list graph integral\<close>

theorem slp_integral_graph_indices_insert_head:
  fixes M :: "'i \<Rightarrow> slp_point measure"
  assumes M_sigma: "product_sigma_finite M"
    and finite_I: "finite I"
    and i_notin: "i \<notin> I"
    and graph_integrable:
      "integrable
        (((PiM (insert i I) M) \<Otimes>\<^sub>M (PiM (insert i I) M))
          \<Otimes>\<^sub>M (lborel :: slp_point measure))
        (slp_left_branch_oscillatory_graph_kernel_indices (i # indices) tau
          center cutoff potential terminal_value origin)"
  shows
    "integral\<^sup>L
        (((PiM (insert i I) M) \<Otimes>\<^sub>M (PiM (insert i I) M))
          \<Otimes>\<^sub>M (lborel :: slp_point measure))
        (slp_left_branch_oscillatory_graph_kernel_indices (i # indices) tau
          center cutoff potential terminal_value origin) =
      integral\<^sup>L
        ((M i \<Otimes>\<^sub>M M i) \<Otimes>\<^sub>M
          ((PiM I M) \<Otimes>\<^sub>M (PiM I M)))
        (\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)).
          integral\<^sup>L (lborel :: slp_point measure)
            (\<lambda>terminal.
              slp_left_branch_oscillatory_graph_kernel_indices
                (i # indices) tau center cutoff potential terminal_value origin
                ((pos_tail(i := pos_head), neg_tail(i := neg_head)),
                  terminal)))"
proof -
  let ?F = "PiM (insert i I) M"
  let ?MF = "?F \<Otimes>\<^sub>M ?F"
  let ?MA = "?MF \<Otimes>\<^sub>M (lborel :: slp_point measure)"
  let ?kernel =
    "slp_left_branch_oscillatory_graph_kernel_indices (i # indices) tau
      center cutoff potential terminal_value origin"
  let ?terminal_integral =
    "\<lambda>families. integral\<^sup>L (lborel :: slp_point measure)
      (\<lambda>terminal. ?kernel (families, terminal))"
  interpret product: product_sigma_finite M
    by (rule M_sigma)
  have F_sigma: "sigma_finite_measure ?F"
    by (rule product.sigma_finite) (use finite_I in simp)
  interpret F: sigma_finite_measure ?F
    by (rule F_sigma)
  interpret families: pair_sigma_finite ?F ?F ..
  have MF_sigma: "sigma_finite_measure ?MF"
    by standard
  interpret MF: sigma_finite_measure ?MF
    by (rule MF_sigma)
  interpret all_coordinates:
    pair_sigma_finite ?MF "(lborel :: slp_point measure)" ..
  have terminal_integrable:
      "integrable ?MF ?terminal_integral"
    using all_coordinates.integrable_fst'[OF graph_integrable]
    by simp
  have terminal_split:
      "integral\<^sup>L ?MA ?kernel =
        integral\<^sup>L ?MF ?terminal_integral"
    using all_coordinates.integral_fst'[OF graph_integrable]
    by simp
  have inserted_split:
      "integral\<^sup>L ?MF ?terminal_integral =
        integral\<^sup>L
          ((M i \<Otimes>\<^sub>M M i) \<Otimes>\<^sub>M
            ((PiM I M) \<Otimes>\<^sub>M (PiM I M)))
          (\<lambda>((pos_head, neg_head), (pos_tail, neg_tail)).
            ?terminal_integral
              (pos_tail(i := pos_head), neg_tail(i := neg_head)))"
    by (rule product.slp_integral_inserted_pair_heads_tails[OF
          finite_I i_notin terminal_integrable])
  show ?thesis
    using terminal_split inserted_split by simp
qed

end
