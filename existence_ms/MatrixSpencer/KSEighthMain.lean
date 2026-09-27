import MatrixSpencer.KSEighthVertex

/-! The full signing conclusion from the original one-eighth-cube proof. -/

namespace MatrixSpencer

theorem kadison_singer_eighth : ksEighthStatement := by
  apply KSFinalAssembly.statement_of_positive_dimension_vector_signings (by norm_num : (0 : ℝ) ≤ 144)
  intro N d hd ε hε v hparseval hbound
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  apply KSFinalAssembly.eighth_signing_of_maxFrozen_vertex v hparseval hε hbound
  intro x hx
  exact KSEighthVertex.maxFrozen_isVertex v (ksRegularizerScale_pos (n := Fin d) hε) hx

end MatrixSpencer
