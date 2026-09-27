import MatrixSpencer.KSSpinVertex

/-! The full Kadison–Singer signing conclusion from the spin-mixed proof. -/

namespace MatrixSpencer

theorem kadison_singer_spin_mixed : ksSpinMixedStatement := by
  apply KSFinalAssembly.statement_of_positive_dimension_vector_signings ksSpinMixedConstant_pos.le
  intro N d hd ε hε v hparseval hbound
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  apply KSFinalAssembly.spin_signing_of_maxFrozen_vertex v hparseval hε hbound
  intro x hx
  exact KSSpinVertex.maxFrozen_isVertex v (ksRegularizerScale_pos (n := Fin d) hε) hx

end MatrixSpencer
