import ExistenceMS.Square
import ExistenceMS.Rectangle

/-! Matrix-only existence for both regimes through the revised projection
walk. N is the number of matrices, d their common dimension. -/
namespace ExistenceMS

theorem exists_combined : Frozen.combinedTarget :=
  ⟨exists_square, exists_rectangular⟩

end ExistenceMS
