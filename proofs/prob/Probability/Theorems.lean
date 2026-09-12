import Mathlib
import Probability.Axioms

open Set

namespace Probability

-- TODO: convert to structure
variable (Ω : Type _)
variable (A B : Set Ω)
variable (P : Set Ω → ℝ)

theorem nothingNeverHappens : P ∅ = 0 := by
  have h := additive Ω univ ∅ P
  specialize h (disjoint_empty univ)

  rw [union_empty univ, normalized Ω P] at h
  symm at h
  
  linarith

