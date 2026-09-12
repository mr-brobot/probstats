import Mathlib

open Set

namespace Probability

-- sample space
variable (Ω : Type _)

-- events
variable (A B : Set Ω)

-- probability measure maps events to real numbers
variable (P : Set Ω → ℝ)

-- probability measure of any event is non-negative
axiom nonnegative : ∀ A, P A ≥ 0

-- probability measure of any outcome is assured
axiom normalized : P univ = 1

-- probability measure of the union of disjoint events is equal to the sum of individual probabilities
axiom additive (h : Disjoint A B) : P (A ∪ B) = P A + P B

