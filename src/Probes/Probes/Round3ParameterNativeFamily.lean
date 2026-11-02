import Probes.Round3ParameterIncrementNaturality

/-! Canonical native representatives of the single physical family.  These
abbreviations only pull back its primitive fields and actual charts.  Every
native output is derived from the original finite construction and is proved
to be the same physical increment on the parameter chart target. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {P M : Type*} [TopologicalSpace P]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  {Label SubPrimary SubSecondary : Type*} [Fintype Label] [DecidableEq Label]
  [Fintype SubPrimary] [Fintype SubSecondary]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

def round3ParameterNativePrimary
    (F : P → M → V)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Label) (Β := SubPrimary) F)
    (B : OpenPartialHomeomorph P Ep) :
    IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (Λ := Label) (Β := SubPrimary) (fun t => F (B.symm t)) :=
  (round3ParameterPrimaryPullback F g B).toNative (fun t => F (B.symm t))

def round3ParameterNativeChoices
    (choice : ActualSecondarySignedRecord Label → SubSecondary → Round3ParameterSecondaryChoice P M m)
    (B : OpenPartialHomeomorph P Ep) :
    ActualSecondarySignedRecord Label → SubSecondary → ActualOriginalSecondaryChoice Ep M m :=
  fun r a => ((choice r a).pullback B).toNative

variable (F : P → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ p, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F p))
  (g : Round3ParameterPrimaryFamily (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))))
    (m := m) (Λ := Label) (Β := SubPrimary) F)
  (B : OpenPartialHomeomorph P (EuclideanSpace ℝ (Fin d)))
  (hg : ∀ ν β, Round3ParameterChartPreserves (g.chart ν β))
  (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x))
  (length : ℕ) (tau delta : ℝ)
  (choice : ActualSecondarySignedRecord Label → SubSecondary → Round3ParameterSecondaryChoice P M m)
  (hc : ∀ r a, Round3ParameterChartPreserves (choice r a).chart)
include hg hc

theorem round3Parameter_native_increment_eq (t : Ep) (ht : t ∈ B.target) (x : M) :
    actualOriginalIncrementMap (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      (round3ParameterNativePrimary F g B) (fun t => input (B.symm t)) length tau delta
      (round3ParameterNativeChoices choice B) (t,x) =
    round3ParameterIncrementMap F hF g input length tau delta choice (B.symm t,x) :=
  round3ParameterIncrement_pullback F hF g B hg input length tau delta choice hc t ht x

/-- Equality of every total derivative, in the original parameter chart. -/
theorem round3Parameter_native_observed_iteratedFDeriv
    (e : OpenPartialHomeomorph M D) (k : ℕ) (z : Ep × D) (hz : z.1 ∈ B.target) :
    iteratedFDeriv ℝ k
      (fun w : Ep × D => actualOriginalIncrementMap (fun t => F (B.symm t)) (fun t => hF (B.symm t))
        (round3ParameterNativePrimary F g B) (fun t => input (B.symm t)) length tau delta
        (round3ParameterNativeChoices choice B) (w.1,e.symm w.2)) z =
    iteratedFDeriv ℝ k
      (fun w : Ep × D => round3ParameterIncrementMap F hF g input length tau delta choice
        (B.symm w.1,e.symm w.2)) z := by
  have he : (fun w : Ep × D => actualOriginalIncrementMap (fun t => F (B.symm t)) (fun t => hF (B.symm t))
        (round3ParameterNativePrimary F g B) (fun t => input (B.symm t)) length tau delta
        (round3ParameterNativeChoices choice B) (w.1,e.symm w.2)) =ᶠ[𝓝 z]
      (fun w : Ep × D => round3ParameterIncrementMap F hF g input length tau delta choice
        (B.symm w.1,e.symm w.2)) := by
    filter_upwards [(B.open_target.preimage continuous_fst).mem_nhds hz] with w hw
    exact round3Parameter_native_increment_eq F hF g B hg input length tau delta choice hc w.1 hw (e.symm w.2)
  exact (he.iteratedFDeriv ℝ k).eq_of_nhds

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_native_increment_eq
#print axioms GlobalEmbedding.Continuation.round3Parameter_native_observed_iteratedFDeriv
