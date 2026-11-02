import NormalPolar.ActualProbeInitialSupplyGroupedSource

/-!
# The same complete first increment in the original map norms

One actual joint raw atlas produces both the primary and every signed
secondary wave. Their literal sum is bound to the original physical source
before differentiation. The original C2 and weighted base-two norm follow
from its true joint jets; no norm bound or closed state is an input.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation
variable {M P Tr Λ Β Sub : Type*} {m d N p r count : ℕ}
  [TopologicalSpace P] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype Sub]
  {Pieces : Fin r → Type*} [∀ l, Fintype (Pieces l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)
local notation "Rec" => ActualSecondarySignedRecord (Λ ⊕ Fin r)

def actualProbeInitialGroupedSource
    (F : P → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Λ) (Β := Β) F)
    (label : (Fin r × Bool) ↪ Fin p) (c : (l : Fin r) → Pieces l → P → D → M)
    (vf : (l : Fin r) → (s : Pieces l) → (b : P) → (x : D) → normalSpace (I := IM) (F b) (c l s b x))
    (phase : Fin r → P × M → ℝ) (tau delta : ℝ) (backgroundLength probeLength : ℕ)
    (a : (l : Fin r) → Pieces l → OpenPartialHomeomorph (P × M) (P × D))
    (input : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
    (u : P → Fin p → ℝ) (choice : Rec → Sub → Round3ParameterSecondaryChoice P M m)
    (hc : ∀ rec b, Round3ParameterChartPreserves (choice rec b).chart) :
    Rec → Sub → ActualProbeSecondaryParameterSource P M m :=
  fun rec b => actualParameterSecondarySourceOfPrimary (Sum.elim g.phase phase)
    (actualProbeInitialGroupedAmplitude F hF g label c vf tau delta backgroundLength
      probeLength a input u false)
    (actualProbeInitialGroupedAmplitude F hF g label c vf tau delta backgroundLength
      probeLength a input u true) tau rec.val (choice rec b) (hc rec b)

def actualProbeInitialGroupedIncrement
    (F : P → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Λ) (Β := Β) F)
    (label : (Fin r × Bool) ↪ Fin p) (c : (l : Fin r) → Pieces l → P → D → M)
    (vf : (l : Fin r) → (s : Pieces l) → (b : P) → (x : D) → normalSpace (I := IM) (F b) (c l s b x))
    (phase : Fin r → P × M → ℝ) (tau delta : ℝ) (backgroundLength probeLength length : ℕ)
    (a : (l : Fin r) → Pieces l → OpenPartialHomeomorph (P × M) (P × D))
    (input : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
    (u : P → Fin p → ℝ) (choice : Rec → Sub → Round3ParameterSecondaryChoice P M m)
    (hc : ∀ rec b, Round3ParameterChartPreserves (choice rec b).chart) : P × M → V :=
  fun z => actualProbeInitialGroupedPrimary F hF g label c vf phase tau delta backgroundLength
    probeLength a input u z + actualParameterSecondarySourceSum F hF
      (actualProbeInitialGroupedSource F hF g label c vf phase tau delta backgroundLength probeLength
        a input u choice hc) tau length z

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualProbeInitialGroupedSource
#print axioms GlobalEmbedding.Continuation.actualProbeInitialGroupedIncrement
