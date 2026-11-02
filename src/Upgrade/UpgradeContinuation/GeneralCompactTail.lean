import UpgradeContinuation.GeneralCompactInitialization
import UpgradeContinuation.GeneralSelectedTail

/-!
# Original F and legal waves produce the actual same-family repair runs

Every source and parameter choice is internal, including the fixed
reference supply, compact sphere model, initialized atlas and base chart.
The output retains the original selected family and its first-map formula,
all primitive profiles, the closed initial state, and the actual same-state
infinite run.  Its numerical repair plan is fixed before the probe scale.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold IsManifold Bundle GlobalEmbedding.Paper GlobalEmbedding.Offline
open GlobalEmbedding.Upgrade GlobalEmbedding.NormalPolar
open scoped ContDiff Topology ENNReal Classical

namespace GlobalEmbedding.Continuation.UpgradeContinuation

variable {m N r : ℕ} {M : Type*}
  [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

/-- A fully constructed original-input supply for the remaining native
response assembly.  The selected first-map data are visible in the final
`GeneralSelectedTailStatement`, rather than hidden inside a realization. -/
def GeneralCompactTailSupply
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (waves : Fin r → OpenSupportedLegalWave F hF) : Prop :=
  let d := Fintype.card (Fin r × Bool)
  let P := ActualRepairCompactParameter d
  let p₀ := actualRepairCompactParameterBase d
  letI := referenceRiemannianBundle (n := m+1) (M := M)
  ∃ s : OriginalReferenceSupply (m := m) F,
    ∃ B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)),
    ∃ hB : IsSmoothBufferedAtlas B,
    ∃ hforward : ∀ i, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin d))
      𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ (B.chart i),
    ∃ Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d)),
    ∃ hQ : ∀ i, IsCompact (Q i) ∧ Q i ⊆ (B.chart i).target ∧
      closure (bufferedSamplingCoordinates B i) ⊆ Q i,
    ∃ BP TP : ℕ → ℝ, (∀ k, 0 ≤ BP k) ∧ (∀ k, 0 ≤ TP k) ∧
    ∃ b : Fin B.count, actualRepairCompactParameterBase d ∈ B.inner b ∧
      GeneralSelectedTailStatement F hF waves s B Q BP TP b p₀

/-- The original qualitative hypotheses manufacture same-family initial
states and complete repair runs at every sufficiently small positive t. -/
theorem generalMap_exists_compact_tail_supply [Nonempty M]
    (hdim : 2 ≤ m+1) (hambient : (m+1)*(m+2)/2 < N)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (hphase : PhaseRegular F hF)
    (waves : Fin r → OpenSupportedLegalWave F hF) :
    GeneralCompactTailSupply (m := m) F hF waves := by
  letI := referenceRiemannianBundle (n := m+1) (M := M)
  obtain ⟨s,B,hB,hforward,Q,hQ,BP,TP,hBP,hTP,b,hb,hSelected⟩ :=
    generalMap_exists_compact_initialized_secondary hdim hambient F hF himm hphase waves
  refine ⟨s,B,hB,hforward,Q,hQ,BP,TP,hBP,hTP,b,hb,?_⟩
  exact generalReference_selected_initial_tail F hF waves s B hB hforward Q
    (fun i => (hQ i).1) (fun i => (hQ i).2.1) BP TP hBP hTP b _ hb hSelected

end GlobalEmbedding.Continuation.UpgradeContinuation

#print axioms GlobalEmbedding.Continuation.UpgradeContinuation.GeneralCompactTailSupply
#print axioms GlobalEmbedding.Continuation.UpgradeContinuation.generalMap_exists_compact_tail_supply
