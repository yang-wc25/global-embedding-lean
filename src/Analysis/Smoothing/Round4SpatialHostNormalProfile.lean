import Smoothing.Round3OuterHostCoverProfiles
import Smoothing.Round4SpatialRepairNormalCoverConsumer

/-! Actual same-SF normal rebound with every derivative profile and the
physical cover produced internally. Fixed reference charts and their stable
reserves are the only geometric input. Constants precede the current stage. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology ENNReal BigOperators
namespace GlobalEmbedding.Continuation
universe uA
variable {m d N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Y" => Fin (m+1+d) → ℝ
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
private local instance hostCoverFirstNormed : NormedAddCommGroup (D →L[ℝ] Ey) := inferInstance
private local instance hostCoverFirstSpace : NormedSpace ℝ (D →L[ℝ] Ey) := inferInstance
private local instance hostCoverFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] Ey) := inferInstance
private local instance hostCoverFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] Ey) := inferInstance

/-- The actual fixed-host normal profile after all observer and reference
field jets have been produced from the unchanged fixed packet. -/
def round4SpatialHostNormalProfile (m d N : ℕ) (radius : ℝ) (hradius : 0 < radius)
    (BS0 TS0 BP0 TP0 T Forward Given : ℕ → ℝ) (Ds Dp r : ℕ)
    (budget cF cT mu : ℝ) (hmu : 0 < mu) : ℕ → ℝ :=
  round4SpatialStageIntrinsicNormalProfile m d N radius hradius BS0 TS0 BP0 TP0
    T (round3HostObserverProfile m d Forward Given)
    (round3HostReferenceProfile m d N T Given) Ds Dp r budget cF cT mu hmu

theorem round4SpatialHostObserverProfile_congr_prefix (m d j : ℕ)
    {F₁ F₂ G₁ G₂ : ℕ → ℝ}
    (hF : ∀ a ≤ j+1, F₁ a = F₂ a) (hG : G₁ j = G₂ j) :
    round3HostObserverProfile m d F₁ G₁ j = round3HostObserverProfile m d F₂ G₂ j := by
  have hs : (∑ k ∈ Finset.range (j+2), F₁ k) = ∑ k ∈ Finset.range (j+2), F₂ k := by
    apply Finset.sum_congr rfl
    intro a ha
    exact hF a (by simp only [Finset.mem_range] at ha; omega)
  simp only [round3HostObserverProfile,hG,hs]

theorem round4SpatialHostReferenceProfile_congr_prefix (m d N j : ℕ)
    {T₁ T₂ G₁ G₂ : ℕ → ℝ}
    (hT : ∀ a ≤ j, T₁ a = T₂ a) (hG : G₁ j = G₂ j) :
    round3HostReferenceProfile m d N T₁ G₁ j = round3HostReferenceProfile m d N T₂ G₂ j := by
  unfold round3HostReferenceProfile
  rw [round4SpatialFastChartTransferPrefix_congr_prefix j hT,hG]

/-- The j-th actual host-normal bound reads raw/T geometry through j+2,
Forward through j+1, and the unchanged fixed-packet bound Given through j. -/
theorem round4SpatialHostNormalProfile_congr_prefix
    (m d N : ℕ) (radius : ℝ) (hradius : 0 < radius) (Ds Dp r j : ℕ)
    (budget cF cT mu : ℝ) (hmu : 0 < mu)
    {BS₁ BS₂ TS₁ TS₂ BP₁ BP₂ TP₁ TP₂ T₁ T₂ F₁ F₂ G₁ G₂ : ℕ → ℝ}
    (hBS : ∀ a ≤ j+2, BS₁ a = BS₂ a) (hTS : ∀ a ≤ j+2, TS₁ a = TS₂ a)
    (hBP : ∀ a ≤ j+2, BP₁ a = BP₂ a) (hTP : ∀ a ≤ j+2, TP₁ a = TP₂ a)
    (hT : ∀ a ≤ j+2, T₁ a = T₂ a)
    (hF : ∀ a ≤ j+1, F₁ a = F₂ a) (hG : ∀ a ≤ j, G₁ a = G₂ a) :
    round4SpatialHostNormalProfile m d N radius hradius BS₁ TS₁ BP₁ TP₁ T₁ F₁ G₁
      Ds Dp r budget cF cT mu hmu j =
    round4SpatialHostNormalProfile m d N radius hradius BS₂ TS₂ BP₂ TP₂ T₂ F₂ G₂
      Ds Dp r budget cF cT mu hmu j := by
  unfold round4SpatialHostNormalProfile
  apply round4SpatialStageIntrinsicNormalProfile_congr_prefix m d N radius hradius Ds Dp r j
    budget cF cT mu hmu hBS hTS hBP hTP hT
  · intro a ha
    exact round4SpatialHostObserverProfile_congr_prefix m d a
      (fun b hb => hF b (by omega)) (hG a ha)
  · intro a ha
    exact round4SpatialHostReferenceProfile_congr_prefix m d N a
      (fun b hb => hT b (by omega)) (hG a ha)

#print axioms round4SpatialHostNormalProfile_congr_prefix
end GlobalEmbedding.Continuation
