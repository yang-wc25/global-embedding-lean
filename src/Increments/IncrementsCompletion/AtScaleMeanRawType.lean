import IncrementsCompletion.AtScaleMeanPreparation
import Repair.FullIncrementNovOpenMeanRawSupply

/-! Actual raw profiles for an actual-scale preparation. The mathematical raw
record and original samples are unchanged. The preparation scale is kept
explicit and separate from the raw analysis scale in this internal type. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter Bundle
open scoped ContDiff ENNReal Topology BigOperators TensorProduct
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × Es
local notation "𝓙" => 𝓘(ℝ,Es)
variable {Β : Type*} [Fintype Β]

local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}

def IncrementsCompletionAtScaleMeanRawProfiles
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Β)
      (fun p x => Data.F (p,x)))
    (V0 : Set P) (cT : ℝ) (Tinv Forward Meta : ℕ → ℝ) (Rsub : ℕ) (preparedScale : ℝ)
    (prep : ∀ i, IncrementsCompletionAtScaleMeanPreparation Data hd hs hn g
      (V0 ×ˢ (univ : Set M)) cT Tinv Forward Meta Rsub preparedScale i)
    (G : Set (P × M)) (hG : IsOpen G)
    (input inputbar : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (n q j : ℕ) (reserve Bnd Mg : ℝ) (T : ℕ → ℝ) (tau ell Delta : ℝ) : Prop :=
  ∀ i : Fin Data.atlas.count × Fin Data.parameterCount,
    let z := prep i
    let eta := (round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart i.2)).eta
    let F := actualOriginalOpenParameterSlice Data i
    let hFn := actualOriginalOpenParameterSlice_contMDiff Data hd hs i
    let g0 := actualOriginalPrimaryFamily Data hd hs hn i z.host z.native z.slices z.data eta z.active
    let W := actualOriginalParameterNeighborhood Data i.2 G
    let hW := actualOriginalParameterNeighborhood_isOpen Data i.2 G hG
    Nonempty (ParameterRound2GlobalMeanRawProfiles (Tr := ℝ) n (q+2) j Rsub Data.primaryCount reserve Bnd Mg T
      F hFn (parameterRound2_restrictPrimaryFamily F g0 W hW)
      (actualOriginalParameterTensorSlice Data i input) (actualOriginalParameterTensorSlice Data i inputbar)
      W (fun nu => W ∩ (fun w : Ep × M => ((Data.parameterChart i.2).symm w.1,w.2)) ⁻¹' Data.primaryDomain nu)
      (Data.atlas.chart i.1) (actualRawObserverOpen (Data.atlas.chart i.1) W)
      ((parameterTensorModelEquiv (m+1) d) ⁻¹' incrementsOriginalEvaluation Data.atlas Data.parameterChart
        Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i) tau ell Delta)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.IncrementsCompletionAtScaleMeanRawProfiles
