import IncrementsCompletion.AtScaleMeanPreparation
import Repair.FullIncrementNovOpenMeanCoordinates

/-! Actual physical/native mean identities use only the unchanged original
computational fields. The preparation scale is irrelevant to these identities;
no refinement certificate at any other scale is requested. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
variable {Sub : Type*} [Fintype Sub]

theorem incrementsCompletion_at_scale_native_mean_eq
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Sub)
      (fun p x => Data.F (p,x)))
    (hActive : ∀ nu beta z, z ∈ (g.chart nu beta).source →
      ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => Data.F (z.1,x)))
    (hPreserves : ∀ nu beta, Round3ParameterChartPreserves (g.chart nu beta))
    (G0 : Set (P × M)) (cT : ℝ) (Tinv Forward Meta : ℕ → ℝ) (Rsub : ℕ)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (preparedScale : ℝ)
    (prep : IncrementsCompletionAtScaleMeanPreparation Data hd hs hn g G0 cT Tinv Forward Meta Rsub preparedScale i)
    (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (length : ℕ) (tau : ℝ) (t : Ep) (ht : t ∈ (Data.parameterChart i.2).target)
    (hp : (Data.parameterChart i.2).symm t ∈ Data.parameterOpen) (x : M) :
    let eta := (round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart i.2)).eta
    let actual := actualOriginalPrimaryFamily Data hd hs hn i prep.host prep.native prep.slices prep.data eta prep.active
    incrementsGlobalPrimaryMean (actualOriginalOpenParameterSlice Data i)
      (actualOriginalOpenParameterSlice_contMDiff Data hd hs i) actual
      (actualOriginalParameterTensorSlice Data i input) length tau t x =
      fullIncrementNovPrimaryMean (fun p x => Data.F (p,x)) g input hActive length tau
        ((Data.parameterChart i.2).symm t) x := by
  intro eta actual
  obtain ⟨hPhase,hCut,hNormal,hLinear,hEta,hChart,hInverse⟩ := prep.same_fields
  exact fullIncrementNov_open_native_mean_eq (fun p x => Data.F (p,x))
    (actualOriginalOpenParameterSlice Data i) (actualOriginalOpenParameterSlice_contMDiff Data hd hs i)
    g actual hActive (Data.parameterChart i.2) hPreserves input
    (actualOriginalParameterTensorSlice Data i input) length tau t ht
    (actualOriginalOpenParameterSlice_eq Data i t hp).symm rfl
    (fun nu x => (congrArg (fun f => f nu (t,x)) hCut).symm)
    (fun nu x => (congrArg (fun f => f nu (t,x)) hNormal).symm)
    (fun nu x => (congrArg (fun f => f nu t x) hLinear).symm)
    (fun nu beta x => (congrArg (fun f => f nu beta (t,x)) hEta).symm)
    (fun nu beta => congrArg (fun f => f nu beta) hChart)
    (fun nu beta => (congrArg (fun f => f nu beta t) hInverse).symm)
    (fun nu x => (congrArg (fun f => f nu (t,x)) hPhase).symm) x

theorem incrementsCompletion_at_scale_restricted_meanError_eq
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Sub)
      (fun p x => Data.F (p,x)))
    (hActive : ∀ nu beta z, z ∈ (g.chart nu beta).source →
      ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => Data.F (z.1,x)))
    (hPreserves : ∀ nu beta, Round3ParameterChartPreserves (g.chart nu beta))
    (G0 : Set (P × M)) (cT : ℝ) (Tinv Forward Meta : ℕ → ℝ) (Rsub : ℕ)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (preparedScale : ℝ)
    (prep : IncrementsCompletionAtScaleMeanPreparation Data hd hs hn g G0 cT Tinv Forward Meta Rsub preparedScale i)
    (G : Set (P × M)) (hG : IsOpen G) (hGR : G ⊆ incrementsOriginalParameterRegion Data)
    (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (length : ℕ) (tau : ℝ) (z : Ep × M)
    (hz : z ∈ actualOriginalParameterNeighborhood Data i.2 G) :
    let eta := (round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart i.2)).eta
    let actual := actualOriginalPrimaryFamily Data hd hs hn i prep.host prep.native prep.slices prep.data eta prep.active
    let F := actualOriginalOpenParameterSlice Data i
    let hF := actualOriginalOpenParameterSlice_contMDiff Data hd hs i
    let W := actualOriginalParameterNeighborhood Data i.2 G
    let hW := actualOriginalParameterNeighborhood_isOpen Data i.2 G hG
    incrementsGlobalPrimaryMeanError F hF (parameterRound2_restrictPrimaryFamily F actual W hW)
      (actualOriginalParameterTensorSlice Data i input) length tau z.1 z.2 =
      fullIncrementNovPrimaryMeanError (fun p x => Data.F (p,x)) g input hActive length tau
        ((Data.parameterChart i.2).symm z.1) z.2 := by
  intro eta actual F hF W hW
  rw [parameterRound2_restrictPrimary_meanError F hF actual W hW _ length tau z hz]
  exact congrArg (fun T => T-input ((Data.parameterChart i.2).symm z.1) z.2)
    (incrementsCompletion_at_scale_native_mean_eq Data hd hs hn g hActive hPreserves G0 cT
      Tinv Forward Meta Rsub i preparedScale prep input length tau z.1 hz.1.1 (hGR hz.2).1 z.2)

theorem incrementsCompletion_at_scale_original_meanError_coordinates
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Sub)
      (fun p x => Data.F (p,x)))
    (hActive : ∀ nu beta z, z ∈ (g.chart nu beta).source →
      ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => Data.F (z.1,x)))
    (hPreserves : ∀ nu beta, Round3ParameterChartPreserves (g.chart nu beta))
    (G0 : Set (P × M)) (cT : ℝ) (Tinv Forward Meta : ℕ → ℝ) (Rsub : ℕ)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (preparedScale : ℝ)
    (prep : IncrementsCompletionAtScaleMeanPreparation Data hd hs hn g G0 cT Tinv Forward Meta Rsub preparedScale i)
    (G : Set (P × M)) (hG : IsOpen G) (hGR : G ⊆ incrementsOriginalParameterRegion Data)
    (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (q : ℕ) (hq : 1 ≤ q) (tau : ℝ) (htau : 0 < tau) :
    let eta := (round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart i.2)).eta
    let actual := actualOriginalPrimaryFamily Data hd hs hn i prep.host prep.native prep.slices prep.data eta prep.active
    let F := actualOriginalOpenParameterSlice Data i
    let hF := actualOriginalOpenParameterSlice_contMDiff Data hd hs i
    let W := actualOriginalParameterNeighborhood Data i.2 G
    let hW := actualOriginalParameterNeighborhood_isOpen Data i.2 G hG
    let gn := parameterRound2_restrictPrimaryFamily F actual W hW
    let primary := fun nu => W ∩ (fun w : Ep × M => ((Data.parameterChart i.2).symm w.1,w.2)) ⁻¹' Data.primaryDomain nu
    ParameterRound2GlobalMeanPrimitives F hF gn (actualOriginalParameterTensorSlice Data i input) W primary →
    ∀ (y : Fin (m+1+d) → ℝ), y ∈ incrementsOriginalDifferentiation Data.atlas Data.parameterChart i →
      (incrementsOriginalParameterPoint y,(Data.atlas.chart i.1).symm (incrementsOriginalSourcePoint y)) ∈ W →
      incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart
        (fullIncrementNovPrimaryMeanError (fun p x => Data.F (p,x)) g input hActive (q+2) tau) i y =
        fun k => (parameterRound2_globalObservedMeanCoefficient F hF gn
          (actualOriginalParameterTensorSlice Data i input) (q+2) tau (Data.atlas.chart i.1)
          (incrementsOriginalParameterPoint y,incrementsOriginalSourcePoint y)
          (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2).re := by
  intro eta actual F hF W hW gn primary prim y hy hWy
  funext k
  have hm := incrementsCompletion_at_scale_restricted_meanError_eq Data hd hs hn g hActive hPreserves
    G0 cT Tinv Forward Meta Rsub i preparedScale prep G hG hGR input (q+2) tau
    (incrementsOriginalParameterPoint y,(Data.atlas.chart i.1).symm (incrementsOriginalSourcePoint y)) hWy
  change fullIncrementNovPrimaryMeanError (fun p x => Data.F (p,x)) g input hActive (q+2) tau
    ((Data.parameterChart i.2).symm (incrementsOriginalParameterPoint y))
    ((Data.atlas.chart i.1).symm (incrementsOriginalSourcePoint y)) _ _ = _
  rw [← hm]
  exact parameterRound2_meanPrimitives_coordinate F hF gn (actualOriginalParameterTensorSlice Data i input)
    W primary prim q hq tau htau (Data.atlas.chart i.1)
    (contMDiffOn_of_mem_maximalAtlas (hd.atlas_smooth.chart_mem i.1))
    (contMDiffOn_symm_of_mem_maximalAtlas (hd.atlas_smooth.chart_mem i.1))
    (incrementsOriginalParameterPoint y,incrementsOriginalSourcePoint y) hy.1 hWy
    (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_at_scale_native_mean_eq
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_at_scale_restricted_meanError_eq
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_at_scale_original_meanError_coordinates
