import OriginalCollars.OriginalObserverCutoffProfiles

/-! Reference conditioning preserves the physical cutoff family exactly.
The explicit raw-parent/grid/transition budget therefore applies to the
conditioned mean packet, with no estimate of its actual derivatives added
as a new hypothesis. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation.OriginalCollars
open OriginalIncrements

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem conditioned_original_observer_cutoff_budget
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (BS TS BP TP : ℕ → ℝ)
    (hBS : ∀ k, 0 ≤ BS k) (hTS : ∀ k, 0 ≤ TS k)
    (hBP : ∀ k, 0 ≤ BP k) (hTP : ∀ k, 0 ≤ TP k) (Ds Dp : ℕ)
    (B : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep)
    (hChart : B.chart = Data.parameterChart)
    (RS : TensorRawCutoffPreparation Data.atlas BS TS Ds)
    (RP : TensorLocalRawPreparation B Data.parameterSet BP TP Dp)
    (psi : P → ℝ) (V : Set P) (hV : IsOpen V) (hKV : Data.parameterSet ⊆ V)
    (hOne : EqOn psi 1 V)
    (Parameter Spatial : ℕ → ℝ)
    (hParameter : ∀ k, 0 ≤ Parameter k) (hSpatial : ∀ k, 0 ≤ Spatial k)
    (transition : RepairOriginalTransitionBudgets Data Parameter Spatial) :
    let theta := fun i => sourceCollarNovParameterLocalized psi
      (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
        (tensorLocalNormalizedCutoff RP.raw) i)
    ∀ (supply : OriginalBudgetedPrimarySupply Data theta)
      (_hCompact : ∀ i, IsCompact (tsupport (theta i)))
      (_hSmooth : ∀ i, ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (theta i))
      (profiles : Round3ParameterWholeReferenceProfiles Data hd hs theta supply.packet),
    let conditioned := supply.packet.replacePieces Data theta profiles.piece profiles.host profiles.cutoff
    let g := round3ParameterWholePrimaryFamily Data hd hs hn theta conditioned
    ∀ ell, 0 ≤ ell → ell ≤ 1 → ∀ nu beta observer j z,
      parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalEvaluation Data.atlas Data.parameterChart
        Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet observer →
      ell^j * ‖iteratedFDeriv ℝ j (fun y : X => g.eta nu beta
        ((Data.parameterChart observer.2).symm y.1,(Data.atlas.chart observer.1).symm y.2)) z‖ ≤
        originalObserverCutoffProfile Data theta supply BS TS BP TP Parameter Spatial Ds Dp j := by
  intro theta supply hCompact hSmooth profiles conditioned g ell hell hell1 nu beta observer j z hz
  have hEta := round3Parameter_replacement_same_global_eta Data hd hs hn theta supply.packet
    profiles.piece profiles.host profiles.cutoff
  change ell^j * ‖iteratedFDeriv ℝ j (fun y : X =>
    (round3ParameterWholePrimaryFamily Data hd hs hn theta
      (supply.packet.replacePieces Data theta profiles.piece profiles.host profiles.cutoff)).eta nu beta
      ((Data.parameterChart observer.2).symm y.1,(Data.atlas.chart observer.1).symm y.2)) z‖ ≤ _
  rw [hEta]
  exact original_primary_observer_cutoff_budget Data hd hs hn BS TS BP TP hBS hTS hBP hTP Ds Dp
    B hChart RS RP psi V hV hKV hOne Parameter Spatial hParameter hSpatial transition
    supply hCompact hSmooth ell hell hell1 nu beta observer j z hz

end GlobalEmbedding.Continuation.OriginalCollars
#print axioms GlobalEmbedding.Continuation.OriginalCollars.conditioned_original_observer_cutoff_budget
