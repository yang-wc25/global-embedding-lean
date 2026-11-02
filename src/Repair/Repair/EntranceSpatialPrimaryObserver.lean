import Repair.EntranceSpatialPrimaryBudget
import Repair.EntranceObserverBudget
import Repair.EntranceOriginalCutoffToMeta

/-! The same original primary factory supplies the actual observer budget.
The true native sample membership is inherited from the original U domains;
the observer costs are the fixed numerical transition formulas. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology ENNReal Classical
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
    {theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ}
    {plateau : Fin Data.primaryCount → P × M → ℝ}
    {mu bound : ℝ}

def RepairReferenceSpatialPrimarySupply.observer_budget
    {owner : Fin Data.primaryCount → OpenPartialHomeomorph M D}
    {xi : Fin Data.primaryCount → D →L[ℝ] ℝ}
    {U : (Fin Data.atlas.count × Fin Data.parameterCount) → Set X}
    (s : RepairReferenceSpatialPrimarySupply Data theta owner xi plateau U mu bound)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (profiles : Round3ParameterWholeReferenceProfiles Data hd hs theta s.packet)
    (hPiece : profiles.piece=s.packet.piece)
    (Parameter Spatial : ℕ → ℝ) (hParameter : ∀ j, 0 ≤ Parameter j) (hSpatial : ∀ j, 0 ≤ Spatial j)
    (transition : RepairOriginalTransitionBudgets Data Parameter Spatial)
    (Bp Bs : ℝ) (hBp : 0 ≤ Bp) (hBs : 0 ≤ Bs)
    (hParameterValue : ∀ ip p, p ∈ Data.parameterNormDomain ip → ‖p‖ ≤ Bp)
    (hSourceValue : ∀ i x, x ∈ Data.sourceNormDomain i → ‖x‖ ≤ Bs)
    (hSamples : ∀ i z, z ∈ U i → parameterTensorModelEquiv (m+1) d z ∈
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet i) :
    RepairPrimaryObserverBudget Data hd hs theta s.packet profiles where
  parameter := Parameter
  spatial := Spatial
  parameter_nonneg := hParameter
  spatial_nonneg := hSpatial
  transition := transition
  parameterValue := Bp
  sourceValue := Bs
  parameterValue_nonneg := hBp
  sourceValue_nonneg := hBs
  parameter_value := hParameterValue
  source_value := hSourceValue
  native_source := by
    intro nu i a z hz
    rw [hPiece] at hz ⊢
    rw [s.packet.host]
    have h := (actual_original_native_evaluation_iff Data hd i z).mp
      (hSamples i z ((s.source nu i a z).mp hz).1)
    exact ⟨h.2.1,h.1⟩

theorem RepairReferenceSpatialPrimarySupply.global_cutoff
    {owner : Fin Data.primaryCount → OpenPartialHomeomorph M D}
    {xi : Fin Data.primaryCount → D →L[ℝ] ℝ}
    {U : (Fin Data.atlas.count × Fin Data.parameterCount) → Set X}
    (s : RepairReferenceSpatialPrimarySupply Data theta owner xi plateau U mu bound)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (nu : Fin Data.primaryCount) (beta : Round3ParameterWholePrimaryIndex Data theta s.packet) :
    (round3ParameterWholePrimaryFamily Data hd hs hn theta s.packet).eta nu beta =
      if beta.2.1=nu then (fun z => theta beta.1 z*plateau nu z) else 0 := by
  rcases beta with ⟨i,nu',a⟩
  by_cases h : nu'=nu
  · subst nu'
    rw [round3ParameterWholePrimaryFamily_eta]
    simp only [round3ParameterWholePrimaryPiece,round3PreparedPrimarySigmaPiece_active,ite_true]
    exact s.cutoff nu i a
  · rw [round3ParameterWholePrimaryFamily_eta]
    simp only [round3ParameterWholePrimaryPiece,round3PreparedPrimarySigmaPiece,h,dite_false,
      round3ParameterLiftedPrimaryCutoff_empty,ite_false]

/-- The original same-factory cutoff jets enter the actual adapted Meta
profile. Any old compact profile is used only for domain membership;
the returned Meta is exactly the displayed numerical composition. -/
theorem RepairReferenceSpatialPrimarySupply.numerical_meta
    {owner : Fin Data.primaryCount → OpenPartialHomeomorph M D}
    {xi : Fin Data.primaryCount → D →L[ℝ] ℝ}
    {U : (Fin Data.atlas.count × Fin Data.parameterCount) → Set X}
    (s : RepairReferenceSpatialPrimarySupply Data theta owner xi plateau U mu bound)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (profiles : Round3ParameterWholeReferenceProfiles Data hd hs theta s.packet)
    (observer : RepairPrimaryObserverBudget Data hd hs theta s.packet profiles)
    (hCompact : ∀ i, IsCompact (incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i))
    (Cutoff : ℕ → ℝ) (hCutoff : ∀ j, 0 ≤ Cutoff j)
    (hOriginal : ∀ nu parent i j z, parameterTensorModelEquiv (m+1) d z ∈
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet i →
      ‖iteratedFDeriv ℝ j (fun w : X =>
        theta parent ((Data.parameterChart i.2).symm w.1,(Data.atlas.chart i.1).symm w.2)*
        plateau nu ((Data.parameterChart i.2).symm w.1,(Data.atlas.chart i.1).symm w.2)) z‖ ≤ Cutoff j) :
    RepairOriginalPrimaryCutoffJets Data
      (round3ParameterWholePrimaryFamily Data hd hs hn theta
        (round3OuterReferencePrimaryPacket Data hd hs theta s.packet profiles))
      (repairEntranceCompositionProfile Cutoff observer.inverseProfile) := by
  let packet := round3OuterReferencePrimaryPacket Data hd hs theta s.packet profiles
  let g := round3ParameterWholePrimaryFamily Data hd hs hn theta packet
  obtain ⟨Forward,Inverse,Meta,hForward,hInverse,hMeta,hOld⟩ :=
    round3Parameter_actual_whole_primary_chart_profiles Data hd hs hn theta packet
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet) hCompact (fun _ _ hz => hz.1)
  have hOld' : Round3ParameterOriginalChartProfiles Data g Forward Inverse Meta := by
    intro ell hell hell1 nu beta i gN t etaN k z hz hPhysical
    exact hOld ell hell hell1 nu beta i k z hz hPhysical
  have hNumerical := observer.original_profiles hn Forward Inverse Meta hOld'
  apply repairEntrance_actual_primary_cutoff_from_original_jets Data hd hs hn theta packet
    Cutoff observer.forwardProfile observer.inverseProfile Meta hCutoff observer.inverse_nonneg hNumerical
  intro nu beta i j z hz hPhysical
  have hEta := round3Parameter_replacement_same_global_eta Data hd hs hn theta s.packet
    profiles.piece profiles.host profiles.cutoff
  have hGlobal : g.eta nu beta =
      if beta.2.1=nu then (fun z => theta beta.1 z*plateau nu z) else 0 := by
    rw [show g.eta=(round3ParameterWholePrimaryFamily Data hd hs hn theta s.packet).eta from hEta]
    exact s.global_cutoff hd hs hn nu beta
  by_cases h : beta.2.1=nu
  · simp only [h,ite_true] at hGlobal
    have hFun : (fun w : X => (round3ParameterWholePrimaryFamily Data hd hs hn theta packet).eta nu beta
        ((Data.parameterChart i.2).symm w.1,(Data.atlas.chart i.1).symm w.2)) =
        (fun w : X => theta beta.1 ((Data.parameterChart i.2).symm w.1,(Data.atlas.chart i.1).symm w.2)*
          plateau nu ((Data.parameterChart i.2).symm w.1,(Data.atlas.chart i.1).symm w.2)) := by
      funext w
      exact congrFun hGlobal _
    rw [hFun]
    exact hOriginal nu beta.1 i j z hz
  · rw [ite_eq_right h] at hGlobal
    change _ ∈ tsupport (g.eta nu beta) at hPhysical
    rw [hGlobal,tsupport_zero] at hPhysical
    exact hPhysical.elim

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.RepairReferenceSpatialPrimarySupply.observer_budget
#print axioms GlobalEmbedding.Continuation.RepairReferenceSpatialPrimarySupply.global_cutoff
#print axioms GlobalEmbedding.Continuation.RepairReferenceSpatialPrimarySupply.numerical_meta
