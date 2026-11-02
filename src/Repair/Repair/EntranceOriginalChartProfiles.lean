import Repair.EntranceOriginalObserverJets
import Probes.Round3ParameterNativeRefinementSamples

/-!
# The original all-observer profiles use the selected numerical charts

The original full joint Forward/Inverse profiles are computed from the
selected native profiles, positive original transition budgets and fixed
coordinate bounds.  The qualitative cutoff certificate is retained only
for its cutoff field; its independently selected forward/inverse maxima
are discarded.  The named ordinary-cutoff producer can then replace that
cutoff certificate exactly as in the actual raw factory.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical BigOperators
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem repairEntrance_original_all_observer_profiles
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (hn : IncrementsOriginalFreeNormalConditions Ref hd hs)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
    (NF NI Parameter Spatial : ℕ → ℝ)
    (hNF : ∀ j, 0 ≤ NF j) (hNI : ∀ j, 0 ≤ NI j)
    (hParameter : ∀ j, 0 ≤ Parameter j) (hSpatial : ∀ j, 0 ≤ Spatial j)
    (transition : RepairOriginalTransitionBudgets Ref Parameter Spatial)
    (hForward : ∀ nu i a j z, z ∈ (packet.piece nu i a).native.source →
      ‖iteratedFDeriv ℝ j (packet.piece nu i a).native z‖ ≤ NF j)
    (hInverse : ∀ nu i a j z, z ∈ (packet.piece nu i a).native.target →
      ‖iteratedFDeriv ℝ j (packet.piece nu i a).native.symm z‖ ≤ NI j)
    (hSource : ∀ nu i a z, z ∈ (packet.piece nu i a).native.source →
      z.1 ∈ Ref.parameterNormDomain i.2 ∧ z.2 ∈ Ref.sourceNormDomain (packet.piece nu i a).host)
    (Bp Bs : ℝ)
    (hBp : ∀ ip p, p ∈ Ref.parameterNormDomain ip → ‖p‖ ≤ Bp)
    (hBs : ∀ is x, x ∈ Ref.sourceNormDomain is → ‖x‖ ≤ Bs)
    (ForwardOld InverseOld Meta : ℕ → ℝ)
    (hOld : Round3ParameterOriginalChartProfiles Ref
      (round3ParameterWholePrimaryFamily Ref hd hs hn theta packet) ForwardOld InverseOld Meta) :
    Round3ParameterOriginalChartProfiles Ref
      (round3ParameterWholePrimaryFamily Ref hd hs hn theta packet)
      (repairEntranceOriginalForwardProfile Bp NF Parameter Spatial)
      (repairEntranceOriginalInverseProfile Bp Bs NI Parameter Spatial) Meta := by
  intro ell hell hell1 nu beta i gN t etaN k z hz hPhysical
  have hOrig := hOld ell hell hell1 nu beta i k z hz hPhysical
  refine ⟨hOrig.1,hOrig.2.1,?_,?_,hOrig.2.2.2.2⟩
  all_goals
    have hJets : ‖iteratedFDeriv ℝ k t z‖ ≤ repairEntranceOriginalForwardProfile Bp NF Parameter Spatial k ∧
        ‖iteratedFDeriv ℝ k t.symm (t z)‖ ≤ repairEntranceOriginalInverseProfile Bp Bs NI Parameter Spatial k := by
      rcases beta with ⟨i0,mu,a⟩
      by_cases hmu : mu=nu
      · subst mu
        have hPiece : round3ParameterWholePrimaryPiece Ref hd theta packet nu ⟨i0,⟨nu,a⟩⟩ =
            packet.piece nu i0 a := by
          simp only [round3ParameterWholePrimaryPiece,round3PreparedPrimarySigmaPiece_active]
        have hChart : gN.chart nu ⟨i0,⟨nu,a⟩⟩ =
            actualHostAdaptedChart (Ref.atlas.chart (packet.piece nu i0 a).host)
              (round3ParameterCrossNativeChart (Ref.parameterChart i0.2) (Ref.parameterChart i.2)
                (packet.piece nu i0 a).native) := by
          change round3ParameterChartPullback (Ref.parameterChart i.2)
            (round3ParameterLiftedPrimaryChart Ref i0.2 nu _
              (round3ParameterWholePrimaryPiece Ref hd theta packet nu ⟨i0,⟨nu,a⟩⟩)) = _
          rw [hPiece]
          exact (round3Parameter_cross_host_conjugation (Ref.parameterChart i0.2) (Ref.parameterChart i.2)
            (Ref.atlas.chart (packet.piece nu i0 a).host) (packet.piece nu i0 a).native
            (round3Parameter_primary_native_preserves_phase Ref hd i0.2 nu _ (packet.piece nu i0 a)).1).symm
        have hSample := (actual_original_native_evaluation_iff Ref hd i z).mp hz
        have hActual := repairEntrance_original_piece_observer_jets Ref hd i0.2 nu _ (packet.piece nu i0 a)
          NF NI Parameter Spatial hNF hNI hParameter hSpatial transition
          (hForward nu i0 a) (hInverse nu i0 a) (hSource nu i0 a) Bp Bs i z
          hSample.2.1 hSample.1 (hBp i.2 z.1 hSample.2.1) (hBs i.1 z.2 hSample.1)
        have hsrc : z ∈ (((OpenPartialHomeomorph.refl Ep).prod (Ref.atlas.chart i.1)).symm.trans
            (actualHostAdaptedChart (Ref.atlas.chart (packet.piece nu i0 a).host)
              (round3ParameterCrossNativeChart (Ref.parameterChart i0.2) (Ref.parameterChart i.2)
                (packet.piece nu i0 a).native))).source := by
          rw [← hChart]
          exact hOrig.1
        have h := hActual hsrc k
        simpa only [← hChart] using h
      · have hZero : (round3ParameterWholePrimaryFamily Ref hd hs hn theta packet).eta nu ⟨i0,⟨mu,a⟩⟩ = 0 := by
          rw [round3ParameterWholePrimaryFamily_eta]
          simp only [round3ParameterWholePrimaryPiece,round3PreparedPrimarySigmaPiece,hmu,dite_false,
            round3ParameterLiftedPrimaryCutoff_empty]
        rw [hZero,tsupport_zero] at hPhysical
        exact False.elim hPhysical
  · exact ((mul_le_mul_of_nonneg_right (pow_le_one₀ hell hell1) (norm_nonneg _)).trans_eq
      (one_mul _)).trans hJets.1
  · exact ((mul_le_mul_of_nonneg_right (pow_le_one₀ hell hell1) (norm_nonneg _)).trans_eq
      (one_mul _)).trans hJets.2

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repairEntrance_original_all_observer_profiles
