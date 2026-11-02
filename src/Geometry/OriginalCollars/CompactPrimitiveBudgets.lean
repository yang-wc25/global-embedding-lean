import Probes.Round3PhaseCompactPreparation
import Probes.Round3PreparedCompactProfiles

/-!
# Actual primitive open budgets from compact smooth input

One open neighborhood is selected before every derivative order and scale.
The returned profile bounds the actual phase, and the finite native budget
bounds the actual joint map through order two. These are fixed-data
existence statements; they do not turn compactness into a uniform estimate
across unrelated data. The receiving numerical class can subsequently fix
the resulting genuine primitive numbers.
-/

noncomputable section
open Set Function Metric
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {Ep Es Y : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Es] [NormedSpace ℝ Es]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [ProperSpace (Ep × Es)]

/-- All derivative bounds refer to the actual functions on the same true
open neighborhood. No adapted chart, inverse, solver or output is supplied. -/
theorem compact_phase_native_two_jet_budgets
    (phase : Ep × Es → ℝ) (nativeMap : Ep × Es → Y)
    (K U : Set (Ep × Es)) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hPhase : ContDiffOn ℝ ∞ phase U) (hMap : ContDiffOn ℝ ∞ nativeMap U)
    (hNoncritical : ∀ x ∈ K,
      (fderiv ℝ phase x).comp (ContinuousLinearMap.inr ℝ Ep Es) ≠ 0) :
    ∃ (mu Mb R buffer coordinateBound nativeTwo : ℝ)
      (O : Set (Ep × Es)) (Phase : ℕ → ℝ),
      0 < mu ∧ 0 < Mb ∧ 0 < R ∧ 0 < buffer ∧ 0 < coordinateBound ∧ 0 ≤ nativeTwo ∧
      IsOpen O ∧ K ⊆ O ∧ O ⊆ U ∧
      K ⊆ closedBall 0 R ∧ (∀ x ∈ K, ball x buffer ⊆ O) ∧
      (∀ x ∈ O, ‖x‖ ≤ coordinateBound) ∧
      (∀ j, 0 ≤ Phase j) ∧ Phase 1 ≤ Mb ∧ buffer*Phase 2 ≤ Mb ∧
      ContDiffOn ℝ ∞ phase O ∧
      (∀ x ∈ K, mu ≤ ‖(fderiv ℝ phase x).comp (ContinuousLinearMap.inr ℝ Ep Es)‖) ∧
      (∀ j x, x ∈ O → ‖iteratedFDeriv ℝ j phase x‖ ≤ Phase j) ∧
      (∀ j, j ≤ 2 → ∀ x ∈ O, ‖iteratedFDeriv ℝ j nativeMap x‖ ≤ nativeTwo) := by
  have hFirst : ContinuousOn (fderiv ℝ phase) U :=
    hPhase.continuousOn_fderiv_of_isOpen hU (by simp)
  have hSpatial : ContinuousOn
      (fun x => ‖(fderiv ℝ phase x).comp (ContinuousLinearMap.inr ℝ Ep Es)‖) K :=
    ((hFirst.clm_comp continuousOn_const).norm).mono hKU
  obtain ⟨mu,hmu,hMu⟩ := hK.exists_forall_le' hSpatial
    (fun x hx => norm_pos_iff.mpr (hNoncritical x hx))
  obtain ⟨buffer,hBuffer,hClosedU⟩ := hK.exists_cthickening_subset_open hU hKU
  let O := thickening buffer K
  have hOC : O ⊆ cthickening buffer K := thickening_subset_cthickening buffer K
  have hOU : O ⊆ U := hOC.trans hClosedU
  have hCompact : IsCompact (cthickening buffer K) := hK.cthickening
  obtain ⟨Phase,hPhaseNN,hPhaseBound⟩ := round3_prepared_compact_profiles
    phase U (cthickening buffer K) hU hCompact hClosedU hPhase
  obtain ⟨MapJets,hMapNN,hMapBound⟩ := round3_prepared_compact_profiles
    nativeMap U (cthickening buffer K) hU hCompact hClosedU hMap
  let Mb := 1+max (Phase 1) (buffer*Phase 2)
  let nativeTwo := max (MapJets 0) (max (MapJets 1) (MapJets 2))
  have hMb : 0 < Mb := by
    have h := (hPhaseNN 1).trans (le_max_left (Phase 1) (buffer*Phase 2))
    dsimp only [Mb]
    linarith
  have hTwo : 0 ≤ nativeTwo := (hMapNN 0).trans (le_max_left _ _)
  have hPhaseOne : Phase 1 ≤ Mb := by
    have h := le_max_left (Phase 1) (buffer*Phase 2)
    dsimp only [Mb]
    linarith
  have hPhaseTwo : buffer*Phase 2 ≤ Mb := by
    have h := le_max_right (Phase 1) (buffer*Phase 2)
    dsimp only [Mb]
    linarith
  obtain ⟨R,hR,hRadius⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨coordinateBound,hCoordinate,hCoordinates⟩ := hCompact.isBounded.exists_pos_norm_le
  refine ⟨mu,Mb,R,buffer,coordinateBound,nativeTwo,O,Phase,
    hmu,hMb,hR,hBuffer,hCoordinate,hTwo,isOpen_thickening,
    self_subset_thickening hBuffer K,hOU,?_,?_,?_,hPhaseNN,hPhaseOne,hPhaseTwo,
    hPhase.mono hOU,hMu,?_,?_⟩
  · intro x hx
    simpa only [mem_closedBall,dist_zero_right] using hRadius x hx
  · intro x hx
    exact ball_subset_thickening hx buffer
  · intro x hx
    exact hCoordinates x (hOC hx)
  · intro j x hx
    simpa only [one_pow,one_mul] using (hPhaseBound 1 zero_le_one le_rfl j x (hOC hx)).1
  · intro j hj x hx
    have hBase : ‖iteratedFDeriv ℝ j nativeMap x‖ ≤ MapJets j := by
      simpa only [one_pow,one_mul] using (hMapBound 1 zero_le_one le_rfl j x (hOC hx)).1
    apply hBase.trans
    have cases : j=0 ∨ j=1 ∨ j=2 := by omega
    rcases cases with rfl | rfl | rfl
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.compact_phase_native_two_jet_budgets
