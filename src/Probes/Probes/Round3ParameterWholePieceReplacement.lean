import Probes.Round3ParameterWholeReferenceStableFamily

/-! Retain the literal global cutoff partition when actual reference targets
are conditioned or changed to genuine stable targets.  This rebuilds the
whole all-chart supply with exactly the same finite index and physical eta,
including ordinary germs, compact supports and dimensional overlap bounds. -/

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
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3Parameter_lifted_cutoff_eq_of_native_eq
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (ip : Fin Ref.parameterCount) (nu : Fin Ref.primaryCount) (W : Set (Ep × M))
    (old new : Round3PreparedPrimaryPiece Ref ip nu W) (h : new.cutoff = old.cutoff) :
    round3ParameterLiftedPrimaryCutoff Ref ip nu W new = round3ParameterLiftedPrimaryCutoff Ref ip nu W old := by
  unfold round3ParameterLiftedPrimaryCutoff
  rw [h]

def Round3ParameterWholePrimaryPieceSupply.replacePieces
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
    (out : ∀ nu i, packet.s nu i → Round3PreparedPrimaryPiece Ref i.2 nu
      ((Ref.parameterChart i.2).target ×ˢ (univ : Set M)))
    (hHost : ∀ nu i a, (out nu i a).host = (packet.piece nu i a).host)
    (hCut : ∀ nu i a, (out nu i a).cutoff = (packet.piece nu i a).cutoff) :
    Round3ParameterWholePrimaryPieceSupply Ref theta where
  s := packet.s
  piece := out
  host := fun nu i a => (hHost nu i a).trans (packet.host nu i a)
  native_parent := by intro nu i a; rw [hCut]; exact packet.native_parent nu i a
  smooth := by
    intro nu i a
    rw [round3Parameter_lifted_cutoff_eq_of_native_eq Ref i.2 nu _ _ _ (hCut nu i a)]
    exact packet.smooth nu i a
  compact := by
    intro nu i a
    rw [round3Parameter_lifted_cutoff_eq_of_native_eq Ref i.2 nu _ _ _ (hCut nu i a)]
    exact packet.compact nu i a
  parent := by
    intro nu i a
    rw [round3Parameter_lifted_cutoff_eq_of_native_eq Ref i.2 nu _ _ _ (hCut nu i a)]
    exact packet.parent nu i a
  source := by
    intro nu i a z hz
    have hOld : z ∈ tsupport (round3ParameterLiftedPrimaryCutoff Ref i.2 nu _ (packet.piece nu i a)) := by
      rwa [round3Parameter_lifted_cutoff_eq_of_native_eq Ref i.2 nu _ _ _ (hCut nu i a)] at hz
    have hOldSource := packet.source nu i a hOld
    have hParam := (round3ParameterChartPullback_source (Ref.parameterChart i.2).symm
      (actualHostAdaptedChart (Ref.atlas.chart (packet.piece nu i a).host) (packet.piece nu i a).native) z).mp hOldSource
    have hNativeEta := (round3ParameterSupportedPullback_tsupport_iff
      (round3ParameterProductChart (M := M) (Ref.parameterChart i.2)) (out nu i a).cutoff z
      ⟨hParam.1,mem_univ _⟩).mp hz
    apply (round3ParameterChartPullback_source_iff (Ref.parameterChart i.2).symm
      (actualHostAdaptedChart (Ref.atlas.chart (out nu i a).host) (out nu i a).native)
      (fun y hy => ((out nu i a).data.2.2.2.1 y hy).1) z hParam.1).mpr
    exact (out nu i a).support hNativeEta
  partition := by
    intro nu i z hz
    simp_rw [round3Parameter_lifted_cutoff_eq_of_native_eq Ref i.2 nu _ _ _ (hCut nu i _)]
    exact packet.partition nu i z hz
  count := by
    intro nu i z
    simp_rw [round3Parameter_lifted_cutoff_eq_of_native_eq Ref i.2 nu _ _ _ (hCut nu i _)]
    exact packet.count nu i z

theorem round3Parameter_replacement_same_global_eta
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (hn : IncrementsOriginalFreeNormalConditions Ref hd hs)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
    (out : ∀ nu i, packet.s nu i → Round3PreparedPrimaryPiece Ref i.2 nu
      ((Ref.parameterChart i.2).target ×ˢ (univ : Set M)))
    (hHost : ∀ nu i a, (out nu i a).host = (packet.piece nu i a).host)
    (hCut : ∀ nu i a, (out nu i a).cutoff = (packet.piece nu i a).cutoff) :
    (round3ParameterWholePrimaryFamily Ref hd hs hn theta
      (packet.replacePieces Ref theta out hHost hCut)).eta =
      (round3ParameterWholePrimaryFamily Ref hd hs hn theta packet).eta := by
  funext nu a z
  change (if z.1 ∈ (Ref.parameterChart a.1.2).source then
      (round3ParameterWholePrimaryPiece Ref hd theta (packet.replacePieces Ref theta out hHost hCut) nu a).cutoff
        ((Ref.parameterChart a.1.2) z.1,z.2) else 0) =
    (if z.1 ∈ (Ref.parameterChart a.1.2).source then
      (round3ParameterWholePrimaryPiece Ref hd theta packet nu a).cutoff
        ((Ref.parameterChart a.1.2) z.1,z.2) else 0)
  by_cases hp : z.1 ∈ (Ref.parameterChart a.1.2).source
  · simp only [hp,ite_true,round3ParameterWholePrimaryPiece,round3PreparedPrimarySigmaPiece,
      Round3ParameterWholePrimaryPieceSupply.replacePieces]
    split_ifs with h
    · exact congrFun (hCut nu a.1 (h ▸ a.2.2)) _
    · rfl
  · simp only [hp,ite_false]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.Round3ParameterWholePrimaryPieceSupply.replacePieces
#print axioms GlobalEmbedding.Continuation.round3Parameter_replacement_same_global_eta
