import Probes.Round3ParameterPrimarySigma

/-! Global primary geometry of the ONE all-chart family: genuine smooth
compact subordinate cutoffs, true ordinary germ partition, unchanged
original phase data, and a support bound controlled by parent overlap. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
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

set_option backward.isDefEq.respectTransparency true in
theorem round3ParameterWholePrimaryFamily_cutoff_geometry
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Data theta)
    (nu : Fin Data.primaryCount) (a : Round3ParameterWholePrimaryIndex Data theta packet) :
    let g := round3ParameterWholePrimaryFamily Data hd hs hn theta packet
    ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (g.eta nu a) ∧
    IsCompact (tsupport (g.eta nu a)) ∧
    tsupport (g.eta nu a) ⊆ tsupport (theta a.1) ∧
    tsupport (g.eta nu a) ⊆ (g.chart nu a).source := by
  intro g
  rcases a with ⟨i,⟨mu,a⟩⟩
  rw [round3ParameterWholePrimaryFamily_eta]
  by_cases h : mu = nu
  · subst mu
    change ContMDiff _ _ ∞ (round3ParameterLiftedPrimaryCutoff Data i.2 nu _
        (round3PreparedPrimarySigmaPiece Data hd i _ (fun mu => ↥(packet.s mu i))
          (fun mu b => packet.piece mu i b) nu ⟨nu,a⟩)) ∧ _
    simpa only [g,round3ParameterWholePrimaryFamily,round3ParameterOriginalPrimaryFamily,
      round3ParameterWholePrimaryPiece,round3PreparedPrimarySigmaPiece_active] using
      (show ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞
          (round3ParameterLiftedPrimaryCutoff Data i.2 nu _ (packet.piece nu i a)) ∧
        IsCompact (tsupport (round3ParameterLiftedPrimaryCutoff Data i.2 nu _ (packet.piece nu i a))) ∧
        tsupport (round3ParameterLiftedPrimaryCutoff Data i.2 nu _ (packet.piece nu i a)) ⊆ tsupport (theta i) ∧
        tsupport (round3ParameterLiftedPrimaryCutoff Data i.2 nu _ (packet.piece nu i a)) ⊆
          (round3ParameterLiftedPrimaryChart Data i.2 nu _ (packet.piece nu i a)).source from
        ⟨packet.smooth nu i a,packet.compact nu i a,packet.parent nu i a,packet.source nu i a⟩)
  · simp only [round3ParameterWholePrimaryPiece,round3PreparedPrimarySigmaPiece,h,dite_false,
      round3ParameterLiftedPrimaryCutoff_empty,tsupport_zero]
    exact ⟨contMDiff_const,isCompact_empty,empty_subset _,empty_subset _⟩

theorem round3ParameterWholePrimaryFamily_partition
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Data theta)
    (hPart : ∀ z, ∑ i, theta i z = 1)
    (nu : Fin Data.primaryCount) (z : P × M) (hz : z ∈ tsupport (Data.cutoff nu)) :
    ∀ᶠ w in 𝓝 z, ∑ a, (round3ParameterWholePrimaryFamily Data hd hs hn theta packet).eta nu a w = 1 := by
  have hall : ∀ᶠ w in 𝓝 z, ∀ i : Fin Data.atlas.count × Fin Data.parameterCount,
      ∑ a : packet.s nu i, round3ParameterLiftedPrimaryCutoff Data i.2 nu _ (packet.piece nu i a) w = theta i w :=
    eventually_all.mpr (fun i => packet.partition nu i z hz)
  filter_upwards [hall] with w hw
  rw [round3ParameterWholePrimaryFamily_eta_sum]
  exact (Finset.sum_congr rfl (fun i _ => hw i)).trans (hPart w)

theorem round3ParameterWholePrimaryFamily_count
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Data theta)
    (R : ℕ) (hCount : ∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ R)
    (nu : Fin Data.primaryCount) (z : P × M) :
    (Finset.univ.filter (fun a => z ∈ tsupport
      ((round3ParameterWholePrimaryFamily Data hd hs hn theta packet).eta nu a))).card ≤
      R*5^Module.finrank ℝ (Ep × D) := by
  let g := round3ParameterWholePrimaryFamily Data hd hs hn theta packet
  have hParent (i) (a : Sigma (fun mu => ↥(packet.s mu i))) : tsupport (g.eta nu ⟨i,a⟩) ⊆ tsupport (theta i) :=
    (round3ParameterWholePrimaryFamily_cutoff_geometry Data hd hs hn theta packet nu ⟨i,a⟩).2.2.1
  have hLocal (i : Fin Data.atlas.count × Fin Data.parameterCount) :
      (Finset.univ.filter (fun a : Sigma (fun mu => ↥(packet.s mu i)) => z ∈ tsupport (g.eta nu ⟨i,a⟩))).card ≤
        5^Module.finrank ℝ (Ep × D) := by
    rw [round3ParameterWholePrimaryFamily_eta_card]
    exact packet.count nu i z
  exact round3_prepared_sigma_local_count (fun i : Fin Data.atlas.count × Fin Data.parameterCount =>
      Sigma (fun mu => ↥(packet.s mu i))) (fun i => tsupport (theta i))
    (fun i a => tsupport (g.eta nu ⟨i,a⟩)) hParent R (5^Module.finrank ℝ (Ep × D)) z (hCount z) hLocal

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3ParameterWholePrimaryFamily_cutoff_geometry
#print axioms GlobalEmbedding.Continuation.round3ParameterWholePrimaryFamily_partition
#print axioms GlobalEmbedding.Continuation.round3ParameterWholePrimaryFamily_count
