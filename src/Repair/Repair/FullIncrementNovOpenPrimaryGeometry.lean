import Repair.FullIncrementNovOpenPrimaryFactory
import Probes.Round3ParameterNativeRefinementGeometry
import Probes.ActualIncrementOriginalMeanPrimitives

/-! The actual open-parameter packet supplies a genuine local partition and
native refinement geometry.  The existing global geometry record is not
weakened or reinterpreted: its global partition field is simply unnecessary
here.  The same eta functions, charts, parent supports and count are used on
the actual original neighborhood, with ordinary germs in the ambient space.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
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

theorem fullIncrementNov_whole_primary_open_partition
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Data theta)
    (V : Set P) (hV : IsOpen V) (hPart : ∀ z : P × M, z.1 ∈ V → ∑ i, theta i z = 1)
    (nu : Fin Data.primaryCount) (z : P × M) (hzV : z.1 ∈ V)
    (hz : z ∈ tsupport (Data.cutoff nu)) :
    ∀ᶠ w in 𝓝 z, ∑ a, (round3ParameterWholePrimaryFamily Data hd hs hn theta packet).eta nu a w = 1 := by
  have hall : ∀ᶠ w in 𝓝 z, ∀ i : Fin Data.atlas.count × Fin Data.parameterCount,
      ∑ a : packet.s nu i, round3ParameterLiftedPrimaryCutoff Data i.2 nu _
        (packet.piece nu i a) w = theta i w :=
    eventually_all.mpr (fun i => packet.partition nu i z hz)
  filter_upwards [hall,(hV.preimage continuous_fst).mem_nhds hzV] with w hw hwV
  rw [round3ParameterWholePrimaryFamily_eta_sum]
  exact (Finset.sum_congr rfl (fun i _ => hw i)).trans (hPart w hwV)

theorem fullIncrementNov_whole_primary_open_native_geometry
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Data theta)
    (V : Set P) (hV : IsOpen V) (hPart : ∀ z : P × M, z.1 ∈ V → ∑ i, theta i z = 1)
    (R : ℕ) (hCount : ∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ R)
    (ip : Fin Data.parameterCount) :
    let g := round3ParameterWholePrimaryFamily Data hd hs hn theta packet
    let gN := round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart ip)
    let W := actualOriginalParameterNeighborhood Data ip (V ×ˢ (univ : Set M))
    (∀ nu a, ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (gN.eta nu a) W) ∧
    (∀ nu a, incrementsGlobalRelativeSupport W (gN.eta nu a) ⊆ (gN.chart nu a).source) ∧
    (∀ nu z, z ∈ incrementsGlobalRelativeSupport W (gN.cutoff nu) →
      ∀ᶠ w in 𝓝 z, ∑ a, gN.eta nu a w = 1) ∧
    (∀ nu z, z ∈ W → (Finset.univ.filter
      (fun a => z ∈ incrementsGlobalRelativeSupport W (gN.eta nu a))).card ≤
        R*5^Module.finrank ℝ (Ep × D)) ∧
    ∀ z, z ∈ W → (Finset.univ.filter
      (fun nu => z ∈ incrementsGlobalRelativeSupport W (gN.cutoff nu))).card ≤ Data.primaryCount := by
  intro g gN W
  let B := Data.parameterChart ip
  let q := round3ParameterProductChart (M := M) B
  have hW : IsOpen W := actualOriginalParameterNeighborhood_isOpen Data ip _ (hV.prod isOpen_univ)
  have hWB : W ⊆ B.target ×ˢ (univ : Set M) := inter_subset_left
  have hq : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ q.symm W :=
    (round3ParameterProductChart_symm_smooth (n := m+1) (M := M) B
      (hd.parameter_charts_smooth ip)).mono hWB
  have hEta (nu : Fin Data.primaryCount)
      (a : Round3ParameterWholePrimaryIndex Data theta packet) (z : Ep × M)
      (hz : z ∈ incrementsGlobalRelativeSupport W (gN.eta nu a)) :
      (B.symm z.1,z.2) ∈ tsupport (g.eta nu a) := by
    rw [parameterRound2_global_relativeSupport_eq W hW] at hz
    exact round3Parameter_plain_pullback_tsupport q (g.eta nu a) z (hWB hz.1) hz.2
  have hPreserves := round3ParameterOriginalPrimaryFamily_preserves Data hd hs hn
    (fun (_ : Fin Data.primaryCount) (a : Round3ParameterWholePrimaryIndex Data theta packet) => a.1.2)
    (fun _ a => (Data.parameterChart a.1.2).target ×ˢ (univ : Set M))
    (round3ParameterWholePrimaryPiece Data hd theta packet)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro nu a
    exact (round3ParameterWholePrimaryFamily_cutoff_geometry Data hd hs hn theta packet nu a).1.comp_contMDiffOn hq
  · intro nu a z hz
    have hzW : z ∈ W := by
      rw [parameterRound2_global_relativeSupport_eq W hW] at hz
      exact hz.1
    apply (round3ParameterChartPullback_source_iff B (g.chart nu a) (hPreserves nu a) z (hWB hzW).1).mpr
    exact (round3ParameterWholePrimaryFamily_cutoff_geometry Data hd hs hn theta packet nu a).2.2.2
      (hEta nu a z hz)
  · intro nu z hz
    rw [parameterRound2_global_relativeSupport_eq W hW] at hz
    have hp : (B.symm z.1,z.2) ∈ tsupport (Data.cutoff nu) :=
      round3Parameter_plain_pullback_tsupport q (Data.cutoff nu) z (hWB hz.1) hz.2
    have ht : Tendsto q.symm (𝓝 z) (𝓝 (q.symm z)) :=
      q.symm.continuousOn.continuousAt (q.open_target.mem_nhds (hWB hz.1))
    exact ht.eventually (fullIncrementNov_whole_primary_open_partition Data hd hs hn theta packet
      V hV hPart nu (q.symm z) hz.1.2.1 hp)
  · intro nu z hz
    apply (Finset.card_le_card ?_).trans
      (round3ParameterWholePrimaryFamily_count Data hd hs hn theta packet R hCount nu (B.symm z.1,z.2))
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hEta nu a z (Finset.mem_filter.mp ha).2⟩
  · intro z hz
    exact (Finset.card_filter_le _ _).trans_eq (by simp)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.fullIncrementNov_whole_primary_open_partition
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_whole_primary_open_native_geometry
