import Probes.Round3ParameterWholePrimaryGeometry

/-! The actual geometric contract of a global ORIGINAL primary family.
Every original field is literally bound, while charts and subordinate eta
are constructed. No coefficient or output estimate is assumed. -/

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

structure Round3ParameterOriginalPrimaryGeometry
    (Data : IncrementsOriginalNativeData (m+1) d N M P) {Β : Type*} [Fintype Β]
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := Β) (fun p x => Data.F (p,x))) (R : ℕ) : Prop where
  phase : g.phase = Data.phase
  cutoff : g.cutoff = Data.cutoff
  normal : g.normal = Data.freeNormal
  linear : g.linearArgument = Data.linearArgument
  preserves : ∀ nu a, Round3ParameterChartPreserves (g.chart nu a)
  inverse : ∀ nu a z, z ∈ (g.chart nu a).target →
    (g.chart nu a).symm z = (z.1,g.inverse nu a z.1 z.2)
  phase_coordinate : ∀ nu a z, z ∈ (g.chart nu a).target →
    Data.phase nu (z.1,g.inverse nu a z.1 z.2) = z.2 0
  inverse_active : ∀ nu a z, z ∈ (g.chart nu a).target →
    (z.1,g.inverse nu a z.1 z.2) ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data
  smooth : ∀ nu a, ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (g.eta nu a)
  compact : ∀ nu a, IsCompact (tsupport (g.eta nu a))
  support : ∀ nu a, tsupport (g.eta nu a) ⊆ (g.chart nu a).source
  partition : ∀ nu z, z ∈ tsupport (Data.cutoff nu) → ∀ᶠ w in 𝓝 z, ∑ a, g.eta nu a w = 1
  count : ∀ nu z, (Finset.univ.filter (fun a => z ∈ tsupport (g.eta nu a))).card ≤ R

set_option backward.isDefEq.respectTransparency true in
theorem round3Parameter_whole_primary_family_geometry
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Data theta)
    (hPart : ∀ z, ∑ i, theta i z = 1)
    (R : ℕ) (hCount : ∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ R) :
    Round3ParameterOriginalPrimaryGeometry Data (round3ParameterWholePrimaryFamily Data hd hs hn theta packet)
      (R*5^Module.finrank ℝ (Ep × D)) where
  phase := rfl
  cutoff := rfl
  normal := rfl
  linear := rfl
  preserves := round3ParameterOriginalPrimaryFamily_preserves Data hd hs hn _ _ _
  inverse := fun nu a z hz => round3ParameterLiftedPrimaryChart_inverse Data a.1.2 nu _
    (round3ParameterWholePrimaryPiece Data hd theta packet nu a) z hz
  phase_coordinate := fun nu a z hz => round3ParameterLiftedPrimaryChart_phase Data a.1.2 nu _
    (round3ParameterWholePrimaryPiece Data hd theta packet nu a) z hz
  inverse_active := fun nu a z hz => round3ParameterLiftedPrimaryChart_active Data a.1.2 nu _
    (round3ParameterWholePrimaryPiece Data hd theta packet nu a) z hz
  smooth := fun nu a => (round3ParameterWholePrimaryFamily_cutoff_geometry Data hd hs hn theta packet nu a).1
  compact := fun nu a => (round3ParameterWholePrimaryFamily_cutoff_geometry Data hd hs hn theta packet nu a).2.1
  support := fun nu a => (round3ParameterWholePrimaryFamily_cutoff_geometry Data hd hs hn theta packet nu a).2.2.2
  partition := round3ParameterWholePrimaryFamily_partition Data hd hs hn theta packet hPart
  count := round3ParameterWholePrimaryFamily_count Data hd hs hn theta packet R hCount

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_whole_primary_family_geometry
