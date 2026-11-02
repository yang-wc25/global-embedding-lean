import Probes.Round3ParameterWholePrimaryPieces

/-! One actual subordinate primary cutoff per original observing chart.
The cutoff is the original parent times an actual primary plateau. No
second chart selection or observing-chart refinement radius is involved. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Filter
open scoped ContDiff Topology BigOperators Classical
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
local notation "I" => 𝓘(ℝ,D)
local notation "IJ" => ModelWithCorners.prod 𝓘(ℝ,Ep) 𝓘(ℝ,D)

theorem repair_reference_singleton_primary_supply
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (hCompact : ∀ i, IsCompact (tsupport (theta i)))
    (hSmooth : ∀ i, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (theta i))
    (hSupport : ∀ i, tsupport (theta i) ⊆ (Data.parameterChart i.2).source ×ˢ (univ : Set M))
    (plateau : Fin Data.primaryCount → P × M → ℝ)
    (hPlateau : ∀ nu, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (plateau nu))
    (hGerm : ∀ nu z, z ∈ tsupport (Data.cutoff nu) → plateau nu =ᶠ[𝓝 z] fun _ => 1)
    (native : Fin Data.primaryCount → (Fin Data.atlas.count × Fin Data.parameterCount) → OpenPartialHomeomorph X X)
    (slices : Fin Data.primaryCount → (Fin Data.atlas.count × Fin Data.parameterCount) → Ep → OpenPartialHomeomorph M D)
    (hData : ∀ nu i, ActualOriginalHostSliceData (Data.atlas.chart i.1) (native nu i)
      (fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) (slices nu i))
    (hNative : ∀ nu i, (native nu i).source ⊆ actualOriginalNativeOpen Data i)
    (hSource : ∀ nu i, (actualHostAdaptedChart (Data.atlas.chart i.1) (native nu i)).source ⊆
      (Data.parameterChart i.2).target ×ˢ (univ : Set M))
    (hActive : ∀ nu i z, z ∈ (actualHostAdaptedChart (Data.atlas.chart i.1) (native nu i)).source →
      ((Data.parameterChart i.2).symm z.1,z.2) ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data)
    (hCover : ∀ nu i z, z ∈ tsupport (theta i) ∩ tsupport (plateau nu) →
      (Data.parameterChart i.2 z.1,z.2) ∈ (actualHostAdaptedChart (Data.atlas.chart i.1) (native nu i)).source)
    (B : ℝ) (hB : 0 < B)
    (hFirst : ∀ nu i z, z ∈ (native nu i).source → ‖fderiv ℝ (native nu i) z‖ ≤ B) :
    ∃ packet : Round3ParameterWholePrimaryPieceSupply Data theta,
      (∀ nu i, (packet.s nu i).card=1) ∧
      (∀ nu i a, (packet.piece nu i a).native=native nu i) ∧
      (∀ nu i a, (packet.piece nu i a).slices=slices nu i) ∧
      ∀ nu i a, round3ParameterLiftedPrimaryCutoff Data i.2 nu _ (packet.piece nu i a)=
        fun z => theta i z*plateau nu z := by
  let s := fun (_ : Fin Data.primaryCount) (_ : Fin Data.atlas.count × Fin Data.parameterCount) =>
    ({0} : Finset X)
  let eta := fun nu i (z : P × M) => theta i z*plateau nu z
  have hEtaCompact (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount) :
      IsCompact (tsupport (eta nu i)) :=
    (hCompact i).of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_left
  have hEtaSource (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount) :
      tsupport (eta nu i) ⊆ (Data.parameterChart i.2).source ×ˢ (univ : Set M) :=
    tsupport_mul_subset_left.trans (hSupport i)
  have hEtaNative (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount) :=
    round3Parameter_native_compact_parent (Data.parameterChart i.2) (hd.parameter_charts_smooth i.2)
      (eta nu i) (hEtaCompact nu i) ((hSmooth i).mul (hPlateau nu)) (hEtaSource nu i)
  let nativeEta := fun nu i => round3ParameterNativeParent (Data.parameterChart i.2) (eta nu i)
  have hNativeSupport (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount) :
      tsupport (nativeEta nu i) ⊆ (actualHostAdaptedChart (Data.atlas.chart i.1) (native nu i)).source := by
    intro z hz
    obtain ⟨y,hy,rfl⟩ := (hEtaNative nu i).2.2 hz
    exact hCover nu i y ⟨tsupport_mul_subset_left hy,tsupport_mul_subset_right hy⟩
  have hNativeParent (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount) :
      tsupport (nativeEta nu i) ⊆ tsupport (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)) := by
    have heq : nativeEta nu i = fun z =>
        round3ParameterNativeParent (Data.parameterChart i.2) (theta i) z *
          plateau nu ((Data.parameterChart i.2).symm z.1,z.2) := by
      funext z
      change (if z ∈ (round3ParameterProductChart (M := M) (Data.parameterChart i.2)).target then _ else 0)=_
      by_cases hz : z ∈ (round3ParameterProductChart (M := M) (Data.parameterChart i.2)).target
      · simp only [if_pos hz,round3ParameterNativeParent,round3ParameterSupportedPullback,
          OpenPartialHomeomorph.symm_source,if_pos hz]
        rfl
      · simp only [if_neg hz,round3ParameterNativeParent,round3ParameterSupportedPullback,
          OpenPartialHomeomorph.symm_source,if_neg hz,zero_mul]
    rw [heq]
    exact tsupport_mul_subset_left
  let piece := fun nu i (_ : s nu i) => ({
    host := i.1
    native := native nu i
    slices := slices nu i
    cutoff := nativeEta nu i
    data := hData nu i
    native_source := hNative nu i
    source_domain := hSource nu i
    active := hActive nu i
    compact := (hEtaNative nu i).2.1
    smooth := (hEtaNative nu i).1
    support := hNativeSupport nu i
    Bnative := B
    positive := hB
    native_first := hFirst nu i } : Round3PreparedPrimaryPiece Data i.2 nu ((Data.parameterChart i.2).target ×ˢ (univ : Set M)))
  have hLiftEq (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount) (a : s nu i) :
      round3ParameterLiftedPrimaryCutoff Data i.2 nu _ (piece nu i a)=eta nu i := by
    funext z
    rw [round3ParameterLiftedPrimaryCutoff_eq]
    by_cases hz : z.1 ∈ (Data.parameterChart i.2).source
    · rw [if_pos hz]
      exact round3ParameterNativeParent_eq (Data.parameterChart i.2) (eta nu i) z hz
    · rw [if_neg hz]
      exact (image_eq_zero_of_notMem_tsupport (fun h => hz (hEtaSource nu i h).1)).symm
  have hParent (i : Fin Data.atlas.count × Fin Data.parameterCount) :=
    round3Parameter_native_compact_parent (Data.parameterChart i.2) (hd.parameter_charts_smooth i.2)
      (theta i) (hCompact i) (hSmooth i) (hSupport i)
  have hLift (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount) (a : s nu i) :=
    round3Parameter_original_primary_cutoff Data hd i.2 nu _ (piece nu i a)
      (theta i) (hCompact i) (hSupport i) (hParent i).2.2 (hNativeParent nu i)
  let packet : Round3ParameterWholePrimaryPieceSupply Data theta := {
    s := s
    piece := piece
    host := fun _ _ _ => rfl
    native_parent := fun nu i _ => hNativeParent nu i
    smooth := fun nu i a => (hLift nu i a).1
    compact := fun nu i a => (hLift nu i a).2.1
    parent := fun nu i a => (hLift nu i a).2.2.1
    source := fun nu i a => (hLift nu i a).2.2.2
    partition := by
      intro nu i z hz
      filter_upwards [hGerm nu z hz] with y hy
      simp only [hLiftEq,eta,hy,mul_one]
      simp [s]
    count := by
      intro nu i z
      have hh := Finset.card_filter_le (s := (Finset.univ : Finset (s nu i)))
        (p := fun a => z ∈ tsupport (round3ParameterLiftedPrimaryCutoff Data i.2 nu _ (piece nu i a)))
      have hc : Fintype.card (s nu i)=1 := by simp [s]
      rw [Finset.card_univ,hc] at hh
      exact hh.trans (one_le_pow₀ (by norm_num)) }
  exact ⟨packet,fun _ _ => by simp [packet,s],fun _ _ _ => rfl,fun _ _ _ => rfl,hLiftEq⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repair_reference_singleton_primary_supply
