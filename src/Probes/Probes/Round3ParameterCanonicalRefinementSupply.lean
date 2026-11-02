import Probes.Round3ParameterNativeRefinementSamples
import Probes.Round3ParameterCrossNativeFamily

/-! The one physical all-chart primary family supplies the genuine original
native refinement packet in EVERY parameter observer. Host charts and slices
are the actual two-sided nonlinear parameter conjugates. Every sample and
all-order bound is produced, and the original native family is proved HEq to
the canonical representative of the same physical family. -/

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

theorem round3Parameter_refinement_samples_heq
    (Data : IncrementsOriginalNativeData (m+1) d N M P) (ip : Fin Data.parameterCount)
    {Sub : Type*} [Fintype Sub]
    {F F' : Ep → M → Ey} (hF : F = F')
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Sub) F)
    (g' : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Sub) F')
    (hg : HEq g g')
    (host : Fin Data.primaryCount → Sub → Fin Data.atlas.count)
    (b : Fin Data.primaryCount → Sub → OpenPartialHomeomorph X X)
    (W : Set (Ep × M)) (ell : ℝ) (Tinv Forward Meta : ℕ → ℝ) (Rsub Lprimary : ℕ) :
    Round3ParameterRefinementSamples Data ip F g host b W ell Tinv Forward Meta Rsub Lprimary ↔
      Round3ParameterRefinementSamples Data ip F' g' host b W ell Tinv Forward Meta Rsub Lprimary := by
  cases hF
  cases eq_of_heq hg
  rfl

theorem round3Parameter_canonical_original_refinement_supply
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs) (hAll : Data.parameterSet = univ)
    {Sub : Type*} [Fintype Sub]
    (ip : Fin Data.primaryCount → Sub → Fin Data.parameterCount)
    (W : Fin Data.primaryCount → Sub → Set (Ep × M))
    (piece : ∀ nu a, Round3PreparedPrimaryPiece Data (ip nu a) nu (W nu a))
    (hInner : ∀ nu a y,
      y ∈ (actualHostAdaptedChart (Data.atlas.chart (piece nu a).host) (piece nu a).native).source →
      y.2 ∈ Data.atlas.inner (piece nu a).host)
    (R : ℕ)
    (hGeometry : Round3ParameterOriginalPrimaryGeometry Data
      (round3ParameterOriginalPrimaryFamily Data hd hs hn ip W piece) R)
    (Forward Inverse Meta : ℕ → ℝ)
    (hProfiles : Round3ParameterOriginalChartProfiles Data
      (round3ParameterOriginalPrimaryFamily Data hd hs hn ip W piece) Forward Inverse Meta)
    (ell : ℝ) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (observer : Fin Data.atlas.count × Fin Data.parameterCount) :
    let g := round3ParameterOriginalPrimaryFamily Data hd hs hn ip W piece
    let gN := round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart observer.2)
    let host := fun nu a => (piece nu a).host
    let b := fun nu a => round3ParameterCrossNativeChart (Data.parameterChart (ip nu a))
      (Data.parameterChart observer.2) (piece nu a).native
    ∃ (e : Fin Data.primaryCount → Sub → Ep → OpenPartialHomeomorph M D)
      (hdata : ∀ nu a, ActualOriginalHostSliceData (Data.atlas.chart (host nu a)) (b nu a)
        (fun z : Ep × M => Data.phase nu ((Data.parameterChart observer.2).symm z.1,z.2)) (e nu a))
      (hactive : ∀ nu a w, w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu a)) (b nu a)).source →
        ((Data.parameterChart observer.2).symm w.1,w.2) ∈
          Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data),
      (∀ nu a, (b nu a).source ⊆ actualOriginalNativeOpen Data (host nu a,observer.2)) ∧
      (∀ nu a p x, (e nu a p).symm x =
        ((piece nu a).slices ((Data.parameterChart (ip nu a)) ((Data.parameterChart observer.2).symm p))).symm x) ∧
      HEq (actualOriginalPrimaryFamily Data hd hs hn observer host b e hdata gN.eta hactive) gN ∧
      Round3ParameterRefinementSamples Data observer.2 (actualOriginalOpenParameterSlice Data observer)
        (actualOriginalPrimaryFamily Data hd hs hn observer host b e hdata gN.eta hactive)
        host b ((Data.parameterChart observer.2).target ×ˢ (univ : Set M)) ell Inverse
        (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+2) => Forward k))
        (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+1) => Meta k)) R Data.primaryCount := by
  intro g gN host b
  obtain ⟨e,hdata,hactive,hNative,hSlices,hSame⟩ :=
    round3Parameter_original_global_family_native_presentation Data hd hs hn hAll ip W piece observer
  have hChart (nu) (a) : actualHostAdaptedChart (Data.atlas.chart (host nu a)) (b nu a) = gN.chart nu a :=
    round3Parameter_cross_host_conjugation (Data.parameterChart (ip nu a))
      (Data.parameterChart observer.2) (Data.atlas.chart (piece nu a).host) (piece nu a).native
      (round3Parameter_primary_native_preserves_phase Data hd (ip nu a) nu (W nu a) (piece nu a)).1
  have hSource (nu) (a) : (b nu a).source ⊆
      (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart (host nu a))).target := by
    intro z hz
    exact ⟨mem_univ _,((round3Parameter_originalNativeOpen_iff Data (host nu a,observer.2) z).mp
      (hNative nu a hz)).1⟩
  have hInnerNative (nu) (a) (y : Ep × M) (hy : y ∈ (gN.chart nu a).source) :
      y.2 ∈ Data.atlas.inner (host nu a) := by
    have h1 := (round3ParameterChartPullback_source (Data.parameterChart observer.2)
      (g.chart nu a) y).mp hy
    have h2 := (round3ParameterChartPullback_source (Data.parameterChart (ip nu a)).symm
      (actualHostAdaptedChart (Data.atlas.chart (piece nu a).host) (piece nu a).native)
      ((Data.parameterChart observer.2).symm y.1,y.2)).mp h1.2.1
    exact hInner nu a ((Data.parameterChart (ip nu a)) ((Data.parameterChart observer.2).symm y.1),y.2) h2.2.1
  have hCtrl := round3Parameter_native_original_refinement_samples Data hd g R hGeometry observer.2
    host b hChart hSource hInnerNative Forward Inverse Meta hProfiles ell hell hell1
    ((Data.parameterChart observer.2).target ×ˢ (univ : Set M))
    ((Data.parameterChart observer.2).open_target.prod isOpen_univ) Subset.rfl
  refine ⟨e,hdata,hactive,hNative,hSlices,hSame,?_⟩
  exact (round3Parameter_refinement_samples_heq Data observer.2
    (round3Parameter_original_open_slice_eq_global Data hd hAll observer)
    _ _ hSame host b _ ell Inverse _ _ R Data.primaryCount).mpr hCtrl

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_refinement_samples_heq
#print axioms GlobalEmbedding.Continuation.round3Parameter_canonical_original_refinement_supply
