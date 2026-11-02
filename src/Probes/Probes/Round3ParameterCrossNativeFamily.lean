import Probes.Round3ParameterCrossNativeData
import Probes.Round3ParameterNativeFamily
import Probes.ActualIncrementOriginalPrimaryFamily

/-! Exact original-family presentation of the canonical native pullback of
ONE global all-chart family.  The actual host/slice packets are constructed,
and the full family is heterogeneously equal only because its base-map type
uses the original open-parameter slice. On K=P that slice is the SAME map at
every parameter value. No local independently chosen increment is introduced. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
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

private theorem round3_native_family_heq
    {Label Sub : Type*} [Fintype Label] [Fintype Sub]
    {F F' : Ep → M → Ey} (hF : F = F')
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (Λ := Label) (Β := Sub) F)
    (g' : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (Λ := Label) (Β := Sub) F')
    (hPhase : g.phase = g'.phase) (hCut : g.cutoff = g'.cutoff)
    (hNormal : g.normal = g'.normal) (hLinear : g.linearArgument = g'.linearArgument)
    (hEta : g.eta = g'.eta) (hChart : g.chart = g'.chart) (hInverse : g.inverse = g'.inverse) :
    HEq g g' := by
  cases hF
  cases g
  cases g'
  cases hPhase
  cases hCut
  cases hNormal
  cases hLinear
  cases hEta
  cases hChart
  cases hInverse
  rfl

theorem round3Parameter_original_open_slice_eq_global
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hAll : Data.parameterSet = univ)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) :
    actualOriginalOpenParameterSlice Data i = fun p x => Data.F ((Data.parameterChart i.2).symm p,x) := by
  funext p
  exact actualOriginalOpenParameterSlice_eq Data i p
    (hd.parameter_subset (by rw [hAll]; exact mem_univ _))

theorem round3Parameter_original_global_family_native_presentation
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs) (hAll : Data.parameterSet = univ)
    {Sub : Type*} [Fintype Sub]
    (ip : Fin Data.primaryCount → Sub → Fin Data.parameterCount)
    (W : Fin Data.primaryCount → Sub → Set (Ep × M))
    (piece : ∀ nu a, Round3PreparedPrimaryPiece Data (ip nu a) nu (W nu a))
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
      HEq (actualOriginalPrimaryFamily Data hd hs hn observer host b e hdata gN.eta hactive) gN := by
  intro g gN host b
  have hEach (nu : Fin Data.primaryCount) (a : Sub) :=
    round3Parameter_actual_cross_native_data Data hd (ip nu a) observer.2 nu (W nu a) (piece nu a)
  choose e hdata hNative hactive hSlices using hEach
  refine ⟨e,hdata,hactive,hNative,hSlices,?_⟩
  apply round3_native_family_heq (round3Parameter_original_open_slice_eq_global Data hd hAll observer)
    (actualOriginalPrimaryFamily Data hd hs hn observer host b e hdata gN.eta hactive) gN
    rfl rfl rfl rfl rfl
  · funext nu a
    exact round3Parameter_cross_host_conjugation (Data.parameterChart (ip nu a))
      (Data.parameterChart observer.2) (Data.atlas.chart (piece nu a).host) (piece nu a).native
      (round3Parameter_primary_native_preserves_phase Data hd (ip nu a) nu (W nu a) (piece nu a)).1
  · funext nu a p x
    exact hSlices nu a p x

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_original_open_slice_eq_global
#print axioms GlobalEmbedding.Continuation.round3Parameter_original_global_family_native_presentation
