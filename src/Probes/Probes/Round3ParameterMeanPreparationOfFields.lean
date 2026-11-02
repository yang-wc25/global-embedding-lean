import Probes.Round3ParameterOriginalMeanPreparation

/-! The fixed-carrier family is consumed without changing its eta again.
Any actual host/slice realization of its canonical charts supplies the whole
native mean preparation. Original phase/cutoff/normal/linear identities,
canonical eta, all samples and all local multiplicities are proved internally. -/

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
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}

private theorem meanNativeFamily_heq
    {Sub Label : Type*} [Fintype Sub] [Fintype Label]
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

theorem round3Parameter_actual_mean_preparation_of_global_fields
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs) (hAll : Data.parameterSet = univ)
    {Sub : Type*} [Fintype Sub]
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Sub)
      (fun p x => Data.F (p,x)))
    (R : ℕ) (hg : Round3ParameterOriginalPrimaryGeometry Data g R)
    (Forward Inverse Meta : ℕ → ℝ)
    (hProfiles : Round3ParameterOriginalChartProfiles Data g Forward Inverse Meta)
    (ell cT : ℝ) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (host : Fin Data.primaryCount → Sub → Fin Data.atlas.count)
    (b : Fin Data.primaryCount → Sub → OpenPartialHomeomorph X X)
    (e : Fin Data.primaryCount → Sub → Ep → OpenPartialHomeomorph M D)
    (hdata : ∀ nu a, ActualOriginalHostSliceData (Data.atlas.chart (host nu a)) (b nu a)
      (fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) (e nu a))
    (hactive : ∀ nu a w, w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu a)) (b nu a)).source →
      ((Data.parameterChart i.2).symm w.1,w.2) ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data)
    (hNative : ∀ nu a, (b nu a).source ⊆ actualOriginalNativeOpen Data (host nu a,i.2))
    (hInner : ∀ nu a w, w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu a)) (b nu a)).source →
      w.2 ∈ Data.atlas.inner (host nu a))
    (hChart : ∀ nu a, actualHostAdaptedChart (Data.atlas.chart (host nu a)) (b nu a) =
      (round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart i.2)).chart nu a)
    (hInverse : ∀ nu a p x, (e nu a p).symm x = g.inverse nu a ((Data.parameterChart i.2).symm p) x)
    (hTransverse : ∀ nu a z, z ∈ (b nu a).target → ∀ v : Tdata, cT*‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame (actualOriginalOpenParameterSlice Data i z.1)
        (actualOriginalOpenParameterSlice_contMDiff Data hd hs i z.1) (e nu a z.1).symm z.2 v‖^2) :
    Nonempty (Round3ParameterOriginalNativeMeanPreparation Data hd hs hn g ell cT Inverse
      (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+2) => Forward k))
      (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+1) => Meta k)) R Data.primaryCount i) := by
  let gN := round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart i.2)
  let g0 := actualOriginalPrimaryFamily Data hd hs hn i host b e hdata gN.eta hactive
  have hSame : HEq g0 gN := by
    apply meanNativeFamily_heq (round3Parameter_original_open_slice_eq_global Data hd hAll i) g0 gN
      ?_ ?_ ?_ ?_ rfl (funext (fun nu => funext (hChart nu))) (by funext nu a p x; exact hInverse nu a p x)
    · funext nu z
      exact (congrFun (congrFun hg.phase nu) ((Data.parameterChart i.2).symm z.1,z.2)).symm
    · funext nu z
      exact (congrFun (congrFun hg.cutoff nu) ((Data.parameterChart i.2).symm z.1,z.2)).symm
    · funext nu z
      exact (congrFun (congrFun hg.normal nu) ((Data.parameterChart i.2).symm z.1,z.2)).symm
    · funext nu p x
      exact (congrFun (congrFun (congrFun hg.linear nu) ((Data.parameterChart i.2).symm p)) x).symm
  have hSource (nu) (a) := (actual_host_slice_geometry_inputs
    (Data.atlas.chart (host nu a)) (hd.atlas_smooth.chart_mem (host nu a)) (b nu a)
    _ (e nu a) (hdata nu a)).1
  have hInnerNative (nu) (a) (w : Ep × M) (hw : w ∈ (gN.chart nu a).source) :
      w.2 ∈ Data.atlas.inner (host nu a) := hInner nu a w (by rwa [hChart nu a])
  have ctrl := round3Parameter_native_original_refinement_samples Data hd g R hg i.2 host b hChart
    hSource hInnerNative Forward Inverse Meta hProfiles ell hell hell1
    ((Data.parameterChart i.2).target ×ˢ (univ : Set M))
    ((Data.parameterChart i.2).open_target.prod isOpen_univ) Subset.rfl
  refine ⟨{
    host := host
    native := b
    slices := e
    data := hdata
    active := hactive
    native_open := hNative
    same := hSame
    transverse := hTransverse
    refinement := ?_ }⟩
  exact (round3Parameter_refinement_samples_heq Data i.2
    (round3Parameter_original_open_slice_eq_global Data hd hAll i) g0 gN hSame host b _ ell
    Inverse _ _ R Data.primaryCount).mpr ctrl

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_actual_mean_preparation_of_global_fields
