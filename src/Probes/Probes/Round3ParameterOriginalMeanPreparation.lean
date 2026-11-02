import Probes.Round3ParameterCanonicalRefinementSupply

/-! Genuine original input packets for the one global mean supplier.
Each observer is the canonical representation of the same physical family;
native slice data, all refinement samples and the actual transverse reserve
are produced from its actual all-parameter pieces. -/

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

theorem round3Parameter_original_cross_transverse_reserve
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hAll : Data.parameterSet = univ)
    (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => Data.F (p,x)))
    (ip : Fin Data.parameterCount) (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (nu : Fin Data.primaryCount) (W : Set (Ep × M)) (piece : Round3PreparedPrimaryPiece Data ip nu W)
    (e : Ep → OpenPartialHomeomorph M D)
    (hSlices : ∀ p x, (e p).symm x = (piece.slices ((Data.parameterChart ip) ((Data.parameterChart i.2).symm p))).symm x)
    (cT : ℝ)
    (hNative : ∀ z ∈ piece.native.target, ∀ v : Tdata, cT*‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame (fun x => Data.F ((Data.parameterChart ip).symm z.1,x))
        (hF ((Data.parameterChart ip).symm z.1)) (piece.slices z.1).symm z.2 v‖^2) :
    ∀ z ∈ (round3ParameterCrossNativeChart (Data.parameterChart ip) (Data.parameterChart i.2) piece.native).target,
      ∀ v : Tdata, cT*‖v‖^2 ≤
        ‖incrementsModeAmbientTransverseFrame (actualOriginalOpenParameterSlice Data i z.1)
          (actualOriginalOpenParameterSlice_contMDiff Data hd hs i z.1) (e z.1).symm z.2 v‖^2 := by
  intro z hz v
  let Bp := Data.parameterChart ip
  let Bo := Data.parameterChart i.2
  have hh := (round3ParameterChartPullback_target (Bp.symm.trans Bo) piece.native z).mp hz
  have hp : Bp.symm (Bp (Bo.symm z.1)) = Bo.symm z.1 := Bp.left_inv hh.1.2
  have hb := hNative (Bp (Bo.symm z.1),z.2) hh.2.1 v
  have hBase : actualOriginalOpenParameterSlice Data i z.1 =
      (fun x => Data.F (Bp.symm (Bp (Bo.symm z.1)),x)) := by
    rw [actualOriginalOpenParameterSlice_eq Data i z.1
      (hd.parameter_subset (by rw [hAll]; exact mem_univ _))]
    simp only [hp]
    rfl
  have he : ((e z.1).symm : D → M) = (piece.slices (Bp (Bo.symm z.1))).symm := funext (hSlices z.1)
  simpa only [hBase,he] using hb

structure Round3ParameterOriginalNativeMeanPreparation
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    {Sub : Type*} [Fintype Sub]
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Sub)
      (fun p x => Data.F (p,x)))
    (ell cT : ℝ) (Tinv Forward Meta : ℕ → ℝ) (Rsub Lprimary : ℕ)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) where
  host : Fin Data.primaryCount → Sub → Fin Data.atlas.count
  native : Fin Data.primaryCount → Sub → OpenPartialHomeomorph X X
  slices : Fin Data.primaryCount → Sub → Ep → OpenPartialHomeomorph M D
  data : ∀ nu a, ActualOriginalHostSliceData (Data.atlas.chart (host nu a)) (native nu a)
    (fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) (slices nu a)
  active : ∀ nu a w, w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu a)) (native nu a)).source →
    ((Data.parameterChart i.2).symm w.1,w.2) ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data
  native_open : ∀ nu a, (native nu a).source ⊆ actualOriginalNativeOpen Data (host nu a,i.2)
  same : HEq (actualOriginalPrimaryFamily Data hd hs hn i host native slices data
    (round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart i.2)).eta active)
    (round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart i.2))
  refinement : Round3ParameterRefinementSamples Data i.2 (actualOriginalOpenParameterSlice Data i)
    (actualOriginalPrimaryFamily Data hd hs hn i host native slices data
      (round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart i.2)).eta active)
    host native ((Data.parameterChart i.2).target ×ˢ (univ : Set M)) ell Tinv Forward Meta Rsub Lprimary
  transverse : ∀ nu a z, z ∈ (native nu a).target → ∀ v : Tdata, cT*‖v‖^2 ≤
    ‖incrementsModeAmbientTransverseFrame (actualOriginalOpenParameterSlice Data i z.1)
      (actualOriginalOpenParameterSlice_contMDiff Data hd hs i z.1) (slices nu a z.1).symm z.2 v‖^2

theorem round3Parameter_actual_original_mean_preparation
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs) (hAll : Data.parameterSet = univ)
    (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => Data.F (p,x)))
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
    (ell cT : ℝ) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (hNative : ∀ nu a z, z ∈ (piece nu a).native.target → ∀ v : Tdata, cT*‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame (fun x => Data.F ((Data.parameterChart (ip nu a)).symm z.1,x))
        (hF ((Data.parameterChart (ip nu a)).symm z.1)) ((piece nu a).slices z.1).symm z.2 v‖^2)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) :
    Nonempty (Round3ParameterOriginalNativeMeanPreparation Data hd hs hn
      (round3ParameterOriginalPrimaryFamily Data hd hs hn ip W piece) ell cT Inverse
      (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+2) => Forward k))
      (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+1) => Meta k)) R Data.primaryCount i) := by
  obtain ⟨e,hdata,hactive,hNativeOpen,hSlices,hSame,hRefinement⟩ :=
    round3Parameter_canonical_original_refinement_supply Data hd hs hn hAll ip W piece hInner R hGeometry
      Forward Inverse Meta hProfiles ell hell hell1 i
  exact ⟨{
    host := fun nu a => (piece nu a).host
    native := fun nu a => round3ParameterCrossNativeChart (Data.parameterChart (ip nu a)) (Data.parameterChart i.2) (piece nu a).native
    slices := e
    data := hdata
    active := hactive
    native_open := hNativeOpen
    same := hSame
    refinement := hRefinement
    transverse := fun nu a => round3Parameter_original_cross_transverse_reserve Data hd hs hAll hF
      (ip nu a) i nu (W nu a) (piece nu a) (e nu a) (hSlices nu a) cT (hNative nu a) }⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_original_cross_transverse_reserve
#print axioms GlobalEmbedding.Continuation.round3Parameter_actual_original_mean_preparation
