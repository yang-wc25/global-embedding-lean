import Probes.Round3ParameterAfterNormalFamily
import Probes.Round3ParameterActualHostRestriction
import Probes.Round3ParameterMeanPreparationOfFields
import Smoothing.Round3ParameterNativeRestriction
import Smoothing.Round3OuterParameterFixedCarrier

/-! The actual normal stage feeds the same fixed-carrier mean family.
The native host charts are genuinely restricted and their phase-adapted
slices reconstructed. All forward and inverse functions stay unchanged.
No new cutoff, current-map profile maximum, or parameter shrink is chosen. -/

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

theorem round3Parameter_fixed_carrier_after_normal_mean_preparation
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hdRef : IncrementsOriginalDomainConditions Ref)
    {Sub : Type*} [Fintype Sub]
    (g0 : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Ref.primaryCount) (Β := Sub)
      (fun p x => Ref.F (p,x)))
    (R : ℕ) (geom : Round3ParameterOriginalPrimaryGeometry Ref g0 R)
    (hOpen : ∀ nu, IsOpen (round3FixedCarrierDomain (g0.eta nu)))
    (Forward Inverse Meta : ℕ → ℝ)
    (hProfiles : Round3ParameterOriginalChartProfiles Ref
      (round3ParameterFixedCarrierFamily Ref g0 hOpen) Forward Inverse Meta)
    (F : P × M → Ey)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (normal : Fin Ref.primaryCount → P × M → Ey)
    (neighborhood : (p : P) → (x : M) → Set {A : LinearMap.BilinForm ℝ (TangentSpace 𝓙 x) // A.IsSymm}) :
    let domain := fun nu => round3FixedCarrierDomain (g0.eta nu)
    let Data := round3ParameterStageData Ref F H Ref.parameterOpen normal domain neighborhood
    let gFixed := round3ParameterFixedCarrierFamily Ref g0 hOpen
    ∀ (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs) (hAll : Data.parameterSet = univ)
    (ell cT : ℝ) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (host : Fin Ref.primaryCount → Fin Ref.parameterCount → Sub → Fin Ref.atlas.count)
    (b : Fin Ref.primaryCount → Fin Ref.parameterCount → Sub → OpenPartialHomeomorph X X)
    (e : Fin Ref.primaryCount → Fin Ref.parameterCount → Sub → Ep → OpenPartialHomeomorph M D)
    (hdata : ∀ nu ip a, ActualOriginalHostSliceData (Ref.atlas.chart (host nu ip a)) (b nu ip a)
      (fun z : Ep × M => Ref.phase nu ((Ref.parameterChart ip).symm z.1,z.2)) (e nu ip a))
    (hNative : ∀ nu ip a, (b nu ip a).source ⊆ actualOriginalNativeOpen Data (host nu ip a,ip))
    (hInner : ∀ nu ip a w, w ∈ (actualHostAdaptedChart (Ref.atlas.chart (host nu ip a)) (b nu ip a)).source →
      w.2 ∈ Ref.atlas.inner (host nu ip a))
    (hChart : ∀ nu ip a, actualHostAdaptedChart (Ref.atlas.chart (host nu ip a)) (b nu ip a) =
      (round3ParameterNativePrimary (fun p x => Ref.F (p,x)) g0 (Ref.parameterChart ip)).chart nu a)
    (hInverse : ∀ nu ip a p x, (e nu ip a p).symm x = g0.inverse nu a ((Ref.parameterChart ip).symm p) x)
    (hTransverse : ∀ (i : Fin Ref.atlas.count × Fin Ref.parameterCount) nu a z,
      z ∈ (b nu i.2 a).target → ∀ v : Tdata, cT*‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame (actualOriginalOpenParameterSlice Data i z.1)
        (actualOriginalOpenParameterSlice_contMDiff Data hd hs i z.1) (e nu i.2 a z.1).symm z.2 v‖^2),
    ∃ hActive : ∀ nu a z, z ∈ (gFixed.chart nu a).target →
      (z.1,gFixed.inverse nu a z.1 z.2) ∈ domain nu ∩ incrementsOriginalParameterRegion Data,
    let g := round3ParameterAfterNormalFamily Ref gFixed F H Ref.parameterOpen normal domain neighborhood hd hs hn hActive
    Round3ParameterOriginalPrimaryGeometry Data g R ∧
      Round3ParameterOriginalChartProfiles Data g Forward Inverse Meta ∧
      g.eta = gFixed.eta ∧ g.chart = gFixed.chart ∧ g.inverse = g0.inverse ∧
      ∀ i, Nonempty (Round3ParameterOriginalNativeMeanPreparation Data hd hs hn g ell cT Inverse
        (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+2) => Forward k))
        (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+1) => Meta k)) R Data.primaryCount i) := by
  intro domain Data gFixed hd hs hn hAll ell cT hell hell1 host b e hdata hNative hInner hChart hInverse hTransverse
  obtain ⟨hOpen0,hCover,hSub,hEffective,hGeom,hFwd,hInv,hInvEq,hSupport⟩ :=
    round3_parameter_original_fixed_carrier Ref g0 R geom
  have hGeomFixed : Round3ParameterOriginalPrimaryGeometry
      {Ref with primaryDomain := domain} gFixed R := hGeom
  have hGeomOld : Round3ParameterOriginalPrimaryGeometry Ref gFixed R := {
    hGeomFixed with
    inverse_active := fun nu a z hz =>
      ⟨(hSub nu (hGeomFixed.inverse_active nu a z hz).1).1,(hGeomFixed.inverse_active nu a z hz).2⟩ }
  have hActive : ∀ nu a z, z ∈ (gFixed.chart nu a).target →
      (z.1,gFixed.inverse nu a z.1 z.2) ∈ domain nu ∩ incrementsOriginalParameterRegion Data :=
    hGeomFixed.inverse_active
  let g := round3ParameterAfterNormalFamily Ref gFixed F H Ref.parameterOpen normal domain neighborhood hd hs hn hActive
  have hOut := round3Parameter_after_normal_geometry_and_profiles Ref hdRef gFixed R hGeomOld
    Forward Inverse Meta hProfiles F H Ref.parameterOpen normal domain neighborhood hd hs hn hActive
  refine ⟨hActive,hOut.1,hOut.2.1,rfl,rfl,rfl,?_⟩
  intro i
  let B := Ref.parameterChart i.2
  let G := fun nu => round3ParameterNativeDomain (M := M) B (domain nu)
  have hG (nu) : IsOpen (G nu) := round3Parameter_nativeDomain_open B (domain nu) (hOpen nu)
  have hChoose (nu) (a) := round3Parameter_actual_host_source_restriction
    (Ref.atlas.chart (host nu i.2 a)) (hdRef.atlas_smooth.chart_mem (host nu i.2 a))
    (b nu i.2 a) _ (e nu i.2 a) (hdata nu i.2 a) (G nu) (hG nu)
  choose bNew eNew hDataNew hForwardNew hInverseNew hSliceNew hSourceNew hTargetNew hChartNew hCarrierNew using hChoose
  have hFullChart (nu) (a) : actualHostAdaptedChart (Ref.atlas.chart (host nu i.2 a)) (bNew nu a) =
      (round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart i.2)).chart nu a := by
    rw [hChartNew nu a,hChart nu i.2 a]
    exact (round3Parameter_chart_restriction_commutes B (g0.chart nu a) (domain nu) (hOpen nu)).symm
  have hNewActive (nu) (a) (w : Ep × M)
      (hw : w ∈ (actualHostAdaptedChart (Ref.atlas.chart (host nu i.2 a)) (bNew nu a)).source) :
      ((Data.parameterChart i.2).symm w.1,w.2) ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data := by
    have hh := hCarrierNew nu a w hw
    have hOld : w ∈ (actualHostAdaptedChart (Ref.atlas.chart (host nu i.2 a)) (b nu i.2 a)).source := by
      rw [hChartNew nu a] at hw
      exact hw.1
    have hPhysical : ((B.symm w.1,w.2) : P × M) ∈ (g0.chart nu a).source := by
      rw [hChart nu i.2 a] at hOld
      exact ((round3ParameterChartPullback_source_iff B (g0.chart nu a)
        (geom.preserves nu a) w hh.1).mp hOld)
    have hRegion := (geom.inverse_active nu a _ ((g0.chart nu a).map_source hPhysical)).2
    have hPoint : ((g0.chart nu a (B.symm w.1,w.2)).1,
        g0.inverse nu a (g0.chart nu a (B.symm w.1,w.2)).1 (g0.chart nu a (B.symm w.1,w.2)).2) =
        (B.symm w.1,w.2) := by
      rw [← geom.inverse nu a _ ((g0.chart nu a).map_source hPhysical),
        (g0.chart nu a).left_inv hPhysical]
    rw [hPoint] at hRegion
    exact ⟨hh.2,hRegion⟩
  have hInnerNew (nu : Fin Ref.primaryCount) (a : Sub) (w : Ep × M)
      (hw : w ∈ (actualHostAdaptedChart (Ref.atlas.chart (host nu i.2 a)) (bNew nu a)).source) :
      w.2 ∈ Ref.atlas.inner (host nu i.2 a) := by
    apply hInner nu i.2 a w
    rw [hChartNew nu a] at hw
    exact hw.1
  apply round3Parameter_actual_mean_preparation_of_global_fields Data hd hs hn hAll g R hOut.1
    Forward Inverse Meta hOut.2.1 ell cT hell hell1 i (fun nu a => host nu i.2 a) bNew eNew hDataNew
    hNewActive (fun nu a => (hNative nu i.2 a).trans' (hSourceNew nu a))
    hInnerNew hFullChart (fun nu a p x => (congrFun (hSliceNew nu a p) x).trans (hInverse nu i.2 a p x))
  intro nu a z hz v
  rw [hSliceNew nu a z.1]
  exact hTransverse i nu a z (hTargetNew nu a hz) v

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_fixed_carrier_after_normal_mean_preparation
