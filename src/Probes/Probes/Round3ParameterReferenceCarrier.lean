import Probes.Round3ParameterStablePrimaryTarget
import Smoothing.Round3OuterC2NativeJets
import Probes.ActualIncrementFreeNormalKernel
import Probes.ActualIncrementOriginalSampling

/-! Fixed actual reference pieces on every parameter chart are sampled in
the original norm.  The old unit normal and beta kernel are derived from
the original free-normal assumptions, without an identity parameter chart. -/

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

theorem round3Parameter_reference_carrier_sampling
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref)
    (ip : Fin Ref.parameterCount) (nu : Fin Ref.primaryCount) (W : Set (Ep × M))
    (piece : Round3PreparedPrimaryPiece Ref ip nu W)
    (hK : Ref.parameterSet = univ)
    (hInner : ∀ y ∈ tsupport piece.cutoff, y.2 ∈ Ref.atlas.inner piece.host)
    (hParam : ∀ y ∈ tsupport piece.cutoff, y.1 ∈ Ref.parameterNormDomain ip)
    (y : Ep × M) (hy : y ∈ tsupport piece.cutoff) :
    let z := actualHostAdaptedChart (Ref.atlas.chart piece.host) piece.native y
    parameterTensorModelEquiv (m+1) d
      (round3OriginalAdaptedTransition Ref.atlas piece.host piece.slices z) ∈
        incrementsOriginalEvaluation Ref.atlas Ref.parameterChart
          Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet (piece.host,ip) := by
  intro z
  let a := actualHostAdaptedChart (Ref.atlas.chart piece.host) piece.native
  have hys := piece.support hy
  have hz : z ∈ piece.native.target := by
    rw [← piece.data.1]
    exact a.map_source hys
  rcases piece.data with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hphase,hback,hforward,hbj,hfj⟩
  have hzp : z.1 = y.1 := (hforw y hys).1
  have hpx : (piece.slices z.1).symm z.2 = y.2 := by
    have hh := a.left_inv hys
    rw [hpair z hz] at hh
    exact congrArg Prod.snd hh
  apply (actual_original_native_evaluation_iff Ref hd (piece.host,ip) _).mpr
  refine ⟨?_,?_,?_⟩
  · change Ref.atlas.chart piece.host ((piece.slices z.1).symm z.2) ∈ Ref.sourceNormDomain piece.host
    rw [hpx]
    exact hd.source_inner_norm piece.host y.2 (hInner y hy)
  · change z.1 ∈ Ref.parameterNormDomain ip
    rw [hzp]
    exact hParam y hy
  · change (Ref.parameterChart ip).symm z.1 ∈ Ref.parameterSet
    rw [hK]
    exact mem_univ _

theorem round3Parameter_reference_primary_normal
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (hn : IncrementsOriginalFreeNormalConditions Ref hd hs)
    (ip : Fin Ref.parameterCount) (nu : Fin Ref.primaryCount) (W : Set (Ep × M))
    (piece : Round3PreparedPrimaryPiece Ref ip nu W)
    (z : X) (hz : z ∈ piece.native.target)
    (hF0 : ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => Ref.F ((Ref.parameterChart ip).symm z.1,x))) :
    let p := (Ref.parameterChart ip).symm z.1
    ∃ normal : normalSpace (I := 𝓙) (fun x => Ref.F (p,x)) ((piece.slices z.1).symm z.2),
      (normal : Ey) = Ref.freeNormal nu (p,(piece.slices z.1).symm z.2) ∧ ‖normal‖ = 1 ∧
      incrementsTransversePairing (fun x => Ref.F (p,x)) hF0 ((piece.slices z.1).symm z.2)
        (fun a : Fin m => incrementsModeCoordinateDirections (piece.slices z.1).symm z.2 a.succ) normal = 0 := by
  intro p
  have hs0 := actual_host_slice_source_point (Ref.atlas.chart piece.host) piece.native _ piece.slices piece.data z hz
  have hact := piece.active _ hs0
  rcases piece.data with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hphase,hback,hforward,hbj,hfj⟩
  have hmap (x : D) (hx : x ∈ (piece.slices z.1).target) :
      (p,(piece.slices z.1).symm x) ∈ Ref.primaryDomain nu := by
    have htx : (z.1,x) ∈ piece.native.target := by simpa only [het,mem_setOf_eq] using hx
    exact (piece.active _ (actual_host_slice_source_point (Ref.atlas.chart piece.host)
      piece.native _ piece.slices piece.data (z.1,x) htx)).1
  have hAdapt (x : D) (hx : x ∈ (piece.slices z.1).target) :
      Ref.phase nu (p,(piece.slices z.1).symm x) = x 0 := by
    exact hphase (z.1,x) (by simpa only [het,mem_setOf_eq] using hx)
  have hzt : z.2 ∈ (piece.slices z.1).target := by simpa only [het,mem_setOf_eq] using hz
  let normal : normalSpace (I := 𝓙) (fun x => Ref.F (p,x)) ((piece.slices z.1).symm z.2) :=
    ⟨Ref.freeNormal nu (p,(piece.slices z.1).symm z.2),
      hn.normal nu (p,(piece.slices z.1).symm z.2) hact⟩
  refine ⟨normal,rfl,?_,?_⟩
  · exact hn.unit nu (p,(piece.slices z.1).symm z.2) hact
  · exact actual_original_free_normal_transverse_kernel Ref hd hs hn nu p hact.2.1
      (piece.slices z.1) (he z.1) (piece.slices z.1).target (piece.slices z.1).open_target
      subset_rfl hmap hAdapt z.2 hzt

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_reference_carrier_sampling
#print axioms GlobalEmbedding.Continuation.round3Parameter_reference_primary_normal
