import Probes.Round3PreparedActualStableTarget
import Probes.Round3PreparedParameterCarrierRestriction
import Probes.Round3PreparedPrimaryPiece
import Probes.ActualOriginalHostTargetRestriction
import Probes.ActualIncrementOriginalPrimitiveBinding

/-! Fixed primary functions acquire stage-dependent stable domains from
pointwise control on the original compact parameter set. All chart functions,
inverse functions, slice inverse functions and cutoff functions are retained.
Only the open domains shrink, and every numerical reserve loses a fixed factor.
This removes the need to control the perturbation on the outer beta support. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Vtarget" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
local notation "𝓙" => 𝓘(ℝ,D)
private local instance domainsFirstNormed : NormedAddCommGroup (D →L[ℝ] Vtarget) := inferInstance
private local instance domainsFirstSpace : NormedSpace ℝ (D →L[ℝ] Vtarget) := inferInstance
private local instance domainsFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] Vtarget) := inferInstance
private local instance domainsFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] Vtarget) := inferInstance

theorem round3_prepared_primary_stable_domains
    {Β : Type*} [Fintype Β]
    (Data : IncrementsOriginalNativeData (m+1) d N M Ep)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (ip : Fin Data.parameterCount) (hId : Data.parameterChart ip = OpenPartialHomeomorph.refl Ep)
    (W : Set (Ep × M))
    (piece : ∀ nu : Fin Data.primaryCount, Β → Round3PreparedPrimaryPiece Data ip nu W)
    (K V0 : Set Ep) (hV0 : IsOpen V0) (hKV0 : K ⊆ V0)
    (F : Ep → M → Vtarget) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Vtarget) ∞ (F p))
    (hJoint : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Vtarget) ∞ (Function.uncurry F) W)
    (cF cT mu : ℝ) (hcF : 0 < cF) (hcT : 0 < cT) (hmu : 0 < mu)
    (hPointwise : ∀ nu a y, y ∈ tsupport (piece nu a).cutoff → y.1 ∈ K →
      let z := actualHostAdaptedChart (Data.atlas.chart (piece nu a).host) (piece nu a).native y
      let e := (piece nu a).slices
      (∀ v : D, cF*‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2 v‖^2) ∧
      (∀ v : Tdata, cT*‖v‖^2 ≤
        ‖incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e z.1).symm z.2 v‖^2) ∧
      mu ≤ ‖actualFreeNormalProjectionRaw
        (fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2)
        (incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e z.1).symm z.2)
        (Data.freeNormal nu ((Data.parameterChart ip).symm z.1,(e z.1).symm z.2))‖) :
    ∃ V : Set Ep, IsOpen V ∧ K ⊆ V ∧ V ⊆ V0 ∧
    ∃ (b : Fin Data.primaryCount → Β → OpenPartialHomeomorph X X)
      (e : Fin Data.primaryCount → Β → Ep → OpenPartialHomeomorph M D),
      (∀ nu a, (b nu a : X → X) = (piece nu a).native) ∧
      (∀ nu a, ((b nu a).symm : X → X) = (piece nu a).native.symm) ∧
      (∀ nu a p, ((e nu a p).symm : D → M) = ((piece nu a).slices p).symm) ∧
      (∀ nu a, (b nu a).source ⊆ (piece nu a).native.source) ∧
      (∀ nu a, ActualOriginalHostSliceData (Data.atlas.chart (piece nu a).host) (b nu a)
        (fun z : Ep × M => Data.phase nu ((Data.parameterChart ip).symm z.1,z.2)) (e nu a)) ∧
      (∀ nu a, incrementsGlobalRelativeSupport (V ×ˢ (univ : Set M)) (piece nu a).cutoff ⊆
        (actualHostAdaptedChart (Data.atlas.chart (piece nu a).host) (b nu a)).source) ∧
      (∀ nu a w, w ∈ (actualHostAdaptedChart (Data.atlas.chart (piece nu a).host) (b nu a)).source →
        ((Data.parameterChart ip).symm w.1,w.2) ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data) ∧
      (∀ nu a z, z ∈ (b nu a).target → ∀ v : D,
        (cF/4)*‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e nu a z.1).symm) z.2 v‖^2) ∧
      (∀ nu a z, z ∈ (b nu a).target → ∀ v : Tdata,
        (cT/4)*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame
          (F z.1) (hF z.1) (e nu a z.1).symm z.2 v‖^2) ∧
      ∀ nu a z, z ∈ (b nu a).target → mu/2 ≤ ‖actualFreeNormalProjectionRaw
        (fderiv ℝ (F z.1 ∘ (e nu a z.1).symm) z.2)
        (incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e nu a z.1).symm z.2)
        (Data.freeNormal nu ((Data.parameterChart ip).symm z.1,(e nu a z.1).symm z.2))‖ := by
  let chart := fun nu a => actualHostAdaptedChart (Data.atlas.chart (piece nu a).host) (piece nu a).native
  let KT := fun nu a => chart nu a '' ((K ×ˢ (univ : Set M)) ∩ tsupport (piece nu a).cutoff)
  have hKT (nu : Fin Data.primaryCount) (a : Β) : KT nu a ⊆ (piece nu a).native.target := by
    rintro _ ⟨y,hy,rfl⟩
    rw [← (piece nu a).data.1]
    exact (chart nu a).map_source ((piece nu a).support hy.2)
  have hNativeJoint (nu : Fin Data.primaryCount) (a : Β) :
      ContDiffOn ℝ ∞ (fun z : X => F z.1 (((piece nu a).slices z.1).symm z.2))
        (piece nu a).native.target := by
    rcases (piece nu a).data with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hadapt,hback,hforward,hbj,hfj⟩
    have hh := (hJoint.comp (hai.mono (by rw [hat]))
      (fun z (hz : z ∈ (piece nu a).native.target) =>
        (piece nu a).source_domain ((chart nu a).map_target (by rwa [hat])))).contDiffOn
    apply hh.congr
    intro z hz
    change F z.1 (((piece nu a).slices z.1).symm z.2) =
      F ((chart nu a).symm z).1 ((chart nu a).symm z).2
    rw [hpair z hz]
  let normal := fun nu a (z : X) => Data.freeNormal nu
    ((Data.parameterChart ip).symm z.1,((piece nu a).slices z.1).symm z.2)
  have hNativeNormal (nu : Fin Data.primaryCount) (a : Β) :
      ContDiffOn ℝ ∞ (normal nu a) (piece nu a).native.target := by
    rcases (piece nu a).data with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hadapt,hback,hforward,hbj,hfj⟩
    have hh := actual_original_parameter_pullback_smooth Data hd ip (Data.freeNormal nu)
      (Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data) (hs.normal_joint nu)
      (chart nu a).source (by intro z hz; rw [hId]; exact Set.mem_univ _) (piece nu a).active
    have hc := (hh.comp (hai.mono (by rw [hat]))
      (fun z (hz : z ∈ (piece nu a).native.target) => (chart nu a).map_target (by rwa [hat]))).contDiffOn
    apply hc.congr
    intro z hz
    change Data.freeNormal nu ((Data.parameterChart ip).symm z.1,((piece nu a).slices z.1).symm z.2) =
      Data.freeNormal nu ((Data.parameterChart ip).symm ((chart nu a).symm z).1,((chart nu a).symm z).2)
    rw [hpair z hz]
  have hLocal (nu : Fin Data.primaryCount) (a : Β) :=
    round3_prepared_actual_stable_target (Data.atlas.chart (piece nu a).host)
      (hd.atlas_smooth.chart_mem (piece nu a).host) (piece nu a).native
      (fun z : Ep × M => Data.phase nu ((Data.parameterChart ip).symm z.1,z.2))
      (piece nu a).slices (piece nu a).data F hF (hNativeJoint nu a)
      (normal nu a) (hNativeNormal nu a) (KT nu a) (hKT nu a) cF cT mu hcF hcT hmu
      (by rintro z ⟨y,hy,rfl⟩; exact (hPointwise nu a y hy.2 hy.1.1).1)
      (by rintro z ⟨y,hy,rfl⟩; exact (hPointwise nu a y hy.2 hy.1.1).2.1)
      (by rintro z ⟨y,hy,rfl⟩; exact (hPointwise nu a y hy.2 hy.1.1).2.2)
  choose O hO hKO hOt hFirst hFrame hNormal hImm hRaw using hLocal
  let good := fun a : Fin Data.primaryCount × Β =>
    (chart a.1 a.2).source ∩ (chart a.1 a.2) ⁻¹' O a.1 a.2
  have hGood (a : Fin Data.primaryCount × Β) : IsOpen (good a) :=
    (chart a.1 a.2).continuousOn.isOpen_inter_preimage (chart a.1 a.2).open_source (hO a.1 a.2)
  obtain ⟨V,hV,hKV,hVV0,hCarrier⟩ := round3_prepared_compact_carrier_parameter_neighborhood K V0 hV0 hKV0
    (fun a : Fin Data.primaryCount × Β => tsupport (piece a.1 a.2).cutoff) good
    (fun a => (piece a.1 a.2).compact) hGood
    (by intro a p hp x hx; exact ⟨(piece a.1 a.2).support hx,hKO a.1 a.2 ⟨(p,x),⟨⟨hp,mem_univ _⟩,hx⟩,rfl⟩⟩)
  have hRestricted (nu : Fin Data.primaryCount) (a : Β) :=
    actual_original_host_restrict_target (Data.atlas.chart (piece nu a).host)
      (hd.atlas_smooth.chart_mem (piece nu a).host) (piece nu a).native
      (fun z : Ep × M => Data.phase nu ((Data.parameterChart ip).symm z.1,z.2))
      (piece nu a).slices (piece nu a).data (O nu a) (hO nu a) (hOt nu a)
  choose b e hTarget hSource hb hbi hData hAdaptedSource hSlices using hRestricted
  refine ⟨V,hV,hKV,hVV0,b,e,hb,hbi,hSlices,hSource,hData,?_,?_,?_,?_,?_⟩
  · intro nu a y hy
    rw [parameterRound2_global_relativeSupport_eq _ (hV.prod isOpen_univ)] at hy
    rw [hAdaptedSource]
    exact hCarrier (nu,a) hy
  · intro nu a w hw
    rw [hAdaptedSource] at hw
    exact (piece nu a).active w hw.1
  · intro nu a z hz
    rw [hSlices]
    exact hFirst nu a z (by rwa [hTarget] at hz)
  · intro nu a z hz
    rw [hSlices]
    exact hFrame nu a z (by rwa [hTarget] at hz)
  · intro nu a z hz
    rw [hSlices]
    exact hNormal nu a z (by rwa [hTarget] at hz)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_primary_stable_domains
