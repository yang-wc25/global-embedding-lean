import NormalPolar.GlobalWaveResponsePrescribedMeanJoint
import NormalPolar.ActualProbePrescribedLocalPhase
import NormalPolar.ParameterDisplacementPrescribedRaw
import Probes.Round4ActualProbeNativeTensorJointCoordinates
import Probes.Round4ActualProbeBackgroundGeometryLift

/-! Actual source geometry for the complete prescribed wave and its native
mean. These are primitive smoothness and support facts for the real source
solver, not completed-wave or parameter-response estimates. The mean's
joint smoothness is derived from the very same reconstructed amplitudes. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold Filter GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Continuation
variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N r p : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Params" => Fin p → ℝ

structure GlobalWavePrescribedPrimitives
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I:=I) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (W : Set (Ep × M)) (K : Fin r → Set (Ep × M)) : Prop where
  domain_open : IsOpen W
  carrier_closed : ∀ l, IsClosed (Subtype.val ⁻¹' K l : Set W)
  carrier_source : ∀ l, K l ⊆ (a l).source
  chart_smooth : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,X) ∞ (a l) (a l).source
  A_smooth : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c l z.1) z.2) (a l).target
  B_smooth : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c l z.1) z.2) (a l).target
  G_smooth : ∀ l, ContDiffOn ℝ ∞ (fun z : X => freeGramRightInverse (fderiv ℝ (F z.1 ∘ c l z.1) z.2)) (a l).target
  J_smooth : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (normalSpace (I:=I) (F z.1) (c l z.1 z.2)).subtypeL.comp
    (incrementsModeCoordinateJ (F z.1) (hF z.1) (c l z.1) z.2)) (a l).target
  T_smooth : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeTransverseValue (F z.1) (c l z.1) z.2) (a l).target
  BR_smooth : ∀ l, ContDiffOn ℝ ∞ (fun z : X => fun k : Fin (m+1) =>
    (incrementsModeSecondForm (F z.1) (hF z.1) (c l z.1) z.2 0 k : V)) (a l).target
  source_smooth : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (vf l z.1 z.2 : V)) (a l).target
  source_support : ∀ l z, z ∈ (a l).target → z ∈ tsupport (fun w : X => (vf l w.1 w.2 : V)) → (a l).symm z ∈ K l
  phase_smooth : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,ℝ) ∞ (phase l) (W ∩ (a l).source)

theorem globalWave_prescribed_primitives_from_raw
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M) (chi : Fin r → X → ℝ)
    (nu : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I:=I) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (W : Set (Ep × M)) (K : Fin r → Set (Ep × M)) (hW : IsOpen W)
    (n j : ℕ) (ell Mg Bchi Bnu delta tau : ℝ) (weight : Fin r → ℝ)
    (raw : ∀ l, ActualPrescribedSpatialRawProfiles F hF (c l) (chi l) (nu l) (a l) W (K l) n j ell Mg Bchi Bnu)
    (hphase : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,ℝ) ∞ (phase l) (W ∩ (a l).source)) :
    GlobalWavePrescribedPrimitives F hF c
      (fun l => actualProbeNormalAmplitude F (c l) (chi l) (nu l) delta tau (weight l)) phase a W K where
  domain_open := hW
  carrier_closed := fun l => (raw l).closed_support
  carrier_source := fun l => (raw l).support_source
  chart_smooth := fun l => (raw l).chart_smooth
  A_smooth := fun l => (raw l).A_smooth
  B_smooth := fun l => (raw l).B_smooth
  G_smooth := fun l => (raw l).G_smooth
  J_smooth := fun l => (raw l).J_smooth
  T_smooth := fun l => (raw l).T_smooth
  BR_smooth := fun l => (raw l).BR_smooth
  source_smooth := fun l => ((raw l).cutoff_smooth.smul (raw l).normal_smooth).const_smul (-(delta*tau)/(weight l)^2)
  source_support := by
    intro l z hz hs
    apply (raw l).cutoff_support z hz
    exact ((tsupport_smul_subset_right _ _).trans (tsupport_smul_subset_left _ _)) hs
  phase_smooth := hphase

namespace GlobalWavePrescribedPrimitives
variable {F : Ep → M → EuclideanSpace ℝ (Fin N)}
  {hF : ∀ b, ContMDiff I 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F b)}
  {c : Fin r → Ep → EuclideanSpace ℝ (Fin (m+1)) → M}
  {vf : (l : Fin r) → (b : Ep) → (x : EuclideanSpace ℝ (Fin (m+1))) → normalSpace (I:=I) (F b) (c l b x)}
  {phase : Fin r → Ep × M → ℝ}
  {a : Fin r → OpenPartialHomeomorph (Ep × M) (Ep × EuclideanSpace ℝ (Fin (m+1)))}
  {W : Set (Ep × M)} {K : Fin r → Set (Ep × M)}

/-- The actual external probe parameter is a genuine coordinate of the
native mean. The zero-germ argument precedes native spatial differentiation. -/
theorem mean_observed_joint (data : GlobalWavePrescribedPrimitives F hF c vf phase a W K)
    (label : (Fin r × Bool) ↪ Fin p) (tau : ℝ) (length : ℕ)
    (obs : D → M) (O : Set ((Params×Ep)×D)) (hO : IsOpen O)
    (hObs : ContMDiffOn 𝓘(ℝ,(Params×Ep)×D) ((𝓘(ℝ,Params×Ep)).prod I) ∞
      (fun z : (Params×Ep)×D => (z.1,obs z.2)) O)
    (hObsSlice : ∀ z ∈ O, ContMDiffAt 𝓘(ℝ,D) I ∞ obs z.2)
    (hMaps : ∀ z ∈ O, (z.1.2,obs z.2) ∈ W) (v w : D) :
    ContDiffOn ℝ ∞ (fun z : (Params×Ep)×D =>
      round4PrescribedNativeMean label F hF c vf phase tau length a z.1.1 z.1.2 (obs z.2)
        (mfderiv 𝓘(ℝ,D) I obs z.2 ((tangentSpaceCastModel 𝓘(ℝ,D) z.2).symm v))
        (mfderiv 𝓘(ℝ,D) I obs z.2 ((tangentSpaceCastModel 𝓘(ℝ,D) z.2).symm w))) O := by
  let pi : (Params×Ep)×M → Ep×M := fun z => (z.1.2,z.2)
  let U : Set ((Params×Ep)×M) := pi ⁻¹' W
  let KL := fun l => pi ⁻¹' K l
  let primary := fun l => pi ⁻¹' (a l).source
  let amp := fun ch l (z : (Params×Ep)×M) =>
    round4PrescribedGlobalAmplitude ch label l F hF (c l) (vf l) tau length (a l) z.1.1 (pi z)
  have hpi := round4_primary_parameter_projection_smooth (P:=Params) (Ep:=Ep) (I:=I) (M:=M)
  have hU : IsOpen U := data.domain_open.preimage hpi.continuous
  have hReassoc : ContMDiff ((𝓘(ℝ,Params×Ep)).prod I)
      ((𝓘(ℝ,Params)).prod ((𝓘(ℝ,Ep)).prod I)) ∞
      (fun z : (Params×Ep)×M => (z.1.1,(z.1.2,z.2))) :=
    ((contDiff_fst.contMDiff).comp contMDiff_fst).prodMk
      (((contDiff_snd.contMDiff).comp contMDiff_fst).prodMk contMDiff_snd)
  have hamp (ch : Bool) (l : Fin r) : ContMDiffOn ((𝓘(ℝ,Params×Ep)).prod I) 𝓘(ℝ,V) ∞ (amp ch l) U := by
    have hh := round4_prescribed_global_parameter_joint_smooth ch label l F hF (c l) (vf l) tau length (a l)
      W (K l) data.domain_open (data.carrier_closed l) (data.carrier_source l) (data.chart_smooth l)
      (data.A_smooth l) (data.B_smooth l) (data.G_smooth l) (data.J_smooth l) (data.T_smooth l)
      (data.BR_smooth l) (data.source_smooth l) (data.source_support l)
    exact hh.comp hReassoc.contMDiffOn (fun z hz => ⟨mem_univ _,hz⟩)
  have hKL (l : Fin r) : IsClosed (Subtype.val ⁻¹' KL l : Set U) := by
    have hm : Continuous (fun z : U => (⟨pi z,z.property⟩ : W)) :=
      (hpi.continuous.comp continuous_subtype_val).subtype_mk _
    exact (data.carrier_closed l).preimage hm
  have hph (l : Fin r) : ContMDiffOn ((𝓘(ℝ,Params×Ep)).prod I) 𝓘(ℝ,ℝ) ∞
      (phase l ∘ pi) (U ∩ primary l) :=
    (data.phase_smooth l).comp hpi.contMDiffOn (fun z hz => ⟨hz.1,hz.2⟩)
  have hzero (ch : Bool) (l : Fin r) (z : (Params×Ep)×M) (hz : z ∈ U) (hn : z ∉ KL l) :
      amp ch l z = 0 := by
    have hs := (round4_prescribed_global_amplitude_smooth ch label l F hF (c l) (vf l) tau length (a l)
      W (K l) data.domain_open (data.carrier_closed l) (data.carrier_source l) (data.chart_smooth l)
      (data.A_smooth l) (data.B_smooth l) (data.G_smooth l) (data.J_smooth l) (data.T_smooth l)
      (data.BR_smooth l) (data.source_smooth l) (data.source_support l) z.1.1).2
    exact image_eq_zero_of_notMem_tsupport
      (f := fun y : W => round4PrescribedGlobalAmplitude ch label l F hF (c l) (vf l) tau length (a l) z.1.1 y)
      (x := ⟨pi z,hz⟩) (fun h => hn (hs h))
  exact globalWave_native_opposite_mean_local_phase_joint (I:=I) (fun l => phase l ∘ pi) (amp false) (amp true)
    tau U hU KL primary hKL (fun l => (a l).open_source.preimage hpi.continuous)
    (fun l z hz => data.carrier_source l hz) hph (hamp false) (hamp true)
    (fun l z hz hn => ⟨hzero false l z hz hn,hzero true l z hz hn⟩)
    obs O hO hObs hObsSlice hMaps v w

end GlobalWavePrescribedPrimitives
end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.GlobalWavePrescribedPrimitives.mean_observed_joint

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Continuation
variable {m d N r p count : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Params" => Fin p → ℝ
local notation "Z" => Fin (m+1+d) → ℝ
local notation "IM" => 𝓘(ℝ,D)

/-- The unchanged source-first coordinates of the actual prescribed native
mean are jointly smooth. No mean-coordinate smoothness premise is needed. -/
theorem GlobalWavePrescribedPrimitives.mean_original_coordinates
    {F : Ep → M → V} {hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b)}
    {c : Fin r → Ep → D → M}
    {vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I:=IM) (F b) (c l b x)}
    {phase : Fin r → Ep × M → ℝ} {a : Fin r → OpenPartialHomeomorph (Ep × M) (Ep × D)}
    {W : Set (Ep × M)} {K : Fin r → Set (Ep × M)}
    (data : GlobalWavePrescribedPrimitives F hF c vf phase a W K)
    (label : (Fin r × Bool) ↪ Fin p) (tau : ℝ) (length : ℕ)
    (atlas : BufferedAtlas M D) (param : Fin count → OpenPartialHomeomorph Ep Ep)
    (hAtlas : IsSmoothBufferedAtlas atlas) (idx : Fin atlas.count × Fin count)
    (Ocoords : Set (Params×Z)) (Omega : Set ((Params×Ep)×D)) (hOmega : IsOpen Omega)
    (hParam : ContDiffOn ℝ ∞ (param idx.2).symm (param idx.2).target)
    (hOmegaTarget : ∀ z ∈ Omega, z.2 ∈ (atlas.chart idx.1).target)
    (hOmegaMaps : ∀ z ∈ Omega, (z.1.2,(atlas.chart idx.1).symm z.2) ∈ W)
    (hQTarget : ∀ z ∈ Ocoords, incrementsOriginalParameterPoint z.2 ∈ (param idx.2).target)
    (hQMaps : MapsTo (round4OriginalJointObserverPullback param idx.2) Ocoords Omega) :
    ContDiffOn ℝ ∞ (fun z : Params×Z => incrementsOriginalTensorCoordinates atlas param
      (round4PrescribedNativeMean label F hF c vf phase tau length a z.1) idx z.2) Ocoords := by
  have hObs : ContMDiffOn 𝓘(ℝ,(Params×Ep)×D) ((𝓘(ℝ,Params×Ep)).prod IM) ∞
      (fun z : (Params×Ep)×D => (z.1,(atlas.chart idx.1).symm z.2)) Omega :=
    contDiff_fst.contMDiff.contMDiffOn.prodMk
      ((contMDiffOn_symm_of_mem_maximalAtlas (hAtlas.chart_mem idx.1)).comp
        contDiff_snd.contMDiff.contMDiffOn hOmegaTarget)
  have hObsSlice (z : (Params×Ep)×D) (hz : z ∈ Omega) :
      ContMDiffAt 𝓘(ℝ,D) IM ∞ (atlas.chart idx.1).symm z.2 :=
    (contMDiffOn_symm_of_mem_maximalAtlas (hAtlas.chart_mem idx.1)).contMDiffAt
      ((atlas.chart idx.1).open_target.mem_nhds (hOmegaTarget z hz))
  exact round4_native_tensor_joint_original_coordinates atlas param idx
    (round4PrescribedNativeMean label F hF c vf phase tau length a) Ocoords Omega hParam hQTarget hQMaps
    (data.mean_observed_joint label tau length (atlas.chart idx.1).symm Omega hOmega
      hObs hObsSlice hOmegaMaps)

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.GlobalWavePrescribedPrimitives.mean_original_coordinates
