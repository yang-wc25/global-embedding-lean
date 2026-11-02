import Smoothing.Round3OuterReferenceNormalStage
import Probes.ActualOriginalChartImmersion

/-! Positive original reference decomposition covers every physical point
by an actually active cutoff. Genuine stable primary charts therefore give
immersion on the entire new parameter neighborhood, not only on individual
pieces. No current-map immersion premise is introduced. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3_inducedMetric_ne_zero_of_immersion
    (F : M → Ey) (x : M)
    (hImm : Function.Injective (mfderiv 𝓙 𝓘(ℝ,Ey) F x)) :
    inducedMetric (I := 𝓙) F x ≠ 0 := by
  let v : TangentSpace 𝓙 x :=
    (tangentSpaceCastModel 𝓙 x).symm (EuclideanSpace.single (0 : Fin (m+1)) 1)
  have hv : v ≠ 0 := by
    intro hv0
    have hh := congrArg (fun w => (tangentSpaceCastModel 𝓙 x w) (0 : Fin (m+1))) hv0
    simpa [v] using hh
  have hpos := inducedMetric_pos_of_injective_mfderiv F x hImm hv
  intro hz
  rw [hz] at hpos
  simpa using hpos

theorem round3_original_reference_active_cutoff
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data)
    (p : P) (hp : p ∈ Data.parameterOpen) (x : M)
    (hReference : Data.reference p x ≠ 0) :
    ∃ nu : Fin Data.primaryCount, Data.cutoff nu (p,x) ≠ 0 := by
  by_contra! hZero
  have hh := hDecomp.decomposition p hp x
    ⟨Data.reference p x,hDecomp.reference_symmetric p hp x⟩ (hDecomp.reference_mem p hp x)
  have hz : Data.reference p x = 0 := by
    simpa only [incrementsOriginalDecompositionTensor,hZero,zero_mul,zero_pow (by omega : 2 ≠ 0),
      zero_smul,Finset.sum_const_zero] using hh
  exact hReference hz

theorem round3_actual_host_cover_global_immersion
    {A : Type*}
    (F : Ep → M → Ey) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p))
    (host : A → OpenPartialHomeomorph M D)
    (host_smooth : ∀ a, host a ∈ maximalAtlas 𝓙 ∞ M)
    (b : A → OpenPartialHomeomorph X X) (psi : A → Ep × M → ℝ)
    (e : A → Ep → OpenPartialHomeomorph M D)
    (hData : ∀ a, ActualOriginalHostSliceData (host a) (b a) (psi a) (e a))
    (W : Set (Ep × M))
    (hCover : ∀ w ∈ W, ∃ a, w ∈ (actualHostAdaptedChart (host a) (b a)).source)
    (c : ℝ) (hc : 0 < c)
    (hFirst : ∀ a z, z ∈ (b a).target → ∀ v : D,
      c*‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e a z.1).symm) z.2 v‖^2) :
    ∀ w ∈ W, Function.Injective (mfderiv 𝓙 𝓘(ℝ,Ey) (F w.1) w.2) := by
  intro w hw
  obtain ⟨a,ha⟩ := hCover w hw
  let chart := actualHostAdaptedChart (host a) (b a)
  let z := chart w
  have hz : z ∈ (b a).target := by rw [← (hData a).1]; exact chart.map_source ha
  have hg := actual_host_slice_geometry_inputs (host a) (host_smooth a) (b a) (psi a) (e a) (hData a)
  have hi := actual_increment_immersion_of_chart_reserve (F z.1) (hF z.1) (e a z.1)
    ((hData a).2.2.2.2.1 z.1) z.2 (hg.2.2.2.1 z hz).1 c hc (hFirst a z hz)
  rcases hData a with ⟨hat,haa,hai,hforw,he,hes,het,hef,hei,hpair,hadapt,hback,hforward,hbj,hfj⟩
  have hp : z.1 = w.1 := (hforw w ha).1
  have hphysical : (z.1,(e a z.1).symm z.2) = w :=
    (hpair z hz).symm.trans (chart.left_inv ha)
  have hx : (e a z.1).symm z.2 = w.2 := congrArg Prod.snd hphysical
  rw [hx,hp] at hi
  exact hi

#print axioms round3_original_reference_active_cutoff
#print axioms round3_actual_host_cover_global_immersion
end GlobalEmbedding.Continuation
