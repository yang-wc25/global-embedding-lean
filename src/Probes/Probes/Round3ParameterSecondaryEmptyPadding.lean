import Probes.Round3ParameterNativeFamily
import Probes.ActualSecondaryOriginalConstruction

/-! Actual zero padding for varying finite secondary refinements. The empty
chart is an honest open restriction of a given original host chart. Every
padded displacement is literally zero for all scales and polynomial lengths;
no formal dummy source or output budget is substituted. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {P Ep M : Type*} [TopologicalSpace P]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

def round3ParameterSecondaryEmptyChoice (host : OpenPartialHomeomorph M D) :
    Round3ParameterSecondaryChoice P M m where
  host := host
  chart := ((OpenPartialHomeomorph.refl P).prod host).restrOpen ∅ isOpen_empty
  c := fun _ x => host.symm x
  cutoff := 0

@[simp] theorem round3ParameterSecondaryEmptyChoice_source (host : OpenPartialHomeomorph M D) :
    (round3ParameterSecondaryEmptyChoice (P := P) host).chart.source = ∅ := by
  change ((OpenPartialHomeomorph.refl P).prod host).source ∩ ∅ = ∅
  exact inter_empty _

@[simp] theorem round3ParameterSecondaryEmptyChoice_target (host : OpenPartialHomeomorph M D) :
    (round3ParameterSecondaryEmptyChoice (P := P) host).chart.target = ∅ := by
  change ((OpenPartialHomeomorph.refl P).prod host).target ∩
    ((OpenPartialHomeomorph.refl P).prod host).symm ⁻¹' ∅ = ∅
  simp only [preimage_empty,inter_empty]

theorem round3ParameterSecondaryEmptyChoice_preserves (host : OpenPartialHomeomorph M D) :
    Round3ParameterChartPreserves (round3ParameterSecondaryEmptyChoice (P := P) host).chart := by
  intro z hz
  simpa only [round3ParameterSecondaryEmptyChoice_source,mem_empty_iff_false] using hz

@[simp] theorem round3ParameterSecondaryEmptyChoice_native_source
    (B : OpenPartialHomeomorph P Ep) (host : OpenPartialHomeomorph M D) :
    ((round3ParameterSecondaryEmptyChoice host).pullback B).chart.source = ∅ := by
  ext z
  change z ∈ (round3ParameterChartPullback B (round3ParameterSecondaryEmptyChoice host).chart).source ↔ z ∈ (∅ : Set (Ep × M))
  rw [round3ParameterChartPullback_source]
  simp only [round3ParameterSecondaryEmptyChoice_source,mem_empty_iff_false,and_false,false_and]

@[simp] theorem round3ParameterSecondaryEmptyChoice_native_target
    (B : OpenPartialHomeomorph P Ep) (host : OpenPartialHomeomorph M D) :
    ((round3ParameterSecondaryEmptyChoice host).pullback B).chart.target = ∅ := by
  ext z
  change z ∈ (round3ParameterChartPullback B (round3ParameterSecondaryEmptyChoice host).chart).target ↔ z ∈ (∅ : Set (Ep × D))
  rw [round3ParameterChartPullback_target]
  simp only [round3ParameterSecondaryEmptyChoice_target,mem_empty_iff_false,and_false,false_and]

def round3ParameterSecondaryEmptyNativeRawGeometry
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (n j : ℕ) (ell Mg : ℝ) (W : Set (Ep × M))
    (B : OpenPartialHomeomorph P Ep)
    (host : OpenPartialHomeomorph M D) (hhost : host ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (phase : Ep × M → ℝ) : ActualSecondaryRawGeometry F hF n j ell Mg W where
  c := fun _ x => host.symm x
  chart := ((round3ParameterSecondaryEmptyChoice host).pullback B).chart
  sample := ∅
  sample_subset := empty_subset _
  support := ∅
  support_closed := by simp only [preimage_empty]; exact isClosed_empty
  support_source := empty_subset _
  source_domain := by rw [round3ParameterSecondaryEmptyChoice_native_source]; exact empty_subset W
  chart_smooth := by rw [round3ParameterSecondaryEmptyChoice_native_source]; exact contMDiffOn_empty
  inverse := by intro z hz; exact (by simpa only [round3ParameterSecondaryEmptyChoice_native_target,mem_empty_iff_false] using hz : False).elim
  phase := phase
  phase_smooth := by rw [round3ParameterSecondaryEmptyChoice_native_source]; exact contMDiffOn_empty
  adaptation := by intro z hz; exact (by simpa only [round3ParameterSecondaryEmptyChoice_native_source,mem_empty_iff_false] using hz : False).elim
  brows_smooth := by rw [round3ParameterSecondaryEmptyChoice_native_target]; exact contDiffOn_empty
  inverse_smooth := by rw [round3ParameterSecondaryEmptyChoice_native_target]; exact contDiffOn_empty
  transverse_smooth := by rw [round3ParameterSecondaryEmptyChoice_native_target]; exact contDiffOn_empty
  value_smooth := by rw [round3ParameterSecondaryEmptyChoice_native_target]; exact contDiffOn_empty
  coefficientA_smooth := by rw [round3ParameterSecondaryEmptyChoice_native_target]; exact contDiffOn_empty
  coefficientB_smooth := by rw [round3ParameterSecondaryEmptyChoice_native_target]; exact contDiffOn_empty
  brows_bound := fun _ _ _ hz => hz.elim
  transverse_bound := fun _ _ _ hz => hz.elim
  inverse_bound := fun _ _ _ hz => hz.elim
  value_bound := fun _ _ _ hz => hz.elim
  coefficientA_bound := fun _ _ _ hz => hz.elim
  coefficientB_bound := fun _ _ _ hz => hz.elim
  spatialChart := fun _ => host
  coordinate := rfl
  maximal := fun _ => hhost
  target := by intro z hz; exact (by simpa only [round3ParameterSecondaryEmptyChoice_native_target,mem_empty_iff_false] using hz : False).elim
  immersion := by intro z hz; exact (by simpa only [round3ParameterSecondaryEmptyChoice_native_target,mem_empty_iff_false] using hz : False).elim
  gram := by intro z hz; exact (by simpa only [round3ParameterSecondaryEmptyChoice_native_target,mem_empty_iff_false] using hz : False).elim

variable {Label SubPrimary : Type*} [Fintype Label] [DecidableEq Label] [Fintype SubPrimary]

theorem round3Parameter_secondary_empty_piece
    (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (length : ℕ) (tau delta : ℝ) (r : (Label × Label) × Fin 4)
    (host : OpenPartialHomeomorph M D) :
    round3ParameterSecondaryPiece F hF g input length tau delta r (round3ParameterSecondaryEmptyChoice host) = 0 := by
  funext y
  simp only [round3ParameterSecondaryPiece,round3ParameterSupportedWave,
    round3ParameterSecondaryEmptyChoice_source,mem_empty_iff_false,ite_false,Pi.zero_apply,smul_zero,sub_self]

theorem round3Parameter_secondary_empty_native_piece
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (input : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (length : ℕ) (tau delta : ℝ) (r : (Label × Label) × Fin 4)
    (B : OpenPartialHomeomorph P Ep) (host : OpenPartialHomeomorph M D) :
    actualOriginalSecondaryPiece F hF g input length tau delta r
      ((round3ParameterSecondaryEmptyChoice host).pullback B).toNative = 0 := by
  funext y
  simp only [actualOriginalSecondaryPiece,actualSecondarySupportedWave,
    Round3ParameterSecondaryChoice.toNative,round3ParameterSecondaryEmptyChoice_native_source,
    mem_empty_iff_false,ite_false,Pi.zero_apply,smul_zero,sub_self]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3ParameterSecondaryEmptyNativeRawGeometry
#print axioms GlobalEmbedding.Continuation.round3Parameter_secondary_empty_piece
#print axioms GlobalEmbedding.Continuation.round3Parameter_secondary_empty_native_piece
