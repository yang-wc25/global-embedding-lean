import NormalPolar.NativeProbeProvider

/-!
# The empty-source branch of the complete native probe provider

The original source need not be nonempty. For an empty source, every field
of the native probe interface is constructed on the literal reference map.
The construction below works on any given smooth compact atlas and keeps
every given legal wave. Its original coordinate norms vanish because their
actual sampling sets are empty, without changing the atlas or any norm.

The final provider merely chooses an empty atlas internally. This removes
the need to choose a source point or a base chart in the nonempty analytic
construction. No assertion about the remaining nonempty case is made here.
-/

noncomputable section
open Set Filter Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.Main
open GlobalEmbedding.NormalPolar GlobalEmbedding.Upgrade

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [IsEmpty M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,E)

/-- The unchanged original atlas gauge is zero on an empty source, even
when its chart index type is nonempty. It is the evaluation set, not the
totalized coordinate map off its chart, that makes the supremum empty. -/
theorem probeAtlasCj_eq_zero_of_isEmpty
    (A : BufferedAtlas M E) (j : ℕ) (f : M → V) :
    probeAtlasCj A j f = 0 := by
  unfold probeAtlasCj paperAtlasCj paperCoordinateCj
  apply le_antisymm
  · refine iSup_le fun i => iSup_le fun l => iSup_le fun x => ?_
    obtain ⟨y,hy,_⟩ := x.property
    obtain ⟨z,_,_⟩ := hy
    exact isEmptyElim z
  · exact bot_le

/-- Genuine native data on the same reference map, arbitrary given atlas,
and arbitrary given finite wave family. The actual C² reserve is zero. -/
def nativeProbeData_of_isEmpty
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ,V) ∞ F₀)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F₀ x))
    {r : ℕ} (waves : Fin r → LocalLegalWave F₀ hF₀) :
    NativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves where
  radius := 1
  radius_pos := zero_lt_one
  threshold := 1
  threshold_pos := zero_lt_one
  map := fun _ _ => F₀
  slice_smooth := fun _ _ => hF₀
  immersion := fun _ _ => hi₀
  joint_smooth := by
    intro t ht htt z hz
    exact isEmptyElim z.2
  metric := by
    intro t ht htt u hu x
    rfl
  weight := fun _ => 1
  weight_pos := fun _ => zero_lt_one
  distinct_on_overlap := by
    intro l k hlk hoverlap
    exact isEmptyElim hoverlap.choose
  constant := 0
  constant_nonneg := le_rfl
  etaH := fun _ => 0
  etaV := fun _ => 0
  etaH_nonneg := fun _ => le_rfl
  etaV_nonneg := fun _ => le_rfl
  etaH_tendsto := tendsto_const_nhds
  etaV_tendsto := tendsto_const_nhds
  closeness := by
    intro t ht htt u hu
    rw [probeAtlasCj_eq_zero_of_isEmpty]
    exact bot_le
  spatial_C3 := by
    intro t ht htt u hu
    rw [probeAtlasCj_eq_zero_of_isEmpty]
    exact bot_le
  parameter_C1 := by
    intro t ht htt u hu d
    rw [probeAtlasCj_eq_zero_of_isEmpty]
    exact bot_le
  parameter_C2 := by
    intro t ht htt u hu d
    rw [probeAtlasCj_eq_zero_of_isEmpty]
    exact bot_le
  native_hessian_response := by
    intro t ht htt u hu l b i x hx
    exact isEmptyElim x
  value_response := by
    intro t ht htt u hu l b x
    exact isEmptyElim x
  reserve := 0
  reserve_lt_one := zero_lt_one
  closeness_reserve := by
    intro t ht htt
    refine ⟨0,le_rfl,?_,?_⟩
    · intro u hu
      rw [probeAtlasCj_eq_zero_of_isEmpty]
      exact bot_le
    · simp only [mul_zero,le_refl]

/-- A genuine empty atlas with a positive buffer, as allowed by the
original atlas definition. -/
def emptyNativeProbeAtlas : BufferedAtlas M E where
  count := 0
  chart := Fin.elim0
  inner := Fin.elim0
  inner_open := fun i => Fin.elim0 i
  inner_subset := fun i => Fin.elim0 i
  cover := fun x => isEmptyElim x
  buffer := 1
  buffer_pos := zero_lt_one
  buffered := fun i => Fin.elim0 i
  support := Fin.elim0

theorem emptyNativeProbeAtlas_smooth :
    IsSmoothBufferedAtlas (emptyNativeProbeAtlas (n := n) (M := M)) := by
  constructor <;> intro i <;> exact Fin.elim0 i

/-- The complete native provider is unconditional in the empty-source
branch, with no dimension restriction and no nonempty-wave assumption. -/
theorem nativeUpgradeProbeProvider_of_isEmpty :
    NativeUpgradeProbeProvider (n := n) (N := N) (M := M) := by
  intro F hF hi _hphase r waves
  let A := emptyNativeProbeAtlas (n := n) (M := M)
  have hA : IsSmoothBufferedAtlas A := emptyNativeProbeAtlas_smooth
  have hcompact : ∀ i, IsCompact (A.support i) := fun i => Fin.elim0 i
  have hcover : ∀ x, ∃ i, x ∈ A.support i := fun x => isEmptyElim x
  exact ⟨A,hA,hcompact,hcover,⟨nativeProbeData_of_isEmpty F hF A hA hcompact hcover hi waves⟩⟩

end GlobalEmbedding.Main

#print axioms GlobalEmbedding.Main.probeAtlasCj_eq_zero_of_isEmpty
#print axioms GlobalEmbedding.Main.nativeProbeData_of_isEmpty
#print axioms GlobalEmbedding.Main.nativeUpgradeProbeProvider_of_isEmpty
