import Main.GeneralNativeProbeConstruction
import NormalPolar.NativeProbeProvider

/-!
# Reuse the established upgrade with the unrestricted actual probe producer

The old geometric proof asks only for the bump waves which it explicitly
constructs. An arbitrary-cutoff native producer therefore supplies its input
by specialization. All maps, original norms, weights and parameter domains
are retained. The actual polar normal identification is definitionally the
same construction. This file does not assume that either producer exists.
-/

noncomputable section
open Set Filter Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.Continuation
open GlobalEmbedding.Upgrade GlobalEmbedding.NormalPolar

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,E)

namespace GeneralNativeProbeData

variable {F₀ : M → EuclideanSpace ℝ (Fin N)}
  {hF₀ : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin n))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F₀}
  {A : BufferedAtlas M (EuclideanSpace ℝ (Fin n))} {hA : IsSmoothBufferedAtlas A}
  {hcompact : ∀ i, IsCompact (A.support i)}
  {hcover : ∀ x, ∃ i, x ∈ A.support i}
  {hi₀ : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin n))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) F₀ x)}
  {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}

/-- Specialize only the wave input class. Every analytic output field is
literally the one already proved for the same original wave and family. -/
def toLocalNativeData
    (d : GeneralNativeProbeData F₀ hF₀ A hA hcompact hcover hi₀
      (fun l => OpenSupportedLegalWave.ofLocal (waves l))) :
    NativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves := by
  exact {
    radius := d.radius
    radius_pos := d.radius_pos
    threshold := d.threshold
    threshold_pos := d.threshold_pos
    map := d.map
    slice_smooth := d.slice_smooth
    immersion := d.immersion
    joint_smooth := d.joint_smooth
    metric := d.metric
    weight := d.weight
    weight_pos := d.weight_pos
    distinct_on_overlap := d.distinct_on_overlap
    constant := d.constant
    constant_nonneg := d.constant_nonneg
    etaH := d.etaH
    etaV := d.etaV
    etaH_nonneg := d.etaH_nonneg
    etaV_nonneg := d.etaV_nonneg
    etaH_tendsto := d.etaH_tendsto
    etaV_tendsto := d.etaV_tendsto
    closeness := d.closeness
    spatial_C3 := d.spatial_C3
    parameter_C1 := d.parameter_C1
    parameter_C2 := d.parameter_C2
    native_hessian_response := d.native_hessian_response
    value_response := d.value_response
    reserve := d.reserve
    reserve_lt_one := d.reserve_lt_one
    closeness_reserve := d.closeness_reserve }

/-- Specialization preserves even the constructed normal geometry, not just
the mapping family and its numerical estimates. -/
@[simp] theorem toLocalNativeData_geometry
    (d : GeneralNativeProbeData F₀ hF₀ A hA hcompact hcover hi₀
      (fun l => OpenSupportedLegalWave.ofLocal (waves l))) :
    d.toLocalNativeData.geometry = d.geometry := rfl

theorem toLocalNativeData_preserves
    (d : GeneralNativeProbeData F₀ hF₀ A hA hcompact hcover hi₀
      (fun l => OpenSupportedLegalWave.ofLocal (waves l))) :
    d.toLocalNativeData.map = d.map ∧ d.toLocalNativeData.weight = d.weight ∧
      d.toLocalNativeData.radius = d.radius ∧ d.toLocalNativeData.threshold = d.threshold ∧
      d.toLocalNativeData.constant = d.constant ∧ d.toLocalNativeData.reserve = d.reserve :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

end GeneralNativeProbeData

/-- The unrestricted native analytic contract. It is only an intermediate
statement: no final theorem in this file assumes it as an extra hypothesis. -/
def GeneralNativeProbeProvider : Prop :=
  ∀ (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (hi : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x)),
    PhaseRegular F hF → ∀ (r : ℕ) (waves : Fin r → OpenSupportedLegalWave F hF),
      ∃ (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
        (hcompact : ∀ i, IsCompact (A.support i))
        (hcover : ∀ x, ∃ i, x ∈ A.support i),
        Nonempty (GeneralNativeProbeData F hF A hA hcompact hcover hi waves)

/-- Any manufactured unrestricted native producer directly supplies the
already proved upgrade chain, without changing any current immersion. -/
theorem GeneralNativeProbeProvider.toNativeUpgradeProbeProvider
    (provider : GeneralNativeProbeProvider (n := n) (N := N) (M := M)) :
    NativeUpgradeProbeProvider (n := n) (N := N) (M := M) := by
  intro F hF hi hphase r waves
  obtain ⟨A,hA,hcompact,hcover,⟨d⟩⟩ :=
    provider F hF hi hphase r (fun l => OpenSupportedLegalWave.ofLocal (waves l))
  exact ⟨A,hA,hcompact,hcover,⟨d.toLocalNativeData⟩⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.GeneralNativeProbeData.toLocalNativeData
#print axioms GlobalEmbedding.Continuation.GeneralNativeProbeData.toLocalNativeData_geometry
#print axioms GlobalEmbedding.Continuation.GeneralNativeProbeProvider.toNativeUpgradeProbeProvider
