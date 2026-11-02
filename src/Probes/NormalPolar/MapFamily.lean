import NormalPolar.ManifoldProjection
import NormalPolar.Smooth
import NormalPolar.ConstructionNormalEquiv
import Upgrade.ProbeInterface
import GlobalEmbedding.Paper.ImmersionNormalRank

/-!
# A total normal identification for one actual immersion family

The admitted domain uses the explicit polar identification. The original
interface asks for an isometry even outside that domain; injectivity of the
actual source differentials gives equal actual normal ranks and supplies an
arbitrary isometry only when the projections are not close. No map is changed.
On every domain with the real projection gap below one, the ambient operator
is exactly the explicit formula and joint smoothness is derived from the maps.
-/

noncomputable section
open Manifold Set
open scoped ContDiff Topology

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade

section EqualRank
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- A total extension used only away from the actual polar neighborhood. -/
def normalEquivOfEqualRank (K L : Submodule ℝ V)
    (hdim : Module.finrank ℝ L = Module.finrank ℝ K) : L ≃ₗᵢ[ℝ] K :=
  ((stdOrthonormalBasis ℝ L).reindex (finCongr hdim)).repr.trans
    (stdOrthonormalBasis ℝ K).repr.symm

/-- One total identification, equal to the explicit polar construction on
its genuine projection-gap domain. -/
def totalNormalPolarEquiv (K L : Submodule ℝ V)
    (hdim : Module.finrank ℝ L = Module.finrank ℝ K) : L ≃ₗᵢ[ℝ] K :=
  if hclose : ‖K.starProjection - L.starProjection‖ < 1 then
    actualNormalPolarEquiv K L hclose
  else normalEquivOfEqualRank K L hdim

theorem totalNormalPolarEquiv_eq (K L : Submodule ℝ V)
    (hdim : Module.finrank ℝ L = Module.finrank ℝ K)
    (hclose : ‖K.starProjection - L.starProjection‖ < 1) :
    totalNormalPolarEquiv K L hdim = actualNormalPolarEquiv K L hclose := by
  simp only [totalNormalPolarEquiv, dite_eq_left hclose]

theorem totalNormalPolarEquiv_operator (K L : Submodule ℝ V)
    (hdim : Module.finrank ℝ L = Module.finrank ℝ K)
    (hclose : ‖K.starProjection - L.starProjection‖ < 1) :
    K.subtypeL.comp ((totalNormalPolarEquiv K L hdim).toContinuousLinearEquiv.toContinuousLinearMap.comp
      L.orthogonalProjectionOnto) = actualPolarOperator K.starProjection L.starProjection := by
  rw [totalNormalPolarEquiv_eq K L hdim hclose]
  exact actualNormalPolarEquiv_operator K L hclose

end EqualRank

variable {n N : ℕ} {M P : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ, E)

/-- The actual native normal ranks agree because both actual maps immerse
the same source into the same ambient space. -/
theorem actualMap_normalRanks_eq (F₀ F : M → V)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (hi : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x)) (x : M) :
    Module.finrank ℝ (normalSpace (I := IM) F x) =
      Module.finrank ℝ (normalSpace (I := IM) F₀ x) := by
  rw [immersion_normal_rank F x (hi x), immersion_normal_rank F₀ x (hi₀ x)]

/-- The same total actual map family gets its actual normal identification.
There is no input normal equivalence or output regularity assumption. -/
def actualImmersionNormalIdentification (F₀ F : M → V)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (hi : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x)) (x : M) :
    normalSpace (I := IM) F x ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ x :=
  totalNormalPolarEquiv (normalSpace (I := IM) F₀ x) (normalSpace (I := IM) F x)
    (actualMap_normalRanks_eq F₀ F hi₀ hi x)

theorem actualImmersionNormalIdentification_operator (F₀ F : M → V)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (hi : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x)) (x : M)
    (hclose : ‖(normalSpace (I := IM) F₀ x).starProjection -
      (normalSpace (I := IM) F x).starProjection‖ < 1) :
    normalIdentificationOperator (n := n) F₀ F
      (actualImmersionNormalIdentification F₀ F hi₀ hi) x =
      actualPolarOperator (normalSpace (I := IM) F₀ x).starProjection
        (normalSpace (I := IM) F x).starProjection := by
  exact totalNormalPolarEquiv_operator _ _ _ hclose

/-- This supplies the native normalIdentification_smooth field on the
original open parameter domain. Both true projection fields are derived from
the maps; the identification is the fixed total construction above. -/
theorem contMDiffOn_actualImmersionNormalIdentification
    (F₀ : M → V) (F : P → M → V)
    (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (hF : ∀ u, ContMDiff IM 𝓘(ℝ, V) ∞ (F u))
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (hi : ∀ u x, Function.Injective (mfderiv IM 𝓘(ℝ, V) (F u) x))
    {U : Set P} (hU : IsOpen U)
    (hjoint : ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V) ∞
      (Function.uncurry F) (U ×ˢ univ))
    (hgap : ∀ u ∈ U, ∀ x,
      ‖(normalSpace (I := IM) F₀ x).starProjection -
        (normalSpace (I := IM) (F u) x).starProjection‖ < 1) :
    ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V →L[ℝ] V) ∞
      (fun z : P × M ↦ normalIdentificationOperator (n := n) F₀ (F z.1)
        (actualImmersionNormalIdentification F₀ (F z.1) hi₀ (hi z.1)) z.2)
      (U ×ˢ univ) := by
  have hp : ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V →L[ℝ] V) ∞
      (fun z : P × M ↦ (normalSpace (I := IM) F₀ z.2).starProjection)
      (U ×ˢ univ) :=
    ((smooth_immersion_normal_projection F₀ hF₀ hi₀).comp contMDiff_snd).contMDiffOn
  have hr := contMDiffOn_joint_normalProjection F hF hU hjoint (fun u _ ↦ hi u)
  have hq := contMDiffOn_actualPolarOperator ((𝓘(ℝ, P)).prod IM) _ _ (U ×ˢ univ)
    hp hr (fun z hz ↦ hgap z.1 hz.1 z.2)
  apply hq.congr
  intro z hz
  exact actualImmersionNormalIdentification_operator F₀ (F z.1) hi₀ (hi z.1) z.2
    (hgap z.1 hz.1 z.2)

/-- An explicit mapping family supplies all normal-bundle fields of the
original geometry interface. The map, scale threshold and parameter ball
are definitionally the supplied ones. Its remaining quantitative probe
fields can be built upstream using this exact identification. -/
def probeGeometryOfActualImmersions
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    {r : ℕ} (F : ℝ → ProbeParameters r → M → V)
    (radius threshold : ℝ) (hradius : 0 < radius) (hthreshold : 0 < threshold)
    (hF : ∀ t u, ContMDiff IM 𝓘(ℝ, V) ∞ (F t u))
    (hi : ∀ t u x, Function.Injective (mfderiv IM 𝓘(ℝ, V) (F t u) x))
    (hjoint : ∀ t, 0 < t → t < threshold →
      ContMDiffOn ((𝓘(ℝ, ProbeParameters r)).prod IM) 𝓘(ℝ, V) ∞
        (Function.uncurry (F t)) (Metric.ball 0 radius ×ˢ univ))
    (hmetric : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius → ∀ x,
      inducedMetric (I := IM) (F t u) x = inducedMetric (I := IM) F₀ x)
    (hreserve : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius → ∀ x,
      ‖(normalSpace (I := IM) F₀ x).starProjection -
        (normalSpace (I := IM) (F t u) x).starProjection‖ < 1) :
    ProbeGeometry (n := n) F₀ r where
  radius := radius
  radius_pos := hradius
  threshold := threshold
  threshold_pos := hthreshold
  map := F
  slice_smooth := hF
  joint_smooth := hjoint
  metric := hmetric
  normalIdentification := fun t u ↦ actualImmersionNormalIdentification F₀ (F t u) hi₀ (hi t u)
  normalIdentification_smooth := by
    intro t ht htt
    apply contMDiffOn_actualImmersionNormalIdentification F₀ (F t) hF₀ (hF t) hi₀
      (hi t) Metric.isOpen_ball (hjoint t ht htt)
    intro u hu x
    exact hreserve t ht htt u (by simpa only [Metric.mem_ball, dist_zero_right] using hu) x

end GlobalEmbedding.NormalPolar
