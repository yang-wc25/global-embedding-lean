import Upgrade.RankQActualIncidence
import Upgrade.SupportedProbeJointSmooth

/-!
# Smoothness of the literal actual rank-q incidence

The coordinate second form is the actual joint Hessian of the same family,
with its actual varying normal identification and source frame. Smoothness
of the Schur equation is proved from the protected invertible block. The
separate charts permit pairs from different components.
-/

noncomputable section
open Function Manifold Module Set
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade
open Paper SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

local instance residualNormedAddCommGroup
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F) (x : M) :
    NormedAddCommGroup ((rankQActualReference F hF x).ker →L[ℝ]
      (rankQActualReference F hF x).rangeᗮ) :=
  rankQResidualNormedAddCommGroup (rankQActualReference F hF x)

local instance residualNormedSpace
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F) (x : M) :
    NormedSpace ℝ ((rankQActualReference F hF x).ker →L[ℝ]
      (rankQActualReference F hF x).rangeᗮ) :=
  rankQResidualNormedSpace (rankQActualReference F hF x)

/-- Joint smoothness follows from the original actual family and its actual
identification; no extra smoothness premise on a second-form field appears. -/
theorem actualRankQJointIncidence_contDiffOn
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (G : P → M → V) (hG : ∀ u, ContMDiff IM 𝓘(ℝ, V) ∞ (G u))
    (Q : ∀ u z, normalSpace (I := IM) (G u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i j : Fin A.count)
    (x : M) (hx : x ∈ (A.chart i).source) (sigma a : ℝ)
    {U : Set P} (hU : IsOpen U)
    (hmap : ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V) ∞
      (Function.uncurry G) (U ×ˢ univ))
    (hQ : ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V →L[ℝ] V) ∞
      (fun z : P × M ↦ normalIdentificationOperator (n := n) F₀ (G z.1) (Q z.1) z.2)
      (U ×ˢ univ))
    {Ω : Set (P × (E × E))}
    (hΩ : ∀ w ∈ Ω, w.1 ∈ U ∧ w.2.1 ∈ (A.chart i).target ∧
      w.2.2 ∈ (A.chart j).target)
    (hblock : ∀ w ∈ Ω, (rankQBlockA (rankQActualReference F₀ hF₀ x)
      (actualSupportedProbeCoordinate F₀ G hG Q A hA i x hx (w.1,w.2.1))).IsInvertible) :
    ContDiffOn ℝ ∞ (actualRankQJointIncidence F₀ hF₀ G hG Q A hA i j x hx sigma a) Ω := by
  have hfirst : ContDiff ℝ ∞ (fun w : P × (E × E) ↦ (w.1,w.2.1)) :=
    contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
  have hsecond : ContDiff ℝ ∞ (fun w : P × (E × E) ↦ (w.1,w.2.2)) :=
    contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)
  have hC := (actualSupportedProbeCoordinate_contDiffOn F₀ G hG Q A hA i x hx
    hU hmap hQ).comp hfirst.contDiffOn
      (fun w hw ↦ ⟨(hΩ w hw).1, (hΩ w hw).2.1⟩)
  have hFx := (contDiffOn_actual_parameter_atlas_pullback A hA i
    (Function.uncurry G) hmap).comp hfirst.contDiffOn
      (fun w hw ↦ ⟨(hΩ w hw).1, (hΩ w hw).2.1⟩)
  have hFy := (contDiffOn_actual_parameter_atlas_pullback A hA j
    (Function.uncurry G) hmap).comp hsecond.contDiffOn
      (fun w hw ↦ ⟨(hΩ w hw).1, (hΩ w hw).2.2⟩)
  intro w hw
  have hR := (rankQSchur_contDiffAt (rankQActualReference F₀ hF₀ x)
    (actualSupportedProbeCoordinate F₀ G hG Q A hA i x hx (w.1,w.2.1))
    (hblock w hw)).comp_contDiffWithinAt w (hC w hw)
  exact (hR.const_smul sigma⁻¹).prodMk (((hFx w hw).sub (hFy w hw)).const_smul a⁻¹)

#print axioms actualRankQJointIncidence_contDiffOn
end GlobalEmbedding.Upgrade
