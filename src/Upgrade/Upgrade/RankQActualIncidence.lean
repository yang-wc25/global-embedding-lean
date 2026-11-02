import Upgrade.RankQIdentifiedCoordinates
import Upgrade.RankQResidualNorms
import Upgrade.IncidenceJointDerivative
import Upgrade.SupportedActualProbeCoordinate

/-!
# The literal rank-q coincidence incidence of an actual identified family

The first and second points use separate actual atlas charts, so pairs in
different components are included. The first equation is the constructed
Schur residual of the shared actual identified true-form coordinate field.
Its zero set is exactly rank q together with coincidence, on the actual
protected normal/block neighborhoods. No incidence rank is an input.
-/

noncomputable section
open Manifold Module
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade

section JointRegularity
variable {P X Y T R V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Internal chain rule for the one joint incidence map. -/
theorem rankQ_jointScaledIncidence_differentiableAt
    (B : P → X → T) (F : P → X → V) (H : P → Y → V) (equation : T → R)
    (sigma a : ℝ) (u : P) (x : X) (y : Y)
    (hB : DifferentiableAt ℝ (Function.uncurry B) (u,x))
    (hF : DifferentiableAt ℝ (Function.uncurry F) (u,x))
    (hH : DifferentiableAt ℝ (Function.uncurry H) (u,y))
    (hR : DifferentiableAt ℝ equation (B u x)) :
    DifferentiableAt ℝ (jointScaledIncidence B F H equation sigma a) (u,x,y) := by
  have hfirst : DifferentiableAt ℝ (fun w : P × (X × Y) ↦ (w.1,w.2.1)) (u,x,y) :=
    differentiableAt_fst.prodMk (differentiableAt_fst.comp _ differentiableAt_snd)
  have hsecond : DifferentiableAt ℝ (fun w : P × (X × Y) ↦ (w.1,w.2.2)) (u,x,y) :=
    differentiableAt_fst.prodMk (differentiableAt_snd.comp _ differentiableAt_snd)
  have hleft := (hR.comp (u,x,y) (hB.comp (u,x,y) hfirst)).const_smul sigma⁻¹
  have hright := ((hF.comp (u,x,y) hfirst).sub
    (hH.comp (u,x,y) hsecond)).const_smul a⁻¹
  exact hleft.prodMk hright
end JointRegularity

open Paper Paper.SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The two equations of the actual family, with its true changing normal
identification and normalized source frame left inside the coordinate field. -/
def actualRankQJointIncidence
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (G : P → M → V) (hG : ∀ u, ContMDiff IM 𝓘(ℝ, V) ∞ (G u))
    (Q : ∀ u z, normalSpace (I := IM) (G u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (i j : Fin A.count) (x : M) (hx : x ∈ (A.chart i).source) (sigma a : ℝ) :
    P × (E × E) →
        ((rankQActualReference F₀ hF₀ x).ker →L[ℝ] (rankQActualReference F₀ hF₀ x).rangeᗮ) × V := by
  exact @jointScaledIncidence P E E
    (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x)
    ((rankQActualReference F₀ hF₀ x).ker →L[ℝ] (rankQActualReference F₀ hF₀ x).rangeᗮ) V
    (rankQResidualNormedAddCommGroup (rankQActualReference F₀ hF₀ x))
    (rankQResidualNormedSpace (rankQActualReference F₀ hF₀ x)) inferInstance inferInstance
    (fun u v ↦ actualSupportedProbeCoordinate F₀ G hG Q A hA i x hx (u,v))
    (fun u v ↦ G u ((A.chart i).symm v))
    (fun u v ↦ G u ((A.chart j).symm v))
    (rankQSchur (rankQActualReference F₀ hF₀ x)) sigma a

/-- Exact dictionary for the actual two-point bad set, valid for separate
source charts and without connectedness or orientation assumptions. -/
theorem actualRankQJointIncidence_zero_iff
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (himm : ∀ z, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ z))
    (G : P → M → V) (hG : ∀ u, ContMDiff IM 𝓘(ℝ, V) ∞ (G u))
    (Q : ∀ u z, normalSpace (I := IM) (G u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (i j : Fin A.count) (x : M) (hx : x ∈ (A.chart i).source)
    (sigma a : ℝ) (hsigma : sigma ≠ 0) (ha : a ≠ 0)
    (w : P × (E × E)) (hw : w.2.1 ∈ (A.chart i).target)
    (hgap : ‖(normalSpace (I := IM) F₀ ((A.chart i).symm w.2.1)).starProjection -
      (normalSpace (I := IM) F₀ x).starProjection‖ < 1)
    (hrank : finrank ℝ (trueSecondForm F₀ hF₀ x).range = n * (n - 1) / 2)
    (hblock : (rankQBlockA (rankQActualReference F₀ hF₀ x)
      (actualSupportedProbeCoordinate F₀ G hG Q A hA i x hx (w.1,w.2.1))).IsInvertible) :
    actualRankQJointIncidence F₀ hF₀ G hG Q A hA i j x hx sigma a w = 0 ↔
      finrank ℝ (trueSecondForm (G w.1) (hG w.1) ((A.chart i).symm w.2.1)).range =
          n * (n - 1) / 2 ∧
        G w.1 ((A.chart i).symm w.2.1) = G w.1 ((A.chart j).symm w.2.2) := by
  let e := probeAtlasNormalizedFrameEquiv A hA i x hx ((A.chart i).symm w.2.1)
    ((A.chart i).map_target hw)
  have he : e.toContinuousLinearMap =
      probeAtlasNormalizedFrame A hA i x hx ((A.chart i).symm w.2.1) :=
    probeAtlasNormalizedFrameEquiv_toContinuousLinearMap A hA i x hx
      ((A.chart i).symm w.2.1) ((A.chart i).map_target hw)
  have hb : (rankQBlockA (rankQActualReference F₀ hF₀ x)
      (projectedIdentifiedTrueForm F₀ (G w.1) (hG w.1) (Q w.1)
        x ((A.chart i).symm w.2.1) e.toContinuousLinearMap)).IsInvertible := by
    rw [he]
    exact hblock
  have hzero := projectedIdentifiedTrueForm_schur_zero_iff F₀ (G w.1) hF₀
    (hG w.1) himm (Q w.1) x ((A.chart i).symm w.2.1) hgap e hrank hb
  rw [he] at hzero
  have hall := @jointScaledIncidence_eq_zero_iff P E E
    (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x)
    ((rankQActualReference F₀ hF₀ x).ker →L[ℝ] (rankQActualReference F₀ hF₀ x).rangeᗮ) V
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance
    (rankQResidualNormedAddCommGroup (rankQActualReference F₀ hF₀ x))
    (rankQResidualNormedSpace (rankQActualReference F₀ hF₀ x)) inferInstance inferInstance
    (fun u v ↦ actualSupportedProbeCoordinate F₀ G hG Q A hA i x hx (u,v))
    (fun u v ↦ G u ((A.chart i).symm v))
    (fun u v ↦ G u ((A.chart j).symm v))
    (rankQSchur (rankQActualReference F₀ hF₀ x)) sigma a hsigma ha w
  exact hall.trans (and_congr hzero Iff.rfl)

#print axioms actualRankQJointIncidence_zero_iff

end GlobalEmbedding.Upgrade
