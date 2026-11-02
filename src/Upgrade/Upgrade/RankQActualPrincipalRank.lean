import Upgrade.RankQActualSecondForm
import Upgrade.RankQPrincipalAssembly
import GlobalEmbedding.Paper.NormalProjectionTangent

/-!
# Actual tangent columns complete the rank-q principal incidence block

The finite ambient tensor/value columns are the literal columns of the existing
`upgradeRankQ_exists_duplicated_principal_packet`. The only span input below is
that theorem's already proved principal span. The actual incidence derivative
is not assumed to have any rank. Its small-error realization is a separate
consumer of the finite frame produced here.
-/

noncomputable section
open Manifold Module Function
open scoped BigOperators ContDiff Topology

namespace GlobalEmbedding.Upgrade
open Paper Paper.SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {H M : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M]

/-- Native first-source derivative, included in the joint Schur/value output. -/
def rankQActualTangentColumn (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (x : M) :
    TangentSpace I x →L[ℝ]
      ((rankQActualReference F hF x).ker →L[ℝ] (rankQActualReference F hF x).rangeᗮ) ×
        EuclideanSpace ℝ (Fin N) :=
  (0 : TangentSpace I x →L[ℝ] _).prod
    ((tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (F x)).toContinuousLinearMap.comp
      (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F x))

/-- Projection kills the actual source tangents and retains both normal outputs. -/
def rankQActualJointProjection (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (x : M) :
    (((rankQActualReference F hF x).ker →L[ℝ] (rankQActualReference F hF x).rangeᗮ) ×
      EuclideanSpace ℝ (Fin N)) →L[ℝ]
    (((rankQActualReference F hF x).ker →L[ℝ] (rankQActualReference F hF x).rangeᗮ) ×
      (rankQActualReference F hF x).rangeᗮ) :=
  (ContinuousLinearMap.id ℝ _).prodMap
    ((rankQActualReference F hF x).rangeᗮ.orthogonalProjectionOnto.comp
      (normalSpace (I := I) F x).orthogonalProjectionOnto)

theorem rankQActualJointProjection_tangent (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (x : M) :
    (rankQActualJointProjection F hF x).comp (rankQActualTangentColumn F hF x) = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  apply Prod.ext
  · rfl
  · change (rankQActualReference F hF x).rangeᗮ.orthogonalProjectionOnto
      ((normalSpace (I := I) F x).orthogonalProjectionOnto
        (tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (F x)
          (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F x v))) = 0
    rw [normal_projection_mfderiv_eq_zero, map_zero]

/-- The literal first-source columns are injective at the original immersion. -/
theorem rankQActualTangentColumn_injective (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (x : M)
    (himm : Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F x)) :
    Function.Injective (rankQActualTangentColumn F hF x) := by
  intro v w h
  apply himm
  apply (tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (F x)).injective
  exact congrArg Prod.snd h

/-- Joint principal columns after the exact differential of the actual Schur chart. -/
def rankQActualPrincipalColumn (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (x : M)
    (A : SymmetricSquare (EuclideanSpace ℝ (Fin n)) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (v : EuclideanSpace ℝ (Fin N)) :
    ((rankQActualReference F hF x).ker →L[ℝ] (rankQActualReference F hF x).rangeᗮ) ×
      EuclideanSpace ℝ (Fin N) :=
  (rankQNormalBlock (rankQActualReference F hF x)
    ((normalSpace (I := I) F x).orthogonalProjectionOnto.comp A), v)

/-- The exact finite principal parameter map plus the actual first-source
linear derivative. Its domain is finite dimensional; the associated native
continuous linear map is obtained by `LinearMap.toContinuousLinearMap`. -/
def rankQActualJointPrincipalMap {ι : Type*} [Fintype ι]
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (x : M)
    (A : ι → SymmetricSquare (EuclideanSpace ℝ (Fin n)) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (v : ι → EuclideanSpace ℝ (Fin N)) :
    ((ι → ℝ) × TangentSpace I x) →ₗ[ℝ]
      (((rankQActualReference F hF x).ker →L[ℝ] (rankQActualReference F hF x).rangeᗮ) ×
        EuclideanSpace ℝ (Fin N)) :=
  (Fintype.linearCombination ℝ
    (fun i ↦ rankQActualPrincipalColumn F hF x (A i) (v i))).coprod
      (rankQActualTangentColumn F hF x).toLinearMap

/-- Exact finite synthesis in the actual joint map. -/
theorem rankQActualJointPrincipalMap_apply {ι : Type*} [Fintype ι]
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (x : M)
    (A : ι → SymmetricSquare (EuclideanSpace ℝ (Fin n)) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (v : ι → EuclideanSpace ℝ (Fin N)) (d : (ι → ℝ) × TangentSpace I x) :
    rankQActualJointPrincipalMap F hF x A v d =
      (∑ i, d.1 i • rankQActualPrincipalColumn F hF x (A i) (v i)) +
        rankQActualTangentColumn F hF x d.2 := by
  change (Fintype.linearCombination ℝ
    (fun i ↦ rankQActualPrincipalColumn F hF x (A i) (v i))) d.1 + _ = _
  rw [Fintype.linearCombination_apply]
  rfl

/-- The main duplicated-principal packet's dimension n+1 and the SAME actual
immersion derivative give principal joint rank at least 2n+1. No desired actual
incidence-rank hypothesis occurs. -/
theorem rankQActualJointPrincipalMap_finrank {ι : Type*} [Fintype ι]
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (x : M)
    (himm : Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F x))
    (A : ι → SymmetricSquare (EuclideanSpace ℝ (Fin n)) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (v : ι → EuclideanSpace ℝ (Fin N))
    (hpacket : finrank ℝ (Submodule.span ℝ (Set.range
      (fun i ↦ rankQActualJointProjection F hF x
        (rankQActualPrincipalColumn F hF x (A i) (v i))))) = n + 1) :
    2 * n + 1 ≤ finrank ℝ (rankQActualJointPrincipalMap F hF x A v).range := by
  have hQT : (rankQActualJointProjection F hF x).toLinearMap.comp
      (rankQActualTangentColumn F hF x).toLinearMap = 0 :=
    congrArg ContinuousLinearMap.toLinearMap (rankQActualJointProjection_tangent F hF x)
  have h := rankQPrincipalColumns_finrank
    (A := TangentSpace I x)
    (C := ((rankQActualReference F hF x).ker →L[ℝ]
      (rankQActualReference F hF x).rangeᗮ) × EuclideanSpace ℝ (Fin N))
    (D := ((rankQActualReference F hF x).ker →L[ℝ]
      (rankQActualReference F hF x).rangeᗮ) × (rankQActualReference F hF x).rangeᗮ)
    (fun i ↦ rankQActualPrincipalColumn F hF x (A i) (v i))
    (rankQActualTangentColumn F hF x).toLinearMap
    (rankQActualJointProjection F hF x).toLinearMap
    (rankQActualTangentColumn_injective F hF x himm) hQT n (n + 1)
    finrank_euclideanSpace_fin (by simpa only [Function.comp_apply] using! hpacket)
  have heq : 2 * n + 1 = n + (n + 1) := by omega
  rw [heq]
  exact h

/-- Choose one actual finite frame in the SAME joint principal map image,
whose positive norm margin is supplied by the accepted stability lemma. The
frame is fixed before fast angles,
probe parameters or the small scale are chosen. -/
theorem rankQActualJointPrincipalMap_finite_frame {ι : Type*} [Fintype ι]
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (x : M)
    (himm : Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F x))
    (A : ι → SymmetricSquare (EuclideanSpace ℝ (Fin n)) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (v : ι → EuclideanSpace ℝ (Fin N))
    (hpacket : finrank ℝ (Submodule.span ℝ (Set.range
      (fun i ↦ rankQActualJointProjection F hF x
        (rankQActualPrincipalColumn F hF x (A i) (v i))))) = n + 1) :
    let J := rankQActualJointPrincipalMap F hF x A v
    ∃ d : Fin (2 * n + 1) → ((ι → ℝ) × TangentSpace I x),
      LinearIndependent ℝ (fun i ↦ J (d i)) := by
  classical
  let : NormedAddCommGroup (SymmetricSquare (EuclideanSpace ℝ (Fin n))) := operatorSquareNormed
  let : NormedSpace ℝ (SymmetricSquare (EuclideanSpace ℝ (Fin n))) := squareNS _
  let : NormedAddCommGroup (normalSpace (I := I) F x) := Submodule.normedAddCommGroup _
  let : InnerProductSpace ℝ (normalSpace (I := I) F x) := inferInstance
  let B := rankQActualReference F hF x
  let : NormedAddCommGroup B.ker := inferInstance
  let : NormedSpace ℝ B.ker := inferInstance
  let : NormedAddCommGroup B.rangeᗮ := inferInstance
  let : NormedSpace ℝ B.rangeᗮ := inferInstance
  let : NormedAddCommGroup (B.ker →L[ℝ] B.rangeᗮ) := inferInstance
  let : NormedSpace ℝ (B.ker →L[ℝ] B.rangeᗮ) := inferInstance
  let : FiniteDimensional ℝ (B.ker →L[ℝ] B.rangeᗮ) := inferInstance
  let : FiniteDimensional ℝ ((B.ker →L[ℝ] B.rangeᗮ) × EuclideanSpace ℝ (Fin N)) := inferInstance
  let J := rankQActualJointPrincipalMap F hF x A v
  have hdim := rankQActualJointPrincipalMap_finrank F hF x himm A v hpacket
  let b := Module.finBasis ℝ J.range
  let e : Fin (2 * n + 1) → Fin (finrank ℝ J.range) := Fin.castLE hdim
  have he : Function.Injective e := Fin.castLE_injective hdim
  have hli : LinearIndependent ℝ (fun i : Fin (2 * n + 1) ↦
      ((b (e i)).val :
        ((B.ker →L[ℝ] B.rangeᗮ) × EuclideanSpace ℝ (Fin N)))) :=
    (b.linearIndependent.comp e he).map' J.range.subtype (by simp)
  have hex : ∀ i : Fin (2 * n + 1), ∃ d : (ι → ℝ) × TangentSpace I x,
      J d = (b (e i)).val := fun i ↦ (b (e i)).property
  choose d hd using hex
  refine ⟨d, ?_⟩
  change LinearIndependent ℝ (fun i ↦ J (d i))
  simpa only [hd] using hli

end GlobalEmbedding.Upgrade
