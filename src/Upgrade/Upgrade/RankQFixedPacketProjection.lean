import Upgrade.RankQFixedPacketGeometry
import Upgrade.RankQFixedPairExtraction

/-!
# The fixed local packet supplies the actual joint normal principal rank

This specializes the accepted duplicated-principal proof to the fixed packet
selected BEFORE probes. The ambient columns are exactly its global wave
`tensors` and `values`; their projection is computed, not supplied by a rank
hypothesis. The same packet works for every positive unequal returned weight.
-/

noncomputable section
open Manifold Module Function Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Upgrade
open Paper Paper.SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Ambient" => EuclideanSpace ℝ (Fin N)

/-- Full joint projected span of the same fixed actual tensor/value packet.
The only rank assumption is the original stratum rank of `trueSecondForm`;
no rank of a perturbation or incidence derivative is an input. -/
theorem RankQLocalWavePacket.duplicated_projected_finrank
    {F : M → Ambient} {hF : ContMDiff IM 𝓘(ℝ, Ambient) ∞ F} {x y : M}
    (p : RankQLocalWavePacket F hF x y)
    (himm : Function.Injective (mfderiv IM 𝓘(ℝ, Ambient) F x))
    (hphase : PhaseRegular F hF) (hn : 3 ≤ n) (hN : N = n * (n + 1) / 2 + 1)
    (hrank : finrank ℝ (trueSecondForm F hF x).range = n * (n - 1) / 2)
    (lambda : Fin n → Fin 2 → ℝ)
    (hlambda : ∀ i j, 0 < lambda i j) (hne : ∀ i, lambda i 0 ≠ lambda i 1) :
    let B := rankQActualReference F hF x
    let K := B.ker
    let L := B.rangeᗮ
    let PN : Ambient →L[ℝ] normalSpace (I := IM) F x :=
      (normalSpace (I := IM) F x).orthogonalProjectionOnto
    let PL : normalSpace (I := IM) F x →L[ℝ] L := L.orthogonalProjectionOnto
    let D (i : Fin n) : K →L[ℝ] L := rankQNormalBlock B (PN.comp ((p.waves i).tensor x))
    let J (ij : Fin n × Fin 2) : (K →L[ℝ] L) × L :=
      (D ij.1, PL (PN (-((lambda ij.1 ij.2 ^ 2)⁻¹) • (p.waves ij.1).value x)))
    finrank ℝ (Submodule.span ℝ (Set.range J)) = n + 1 := by
  classical
  let B := rankQActualReference F hF x
  let K := B.ker
  let L := B.rangeᗮ
  let PN : Ambient →L[ℝ] normalSpace (I := IM) F x :=
    (normalSpace (I := IM) F x).orthogonalProjectionOnto
  let PL : normalSpace (I := IM) F x →L[ℝ] L := L.orthogonalProjectionOnto
  let Q : Ambient →L[ℝ] L := PL.comp PN
  let D (i : Fin n) : K →L[ℝ] L := rankQNormalBlock B (PN.comp ((p.waves i).tensor x))
  obtain ⟨ell, hell, hspan, hdim⟩ :=
    p.normal_coordinates_span himm hphase hn hN hrank lambda hlambda hne
  have hvalue (i : Fin n) : Q ((p.waves i).value x) = ell i :=
    p.projected_value_coordinates ell hell i
  have hres := rankQFixedPair_projected_span_transfer
    (ι := Fin n) (U := K →L[ℝ] L) (V := Ambient) (Z := L)
    D (fun i ↦ (p.waves i).value x) ell Q.toLinearMap hvalue
    (fun ij ↦ -((lambda ij.1 ij.2 ^ 2)⁻¹)) (n + 1) hspan hdim
  exact hres.2

end GlobalEmbedding.Upgrade
