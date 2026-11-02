import Upgrade.RankQSchurRank
import Upgrade.RankQSchurDifferential

/-!
# Literal legal-operator packets enter the nonlinear Schur equation

The old normal block in the accepted finite legal-wave theorem is the exact
derivative of the new nonlinear residual.  No incidence rank is supplied as
an input. The first theorem also gives an explicit right inverse of the full
Schur derivative in actual kernel/range coordinates.
-/

noncomputable section
open scoped Topology
namespace GlobalEmbedding.Upgrade

variable {S W : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [FiniteDimensional ℝ S] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W]

/-- Every actual kernel-to-normal block is realized by an actual ambient
operator, using the genuine kernel projection already constructed above. -/
theorem rankQNormalBlock_surjective (B : S →L[ℝ] W) :
    Function.Surjective (rankQNormalBlock B) := by
  intro D
  refine ⟨B.rangeᗮ.subtypeL.comp (D.comp (rankQKernelProjection B)), ?_⟩
  apply ContinuousLinearMap.ext
  intro k
  change B.rangeᗮ.orthogonalProjectionOnto
    ((D (rankQKernelProjection B k) : B.rangeᗮ) : W) = D k
  simp

/-- The actual Schur equation has surjective derivative at the reference form. -/
theorem rankQSchur_fderiv_self_surjective (B : S →L[ℝ] W) :
    Function.Surjective (fderiv ℝ (rankQSchur B) B) := by
  rw [rankQSchur_fderiv_self]
  exact rankQNormalBlock_surjective B

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The same finite operator packet used by the accepted local legal waves has
this exact derivative after entering the nonlinear Schur residual. -/
theorem rankQSchur_hasFDerivAt_add_packet (B : S →L[ℝ] W)
    (packet : P →L[ℝ] (S →L[ℝ] W)) :
    HasFDerivAt (fun u ↦ rankQSchur B (B + packet u))
      ((rankQNormalBlock B).comp packet) 0 := by
  have hp : HasFDerivAt (fun u : P ↦ B + packet u) packet 0 :=
    packet.hasFDerivAt.const_add B
  have hs : HasFDerivAt (rankQSchur B) (rankQNormalBlock B) (B + packet 0) := by
    simpa only [map_zero, add_zero] using rankQSchur_hasFDerivAt_self B
  simpa only [Function.comp_def] using! HasFDerivAt.comp (𝕜 := ℝ) (E := P)
    (F := S →L[ℝ] W) (G := B.ker →L[ℝ] B.rangeᗮ) 0 hs hp

/-- Exact equality to the already accepted normal-block packet derivative. -/
theorem rankQSchur_fderiv_eq_normal_packet (B : S →L[ℝ] W)
    (packet : P →L[ℝ] (S →L[ℝ] W)) :
    fderiv ℝ (fun u ↦ rankQSchur B (B + packet u)) 0 =
      fderiv ℝ (fun u ↦ B.rangeᗮ.orthogonalProjectionOnto.comp
        ((B + packet u).comp B.ker.subtypeL)) 0 := by
  have hEq : (fun u : P ↦ B.rangeᗮ.orthogonalProjectionOnto.comp
      ((B + packet u).comp B.ker.subtypeL)) = (rankQNormalBlock B).comp packet := by
    funext u
    apply ContinuousLinearMap.ext
    intro k
    have hk : B (k : S) = 0 := k.property
    change B.rangeᗮ.orthogonalProjectionOnto ((B + packet u) (k : S)) =
      B.rangeᗮ.orthogonalProjectionOnto (packet u (k : S))
    simp only [ContinuousLinearMap.add_apply, hk, zero_add]
  rw [(rankQSchur_hasFDerivAt_add_packet B packet).fderiv, hEq]
  exact ((rankQNormalBlock B).comp packet).fderiv.symm

/-- The literal finite global tensors give the original normal block as their
finite linear combination. This identity does not use any packet rank. -/
theorem rankQNormalBlock_sum_comp {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {ι : Type*} [Fintype ι] (B : S →L[ℝ] W) (PN : V →L[ℝ] W)
    (A : ι → S →L[ℝ] V) (t : ι → ℝ) :
    B.rangeᗮ.orthogonalProjectionOnto.comp
      ((B + PN.comp (∑ i, t i • A i)).comp B.ker.subtypeL) =
        ∑ i, t i • rankQNormalBlock B (PN.comp (A i)) := by
  have hB : rankQNormalBlock B B = 0 := rankQBlockD_self B
  change rankQNormalBlock B (B + PN.comp (∑ i, t i • A i)) = _
  rw [map_add, hB, zero_add]
  simp only [ContinuousLinearMap.comp_finsetSum, ContinuousLinearMap.comp_smul, map_sum, map_smul]

end GlobalEmbedding.Upgrade
