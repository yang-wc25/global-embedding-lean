import Repair.IncrementUniformSignedReserve
import Smoothing.Round4NativeFrameReserve

/-!
# Uniform numerical signed reserves for the actual secondary solve

The same numerical template cover produces the reserve on the literal
kernel of a signed phase.  The genuine normal-Hessian coordinate identity
then gives the lower bound on the original ambient transverse frame used by
the finite solver.  Its constant depends only on the allowed operator class,
the fixed templates and the coordinate differential bound.  It is chosen
before the map, parameter chart and secondary signed record.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function
open scoped TensorProduct ContDiff Topology
namespace GlobalEmbedding.Continuation

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule

private local instance secondaryReserveRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private local instance secondaryReserveSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}

variable {K : Set ((SymmetricSquare (EuclideanSpace ℝ (Fin (m+1))) →L[ℝ]
  EuclideanSpace ℝ (Fin N)) × (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
    EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] ℝ))}

/-- A single numerical beta reserve for every signed phase covered by the
same allowed template family.  `J` bounds the squared inverse differential. -/
def incrementSecondaryFrameReserve (C : UniformActualGoodDictionaryCover K) (R J : ℝ) : ℝ :=
  (incrementUniformSignedMargin C R / (J * actualIncrementSortedSymmetricConstant m))^2

theorem incrementSecondaryFrameReserve_pos
    (C : UniformActualGoodDictionaryCover K) (R J : ℝ) (hJ : 0 < J) :
    0 < incrementSecondaryFrameReserve C R J := by
  apply sq_pos_of_pos
  exact div_pos (incrementUniformSignedMargin_pos C R)
    (mul_pos hJ (actualIncrementSortedSymmetricConstant_pos m))

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

/-- The normalized actual signed covector supplies the native kernel margin
and the same original beta-adjoint frame reserve.  The tensor identity is
produced by the actual source-coordinate transition, not postulated. -/
theorem increment_actual_secondary_frame_reserve
    (C : UniformActualGoodDictionaryCover K) (R J : ℝ) (hJ : 0 < J)
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (e0 e1 : Ep → OpenPartialHomeomorph M D)
    (he0 : ∀ p, e0 p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (he1 : ∀ p, e1 p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (U W : Set X) (hU : IsOpen U) (hW : IsOpen W)
    (hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e0 z.1).symm z.2)) W)
    (hPhi : ContDiffOn ℝ ∞ (actualSourceChartTransition e0 e1) U)
    (hMap : MapsTo (actualSourceChartTransition e0 e1) U W)
    (hCoord : ∀ z ∈ U, z.2 ∈ (e1 z.1).target ∧ (e1 z.1).symm z.2 ∈ (e0 z.1).source)
    (z : X) (hz : z ∈ U)
    (A : D ≃L[ℝ] D)
    (hJac : A.toContinuousLinearMap = actualJointSpatialJacobian (actualSourceChartTransition e0 e1) z)
    (hInverse : ‖A.symm.toContinuousLinearMap‖^2 ≤ J)
    (i : C.indices) (a : EdgePair (Module.finrank ℝ D+1)) (w : ℝ) (hw : w ≠ 0)
    (hUpper : ‖round4ActualPhaseOperatorInChart F e0 (actualSourceChartTransition e0 e1 z)‖ ≤ R)
    (hTemplate : round4ActualPhaseOperatorInChart F e0 (actualSourceChartTransition e0 e1 z) ∈
      (C.template i).operatorDomain)
    (hClose : ‖w⁻¹ • actualIncrementCoordinateCovector A - (C.template i).covectors a‖ <
      incrementUniformSignedRadius C R)
    (v : Tdata) :
    incrementSecondaryFrameReserve C R J * ‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e1 z.1).symm z.2 v‖^2 := by
  let y := actualSourceChartTransition e0 e1 z
  have hMargin := (increment_uniform_signed_control C R
    (round4ActualPhaseOperatorInChart F e0 y) hUpper i hTemplate a
    (actualIncrementCoordinateCovector A) w hw hClose).2.1
  have hTensor : actualNormalHessianInChart F e1 z =
      (actualNormalHessianInChart F e0 y).bilinearComp A.toContinuousLinearMap A.toContinuousLinearMap := by
    rw [hJac]
    exact actual_normal_hessian_true_chart_transition F hF e0 e1 he0 U W hU hW
      hJoint hPhi hMap hCoord z hz
  exact round4_actual_native_frame_reserve F hF e0 e1 he1 W hW hJoint
    y (hMap hz) z (hCoord z hz).1 A hTensor (actualIncrementCoordinateCovector A) rfl
    (incrementUniformSignedMargin C R) J (incrementUniformSignedMargin_pos C R).le hJ
    hInverse hMargin v

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.increment_actual_secondary_frame_reserve
