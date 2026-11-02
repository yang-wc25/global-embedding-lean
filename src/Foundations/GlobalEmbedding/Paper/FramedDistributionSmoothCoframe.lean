import GlobalEmbedding.Paper.FramedDistribution
import GlobalEmbedding.Paper.FrameGramInverseIdentities
import GlobalEmbedding.Paper.SmoothFrameGramCoefficients
import GlobalEmbedding.Paper.ManifoldFiniteOperatorSmoothness
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Actual smooth coframes dual to a framed distribution

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:planar`, lines245–258.
Local tangent coordinates and the actual inverse Gram operator construct local left inverses.
The native convex-section partition theorem patches them while preserving the exact frame
identities. No metric, coframe or desired formal derivative is supplied as an input.
-/

noncomputable section

open Bundle Filter Set
open scoped Topology Manifold ContDiff

namespace GlobalEmbedding.Paper

private def framedCoordinateOperator {b : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (v : Fin b → F) :
    EuclideanSpace ℝ (Fin b) →L[ℝ] F :=
  ∑ i, (EuclideanSpace.proj i).smulRight (v i)

private theorem framedCoordinateOperator_apply {b : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (v : Fin b → F)
    (a : EuclideanSpace ℝ (Fin b)) :
    framedCoordinateOperator v a = ∑ i, a i • v i := by
  simp [framedCoordinateOperator]

private theorem framedCoordinateOperator_single {b : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (v : Fin b → F) (i : Fin b) :
    framedCoordinateOperator v (EuclideanSpace.single i 1) = v i := by
  rw [framedCoordinateOperator_apply]
  simp [EuclideanSpace.single]

private theorem framedCoordinateOperator_injective {b : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (v : Fin b → F)
    (hv : LinearIndependent ℝ v) : Function.Injective (framedCoordinateOperator v) := by
  intro a c hac
  have hcoeff : (fun i ↦ a i) = (fun i ↦ c i) :=
    hv.fintypeLinearCombination_injective (by
      simpa only [Fintype.linearCombination_apply, framedCoordinateOperator_apply] using hac)
  ext i
  exact congrFun hcoeff i

private theorem exists_local_framed_coframe
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {b : ℕ} (D : FramedDistribution I (M := M) b) (x₀ : M) :
    ∃ U ∈ 𝓝 x₀, ∃ B : (x : M) → TangentSpace I x →L[ℝ] EuclideanSpace ℝ (Fin b),
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] EuclideanSpace ℝ (Fin b))) ∞
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] EuclideanSpace ℝ (Fin b)) x (B x)) U ∧
      ∀ x ∈ U, ∀ i, B x (D.frame i x) = EuclideanSpace.single i 1 := by
  classical
  let V := EuclideanSpace ℝ (Fin b)
  let P := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let c : E ≃L[ℝ] P := ContinuousLinearEquiv.ofFinrankEq (by simp [P])
  let e := trivializationAt E (TangentSpace I) x₀
  let U := e.baseSet
  let v (x : M) (i : Fin b) : P := c (e ⟨x, D.frame i x⟩).2
  let A (x : M) : V →L[ℝ] P := framedCoordinateOperator (v x)
  have hv (i : Fin b) : ContMDiffOn I 𝓘(ℝ, P) ∞ (fun x ↦ v x i) U := by
    have h := (e.contMDiffOn_section_baseSet_iff).mp (D.frame i).contMDiff.contMDiffOn
    exact c.contDiff.contMDiff.comp_contMDiffOn h
  have hA : ContMDiffOn I 𝓘(ℝ, V →L[ℝ] P) ∞ A U := by
    intro x hx
    apply ContMDiffAt.contMDiffWithinAt
    apply (manifold_finite_operator_smooth_iff A x).mpr
    intro a
    have hs : ContMDiffOn I 𝓘(ℝ, P) ∞ (fun y ↦ ∑ i, a i • v y i) U :=
      contMDiffOn_finsetSum fun i _ ↦
        (contMDiffOn_const : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun _ : M ↦ a i) U).smul (hv i)
    have heval : (fun y ↦ A y a) = (fun y ↦ ∑ i, a i • v y i) := by
      funext y
      exact framedCoordinateOperator_apply (v y) a
    rw [heval]
    exact hs.contMDiffAt (e.open_baseSet.mem_nhds hx)
  have hinj (x : M) (hx : x ∈ U) : Function.Injective (A x) := by
    apply framedCoordinateOperator_injective
    let ec : TangentSpace I x ≃L[ℝ] P := (e.continuousLinearEquivAt ℝ x hx).trans c
    exact (D.independent x).map' ec.toLinearMap (LinearMap.ker_eq_bot.mpr ec.injective)
  let L (x : M) : P →L[ℝ] V := ((A x).adjoint.comp (A x)).inverse.comp (A x).adjoint
  have hL : ContMDiffOn I 𝓘(ℝ, P →L[ℝ] V) ∞ L U :=
    smooth_frame_gram_coefficients A hA hinj
  let et := trivializationAt V (fun _ : M ↦ V) x₀
  let eh := e.continuousLinearMap (RingHom.id ℝ) et
  let B (x : M) : TangentSpace I x →L[ℝ] V :=
    eh.symmL ℝ x ((L x).comp c.toContinuousLinearMap)
  have hbase (x : M) (hx : x ∈ U) : x ∈ eh.baseSet := by
    simpa [eh, et, U] using hx
  have hB : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] V)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] V) x (B x)) U := by
    apply (eh.contMDiffOn_section_iff e.open_baseSet (fun x hx ↦ hbase x hx)).mpr
    apply (hL.clm_comp contMDiffOn_const).congr
    intro x hx
    dsimp only [B]
    rw [eh.symmL_apply (hbase x hx), eh.apply_mk_symm (hbase x hx)]
  refine ⟨U, e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E (TangentSpace I) x₀),
    B, hB, ?_⟩
  intro x hx i
  have hleft := (frame_gram_inverse_identities (A x) (hinj x hx)).1
  have hi := congrArg (fun f : V →L[ℝ] V ↦ f (EuclideanSpace.single i 1)) hleft
  have hAi : A x (EuclideanSpace.single i 1) = v x i :=
    framedCoordinateOperator_single (v x) i
  dsimp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hi
  rw [hAi] at hi
  change B x (D.frame i x) = _
  dsimp only [B]
  rw [eh.symmL_apply (hbase x hx)]
  change ((Pretrivialization.continuousLinearMap (RingHom.id ℝ) e et).symm x
      ((L x).comp c.toContinuousLinearMap)) (D.frame i x) = _
  rw [Pretrivialization.continuousLinearMap_symm_apply' (RingHom.id ℝ) e et (hbase x hx)]
  change et.symmL ℝ x ((L x) (c (e.continuousLinearMapAt ℝ x (D.frame i x)))) = _
  rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hx]
  simpa [L, v, et] using hi

/-- The ordered frame of a genuine framed distribution has a global native smooth coframe
with exactly the prescribed values on every frame vector, including rank zero and empty
manifolds. No metric, coframe, formal derivative or splitting is an input.

Proof: in a native tangent trivialization, express the actual frame in a fixed Euclidean
model. The accepted inverse Gram formula gives a smooth left inverse on the chart base.
The induced Hom trivialization turns this into a genuine local section of the coframe
bundle. Its prescribed frame identities are affine constraints in each fiber, hence convex.
The native smooth convex-section theorem uses an actual subordinate partition of unity to
patch these local sections, preserving their values because the partition sums to one.
Source: `lem:planar`, first proof paragraph, dual covectors to the given frame, lines245–258. -/
theorem framed_distribution_smooth_coframe
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [CompactSpace M] {b : ℕ} (D : FramedDistribution I (M := M) b) :
    ∃ B : ContMDiffSection I (E →L[ℝ] EuclideanSpace ℝ (Fin b)) ∞
        (fun x : M ↦ TangentSpace I x →L[ℝ] EuclideanSpace ℝ (Fin b)),
      ∀ x i, B x (D.frame i x) = EuclideanSpace.single i 1 := by
  have hc (x : M) : Convex ℝ
      {B : TangentSpace I x →L[ℝ] EuclideanSpace ℝ (Fin b) |
        ∀ i, B (D.frame i x) = EuclideanSpace.single i 1} := by
    intro B hB C hC a d _ _ had i
    change a • B (D.frame i x) + d • C (D.frame i x) = _
    rw [hB i, hC i, ← add_smul, had, one_smul]
  exact exists_contMDiffSection_forall_mem_convex_of_local (n := (⊤ : ℕ∞)) I
    (fun x : M ↦ TangentSpace I x →L[ℝ] EuclideanSpace ℝ (Fin b))
    (fun x ↦ {B | ∀ i, B (D.frame i x) = EuclideanSpace.single i 1}) hc
    (exists_local_framed_coframe I D)

#print axioms framed_distribution_smooth_coframe

end GlobalEmbedding.Paper
