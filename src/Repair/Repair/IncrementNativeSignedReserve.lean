import Repair.IncrementSecondaryReserve

/-!
# The original nonlinear signed phase in the same native chart

The signed phase need not be linear in the observing host: a foreign phase
is composed with the true host transition.  Its actual spatial differential
is identified with the kernel coordinate of the constructed native chart.
The numerical moving-kernel reserve then supplies the original transverse
frame lower bound on that chart's whole target.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Filter
open scoped TensorProduct ContDiff Topology
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule

private local instance nativeSignedRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private local instance nativeSignedSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}

/-- The actual spatial derivative of the first adapted source coordinate. -/
def incrementNativePhaseCovector (b : X → X) (y : X) : D →L[ℝ] ℝ :=
  (EuclideanSpace.proj 0).comp (actualJointSpatialJacobian b y)

theorem increment_actual_native_spatial_equiv
    (b : OpenPartialHomeomorph X X)
    (hb : ContDiffOn ℝ ∞ b b.source) (hbi : ContDiffOn ℝ ∞ b.symm b.target)
    (hp : ∀ y ∈ b.source, (b y).1 = y.1)
    (hpi : ∀ z ∈ b.target, (b.symm z).1 = z.1)
    (B : ℝ) (hB : ∀ y ∈ b.source, ‖fderiv ℝ b y‖ ≤ B)
    (z : X) (hz : z ∈ b.target) :
    ∃ A : D ≃L[ℝ] D,
      A.toContinuousLinearMap = actualJointSpatialJacobian b.symm z ∧
      A.symm.toContinuousLinearMap = actualJointSpatialJacobian b (b.symm z) ∧
      actualIncrementCoordinateCovector A = incrementNativePhaseCovector b (b.symm z) ∧
      ‖A.symm.toContinuousLinearMap‖ ≤ B := by
  let J := actualJointSpatialJacobian b.symm z
  let S := actualJointSpatialJacobian b (b.symm z)
  have hSJ : S.comp J = ContinuousLinearMap.id ℝ D :=
    actual_joint_spatial_jacobian_inverse b.symm hbi hb hpi z hz
  have hJS : J.comp S = ContinuousLinearMap.id ℝ D := by
    have h := actual_joint_spatial_jacobian_inverse b hb hbi hp (b.symm z) (b.map_target hz)
    simpa only [b.right_inv hz] using h
  let A := ContinuousLinearEquiv.equivOfInverse J S
    (fun v => congrArg (fun L : D →L[ℝ] D => L v) hSJ)
    (fun v => congrArg (fun L : D →L[ℝ] D => L v) hJS)
  refine ⟨A, rfl, rfl, rfl, ?_⟩
  exact (actual_joint_spatial_jacobian_norm_le b b.source b.open_source hb
    (b.symm z) (b.map_target hz)).trans (hB _ (b.map_target hz))

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

theorem increment_original_host_phase_differential
    (host : OpenPartialHomeomorph M D)
    (hhost : host ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (b : OpenPartialHomeomorph X X) (psi : Ep × M → ℝ)
    (e : Ep → OpenPartialHomeomorph M D)
    (hdata : ActualOriginalHostSliceData host b psi e) :
    (∀ y ∈ b.source, (b y).1 = y.1) ∧
    (∀ z ∈ b.target, (b.symm z).1 = z.1) ∧
    ∀ y ∈ b.source, incrementNativePhaseCovector b y =
      fderiv ℝ (fun x : D => psi (y.1,host.symm x)) y.2 := by
  have hGeom := actual_host_slice_geometry_inputs host hhost b psi e hdata
  rcases hdata with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hadapt,hback,hforward,hbj,hfj⟩
  let q := actualOriginalHostJointChart (Ep := Ep) host
  have hNative (y : X) (hy : y ∈ b.source) :
      (b y).1 = y.1 ∧ (b y).2 0 = psi (y.1,host.symm y.2) := by
    have hq : q.symm y ∈ (actualHostAdaptedChart host b).source :=
      ⟨q.map_target (hGeom.1 hy), by change q (q.symm y) ∈ b.source; rwa [q.right_inv (hGeom.1 hy)]⟩
    have hh := hforw (q.symm y) hq
    change (b (q (q.symm y))).1 = y.1 ∧
      (b (q (q.symm y))).2 0 = psi (y.1,host.symm y.2) at hh
    rwa [q.right_inv (hGeom.1 hy)] at hh
  refine ⟨fun y hy => (hNative y hy).1, ?_, ?_⟩
  · intro z hz
    exact congrArg (fun w : Ep × M => w.1) (hpair z hz)
  · intro y hy
    let f : D → D := fun x => (b (y.1,x)).2
    have hf : DifferentiableAt ℝ f y.2 :=
      ((hGeom.2.1.contDiffAt (b.open_source.mem_nhds hy)).snd.comp y.2
        (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
    have hg : (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (m+1)) 0) ∘ f =ᶠ[𝓝 y.2]
        (fun x : D => psi (y.1,host.symm x)) := by
      filter_upwards [(b.open_source.preimage (continuous_const.prodMk continuous_id)).mem_nhds hy]
        with x hx
      exact (hNative (y.1,x) hx).2
    have hh := hg.fderiv_eq (𝕜 := ℝ)
    rw [fderiv_comp y.2 (EuclideanSpace.proj 0).differentiableAt hf,
      ContinuousLinearMap.fderiv] at hh
    exact hh

variable {K : Set ((SymmetricSquare (EuclideanSpace ℝ (Fin (m+1))) →L[ℝ]
  EuclideanSpace ℝ (Fin N)) × (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
    EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] ℝ))}

/-- A genuine original adapted chart receives a numerical transverse reserve
from the actual signed phase differential. All coordinate identities are
derived from its existing `ActualOriginalHostSliceData`. -/
theorem increment_original_host_signed_frame_reserve
    (C : UniformActualGoodDictionaryCover K) (R B : ℝ) (hB : 0 < B)
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (host : OpenPartialHomeomorph M D)
    (hhost : host ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (b : OpenPartialHomeomorph X X) (psi : Ep × M → ℝ)
    (e : Ep → OpenPartialHomeomorph M D)
    (hdata : ActualOriginalHostSliceData host b psi e)
    (W : Set X) (hW : IsOpen W)
    (hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 (host.symm z.2)) W)
    (hSource : b.source ⊆ W)
    (hForward : ∀ y ∈ b.source, ‖fderiv ℝ b y‖ ≤ B)
    (z : X) (hz : z ∈ b.target)
    (i : C.indices) (a : EdgePair (Module.finrank ℝ D+1)) (w : ℝ) (hw : w ≠ 0)
    (hUpper : ‖round4ActualPhaseOperatorInChart F (fun _ => host) (b.symm z)‖ ≤ R)
    (hTemplate : round4ActualPhaseOperatorInChart F (fun _ => host) (b.symm z) ∈
      (C.template i).operatorDomain)
    (hClose : ‖w⁻¹ • fderiv ℝ (fun x : D => psi ((b.symm z).1,host.symm x)) (b.symm z).2 -
      (C.template i).covectors a‖ < incrementUniformSignedRadius C R)
    (v : Tdata) :
    incrementSecondaryFrameReserve C R (B^2) * ‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e z.1).symm z.2 v‖^2 := by
  have hGeom := actual_host_slice_geometry_inputs host hhost b psi e hdata
  obtain ⟨hp,hpi,hPhase⟩ := increment_original_host_phase_differential host hhost b psi e hdata
  obtain ⟨A,hA,hAi,hxi,hAn⟩ := increment_actual_native_spatial_equiv b hGeom.2.1 hGeom.2.2.1
    hp hpi B hForward z hz
  rcases hdata with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hadapt,hback,hforward,hbj,hfj⟩
  have hJ : actualJointSpatialJacobian (actualSourceChartTransition (fun _ => host) e) z =
      actualJointSpatialJacobian b.symm z := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [(b.open_target.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz]
      with x hx
    exact congrArg Prod.snd (hback hx)
  apply increment_actual_secondary_frame_reserve C R (B^2) (sq_pos_of_pos hB)
    F hF (fun _ => host) e (fun _ => hhost) he b.target W b.open_target hW hJoint
    hGeom.2.2.2.2.1 (fun y hy => hSource (hGeom.2.2.2.2.2.2.1 hy))
    hGeom.2.2.2.1 z hz A (hA.trans hJ.symm)
    ((sq_le_sq₀ (norm_nonneg _) hB.le).mpr hAn) i a w hw
  · rwa [hback hz]
  · rwa [hback hz]
  · rwa [hxi,hPhase (b.symm z) (b.map_target hz)]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.increment_original_host_signed_frame_reserve
