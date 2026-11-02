import Repair.IncrementNativeSignedReserve
import Probes.ActualAdaptedFirstFrameReserve
import Probes.ActualFirstFrameChartTransfer
import Probes.Round3ParameterWholeReferenceProfiles
import Smoothing.Round4OriginalC3NativeJets

/-!
# Numerical reference reserves on the actual supplied native charts

These producers retain the existing chart functions and their slice maps.
Original host map jets, host ellipticity, chart derivatives and the original
kernel restriction margin produce the adapted first/transverse/Hessian
budgets.  No adapted frame or Hessian output bound is assumed.

The subsequent whole-packet constructor uses one numerical profile for all
pieces.  The numerical chart-jet certificates are intended to be supplied
by the actual linear/weighted chart construction; arbitrary compactly
chosen charts do not acquire uniform bounds merely by this constructor.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Filter
open scoped TensorProduct ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule

private local instance entranceReferenceRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private local instance entranceReferenceSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

/-- Original host C2 data and actual forward/inverse derivatives generate
the low reference budgets on this same adapted target. -/
theorem repairEntrance_native_original_low_budgets
    (F : Ep → M → V)
    (host : OpenPartialHomeomorph M D) (hhost : host ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (b : OpenPartialHomeomorph X X) (psi : Ep × M → ℝ)
    (e : Ep → OpenPartialHomeomorph M D)
    (hdata : ActualOriginalHostSliceData host b psi e)
    (W : Set X) (hW : IsOpen W)
    (hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 (host.symm z.2)) W)
    (hSource : b.source ⊆ W)
    (lower B K : ℝ) (hLower : 0 < lower) (hB : 0 < B) (hK : 0 ≤ K)
    (T : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j)
    (hFirst : ∀ z ∈ W, ∀ v : D,
      lower*‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ host.symm) z.2 v‖^2)
    (hJets : ∀ k ≤ 2, ∀ z ∈ W,
      ‖iteratedFDeriv ℝ k (fun y : X => F y.1 (host.symm y.2)) z‖ ≤ K)
    (hForward : ∀ y ∈ b.source, ‖fderiv ℝ b y‖ ≤ B)
    (hInverse : ∀ j z, z ∈ b.target → ‖iteratedFDeriv ℝ j b.symm z‖ ≤ T j) :
    (∀ z ∈ b.target, ∀ v : D,
      (lower/B^2)*‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2 v‖^2) ∧
    ∀ z ∈ b.target,
      ‖fderiv ℝ (fderiv ℝ (F z.1 ∘ (e z.1).symm)) z.2‖ ≤
        actualFirstFrameTransferCost T 1*K := by
  have hGeom := actual_host_slice_geometry_inputs host hhost b psi e hdata
  rcases hdata with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hadapt,hback,hforward,hbj,hfj⟩
  have hFirst' := actual_adapted_first_frame_reserve_from_original F (fun _ => host) e
    b.target b.source b.open_target b.open_source (hJoint.mono hSource)
    hGeom.2.2.2.2.1 hGeom.2.2.2.2.2.1 hGeom.2.2.2.2.2.2.1 hGeom.2.2.2.1
    lower B hLower hB (fun z hz => hFirst z (hSource hz)) (by
      intro z hz
      have hg := Filter.eventuallyEq_of_mem (b.open_source.mem_nhds hz)
        (fun y hy => hforward hy)
      rw [hg.fderiv_eq]
      exact hForward z hz)
  have hHostFirst : ∀ k ≤ 0+1, ∀ z ∈ W,
      (1:ℝ)^k*‖iteratedFDeriv ℝ k
        (fun y : X => fderiv ℝ (F y.1 ∘ host.symm) y.2) z‖ ≤ K := by
    intro k hk z hz
    simp only [one_pow,one_mul]
    exact (spatial_first_jet_le hW hJoint hz k).trans (hJets (k+1) (by omega) z hz)
  have hTransfer := actual_first_frame_hessian_transferred_from_original_jets
    T hT 0 F (fun _ => host) e b.target W b.open_target hW hJoint hGeom.2.2.2.2.1
    (fun y hy => hSource (hGeom.2.2.2.2.2.2.1 hy))
    (fun y hy => (hGeom.2.2.2.1 y hy).2) 1 K zero_lt_one hK hHostFirst (by
      intro k hk hk2 z hz
      rw [hbj k z hz]
      simpa only [one_pow,one_mul] using hInverse k z hz)
  refine ⟨hFirst',?_⟩
  intro z hz
  simpa only [one_pow,one_mul,norm_iteratedFDeriv_zero] using
    (hTransfer.2.2.2 0 le_rfl z hz).2

/-- The original restriction margin, in the original Sym² norm and for the
actual phase differential, produces the adapted transverse reserve. -/
theorem repairEntrance_native_original_transverse_reserve
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (host : OpenPartialHomeomorph M D) (hhost : host ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (b : OpenPartialHomeomorph X X) (psi : Ep × M → ℝ)
    (e : Ep → OpenPartialHomeomorph M D)
    (hdata : ActualOriginalHostSliceData host b psi e)
    (W : Set X) (hW : IsOpen W)
    (hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 (host.symm z.2)) W)
    (hSource : b.source ⊆ W)
    (mu B : ℝ) (hmu : 0 ≤ mu) (hB : 0 < B)
    (hForward : ∀ y ∈ b.source, ‖fderiv ℝ b y‖ ≤ B)
    (z : X) (hz : z ∈ b.target)
    (hMargin : ∀ w, mu*‖w‖ ≤ ‖covectorRestriction
      (round4ActualPhaseOperatorInChart F (fun _ => host) (b.symm z))
      (fderiv ℝ (fun x : D => psi ((b.symm z).1,host.symm x)) (b.symm z).2) w‖)
    (v : Tdata) :
    (mu/(B^2*actualIncrementSortedSymmetricConstant m))^2*‖v‖^2 ≤
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
  let y := actualSourceChartTransition (fun _ => host) e z
  have hTensor : actualNormalHessianInChart F e z =
      (actualNormalHessianInChart F (fun _ => host) y).bilinearComp
        A.toContinuousLinearMap A.toContinuousLinearMap := by
    rw [hA,← hJ]
    exact actual_normal_hessian_true_chart_transition F hF (fun _ => host) e
      (fun _ => hhost) b.target W b.open_target hW hJoint hGeom.2.2.2.2.1
      (fun y hy => hSource (hGeom.2.2.2.2.2.2.1 hy)) hGeom.2.2.2.1 z hz
  have hMargin' : ∀ w, mu*‖w‖ ≤ ‖covectorRestriction
      (round4ActualPhaseOperatorInChart F (fun _ => host) y)
      (actualIncrementCoordinateCovector A) w‖ := by
    dsimp only [y]
    rw [hback hz,hxi,hPhase (b.symm z) (b.map_target hz)]
    exact hMargin
  exact round4_actual_native_frame_reserve F hF (fun _ => host) e he W hW hJoint
    y (hSource (hGeom.2.2.2.2.2.2.1 hz)) z (hGeom.2.2.2.1 z hz).1
    A hTensor (actualIncrementCoordinateCovector A) rfl mu (B^2) hmu (sq_pos_of_pos hB)
    ((sq_le_sq₀ (norm_nonneg _) hB.le).mpr hAn) hMargin' v

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repairEntrance_native_original_low_budgets
#print axioms GlobalEmbedding.Continuation.repairEntrance_native_original_transverse_reserve
