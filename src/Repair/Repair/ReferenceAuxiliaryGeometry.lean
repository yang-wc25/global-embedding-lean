import Repair.EndpointUniformGeometry
import Probes.ActualIncrementChartMarginReserve
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! The auxiliary tangent norm is part of the fixed geometry.  Its chart
comparison is chosen before any reference map.  Continuity in the basepoint
is explicit: pointwise RiemannianBundle data alone do not imply this bound. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold IsManifold Set Function Filter Bundle
open scoped ContDiff Topology
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
namespace GlobalEmbedding.Continuation

/-- A locally upper bounded real function is bounded on a compact set.
No continuity of the function itself is assumed. -/
theorem repair_auxiliary_compact_bound {X : Type*} [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K) (f : X → ℝ)
    (hLocal : ∀ x ∈ K, ∃ C : ℝ, ∀ᶠ y in 𝓝 x, f y ≤ C) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, f x ≤ C := by
  classical
  have hOpen : ∀ x : K, ∃ C : ℝ, ∃ U : Set X,
      IsOpen U ∧ x.1 ∈ U ∧ ∀ y ∈ U, f y ≤ C := by
    intro x
    obtain ⟨C,hC⟩ := hLocal x x.2
    obtain ⟨U,hU,hOpen,hx⟩ := mem_nhds_iff.mp hC
    exact ⟨C,U,hOpen,hx,fun y hy => hU hy⟩
  choose C U hOpen hx hBound using hOpen
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover U hOpen (by
    intro x hxK
    exact mem_iUnion.mpr ⟨⟨x,hxK⟩,hx ⟨x,hxK⟩⟩)
  refine ⟨1+∑ x ∈ s, max 0 (C x), by positivity, ?_⟩
  intro x hxK
  obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp (hs hxK)
  have hsum : max 0 (C y) ≤ ∑ z ∈ s, max 0 (C z) :=
    Finset.single_le_sum (fun z _ => le_max_left 0 (C z)) hy
  exact (hBound y x hxy).trans ((le_max_right 0 (C y)).trans (by linarith))

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "I" => 𝓘(ℝ,D)


/-- A genuine source derivative into Euclidean space is locally bounded in
the fixed continuous auxiliary tangent norm. -/
theorem repair_auxiliary_mfderiv_locally_bounded
    [IsContinuousRiemannianBundle D (TangentSpace I : M → Type _)]
    (f : M → D) (x : M) (hf : ContMDiffAt I I ∞ f x) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ y in 𝓝 x, ‖mfderiv I I f y‖ ≤ C := by
  let H : M → D →L[ℝ] D := inTangentCoordinates I I id f (mfderiv I I f) x
  have hH : ContinuousAt H x := (hf.mfderiv_const (m := 0) (by simp)).continuousAt
  have hHb : ∀ᶠ y in 𝓝 x, ‖H y‖ < ‖H x‖+1 :=
    hH.norm.eventually_lt_const (lt_add_one _)
  obtain ⟨C,hC,hCb⟩ := eventually_norm_mfderiv_extChartAt_lt I x
  refine ⟨(‖H x‖+1)*C, mul_pos (by positivity) hC, ?_⟩
  filter_upwards [hHb,hCb,chart_source_mem_nhds D x] with y hy hCy hys
  have hRep : H y = (mfderiv I I f y).comp
      (mfderivWithin I I (extChartAt I x).symm (range I) (extChartAt I x y)) := by
    have hh := inTangentCoordinates_eq_mfderiv_comp_abuse
      («I» := I) (I' := I) (f := id) (g := f) (ϕ := mfderiv I I f)
      (x₀ := x) (x := y) hys (by simp)
    simpa only [H,extChartAt_self_eq,modelWithCornersSelf_coe,mfderiv_id,ContinuousLinearMap.id_comp,
      id_eq] using hh
  have hFactor : mfderiv I I f y = (H y).comp (mfderiv I I (extChartAt I x) y) := by
    rw [hRep,ContinuousLinearMap.comp_assoc,
      mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (by simpa using hys),
      ContinuousLinearMap.comp_id]
  rw [hFactor]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul hy.le hCy.le (norm_nonneg _) (by positivity))

/-- A fixed original chart has a uniform auxiliary-norm derivative bound
on its actual compact coordinate sampling set. -/
theorem repair_auxiliary_chart_bound
    [IsContinuousRiemannianBundle D (TangentSpace I : M → Type _)]
    (e : OpenPartialHomeomorph M D) (he : e ∈ maximalAtlas I ∞ M)
    (K : Set D) (hK : IsCompact K) (hTarget : K ⊆ e.target) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ K, ‖mfderiv I I e (e.symm y)‖ ≤ C := by
  have hCompact : IsCompact (e.symm '' K) := hK.image_of_continuousOn
    (e.symm.continuousOn.mono hTarget)
  obtain ⟨C,hC,hBound⟩ := repair_auxiliary_compact_bound (e.symm '' K) hCompact
    (fun x => ‖mfderiv I I e x‖) (by
      intro x hx
      obtain ⟨y,hy,rfl⟩ := hx
      obtain ⟨C,_,hB⟩ := repair_auxiliary_mfderiv_locally_bounded e (e.symm y)
        (contMDiffAt_of_mem_maximalAtlas he (e.map_target (hTarget hy)))
      exact ⟨C,hB⟩)
  exact ⟨C,hC,fun y hy => hBound _ ⟨y,hy,rfl⟩⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_auxiliary_mfderiv_locally_bounded
#print axioms GlobalEmbedding.Continuation.repair_auxiliary_chart_bound
