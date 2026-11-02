import Initialization.Phase.CoefficientKernel
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The selector's literal old-coordinate hyperplane

The selector theorem supplies its second-form bound on `EuclideanSpace ℝ (Fin m)`.
The initialization theorem needs that bound on the kernel of the last coframe.
The equivalences here append or remove the literal last zero coordinate and
preserve the Euclidean norm.  Thus they introduce no hidden dimension-dependent
factor and also handle `m = 0` (the original application has `m ≥ 1`).
-/

noncomputable section

namespace GlobalEmbedding.Initialization

/-- The original last-coordinate covector, before pulling it back by the coframe. -/
abbrev lastCoordinateCovector (m : ℕ) : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] ℝ :=
  EuclideanSpace.proj (Fin.last m)

theorem lastCoordinateCovector_ne_zero (m : ℕ) : lastCoordinateCovector m ≠ 0 := by
  intro h
  have hv := congrArg (fun L : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] ℝ ↦
    L (EuclideanSpace.single (Fin.last m) 1)) h
  simp [lastCoordinateCovector] at hv

/-- The last-coordinate kernel is the original `m`-dimensional Euclidean space,
with the *same* l2 norm; the inverse literally appends a zero. -/
def coordinateHyperplaneEquiv (m : ℕ) :
    (lastCoordinateCovector m).ker ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m) where
  toLinearEquiv :=
    { toFun := fun v ↦ WithLp.toLp 2 (fun i : Fin m ↦ (v : EuclideanSpace ℝ (Fin (m + 1))) i.castSucc)
      invFun := fun (v : EuclideanSpace ℝ (Fin m)) ↦
        ⟨(WithLp.toLp 2 (Fin.snoc (fun i : Fin m ↦ v i) (0 : ℝ)) :
          EuclideanSpace ℝ (Fin (m + 1))), by
        change Fin.snoc (α := fun _ : Fin (m + 1) ↦ ℝ)
          (fun i : Fin m ↦ v i) (0 : ℝ) (Fin.last m) = 0
        simp⟩
      left_inv := by
        intro v
        apply Subtype.ext
        ext j
        refine Fin.lastCases ?_ (fun i ↦ ?_) j
        · have hv : (v : EuclideanSpace ℝ (Fin (m + 1))) (Fin.last m) = 0 := v.property
          simpa using hv.symm
        · simp
      right_inv := by
        intro v
        ext i
        simp
      map_add' := by
        intro v w
        ext i
        rfl
      map_smul' := by
        intro r v
        ext i
        rfl }
  norm_map' := by
    intro v
    change ‖WithLp.toLp 2 (fun i : Fin m ↦
      (v : EuclideanSpace ℝ (Fin (m + 1))) i.castSucc)‖ =
        ‖(v : EuclideanSpace ℝ (Fin (m + 1)))‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
      Fin.sum_univ_castSucc]
    have hv : (v : EuclideanSpace ℝ (Fin (m + 1))) (Fin.last m) = 0 := v.property
    simp [hv]

@[simp] theorem coordinateHyperplaneEquiv_apply (m : ℕ)
    (v : (lastCoordinateCovector m).ker) (i : Fin m) :
    coordinateHyperplaneEquiv m v i =
      (v : EuclideanSpace ℝ (Fin (m + 1))) i.castSucc := rfl

@[simp] theorem coordinateHyperplaneEquiv_symm_coe (m : ℕ)
    (v : EuclideanSpace ℝ (Fin m)) :
    ((coordinateHyperplaneEquiv m).symm v : EuclideanSpace ℝ (Fin (m + 1))) =
      WithLp.toLp 2 (Fin.snoc (fun i ↦ v i) 0) := rfl

/-- The actual inclusion of the selector's old coordinates, appending zero. -/
def oldCoordinateInjection (m : ℕ) : EuclideanSpace ℝ (Fin m) →L[ℝ]
    EuclideanSpace ℝ (Fin (m + 1)) :=
  (lastCoordinateCovector m).ker.subtypeL.comp
    (coordinateHyperplaneEquiv m).symm.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem oldCoordinateInjection_apply (m : ℕ) (v : EuclideanSpace ℝ (Fin m)) :
    oldCoordinateInjection m v = WithLp.toLp 2 (Fin.snoc (fun i ↦ v i) 0) := rfl

@[simp] theorem oldCoordinateInjection_single (m : ℕ) (i : Fin m) :
    oldCoordinateInjection m (EuclideanSpace.single i 1) =
      EuclideanSpace.single i.castSucc 1 := by
  rw [oldCoordinateInjection_apply]
  ext j
  refine Fin.lastCases ?_ (fun k ↦ ?_) j <;>
    simp [EuclideanSpace.single]

@[simp] theorem oldCoordinateInjection_norm (m : ℕ) (v : EuclideanSpace ℝ (Fin m)) :
    ‖oldCoordinateInjection m v‖ = ‖v‖ :=
  (coordinateHyperplaneEquiv m).symm.norm_map v

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual good hyperplane in a rescaled chart, expressed in the exact
coordinates used by the original selector's old second form. -/
def coframeOldHyperplaneEquiv {m : ℕ} (c : E ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1))) :
    (unitCoefficientCovector c (lastCoordinateCovector m)).ker ≃L[ℝ]
      EuclideanSpace ℝ (Fin m) :=
  (unitCoefficientKernelEquiv c (lastCoordinateCovector m)
    (lastCoordinateCovector_ne_zero m)).trans (coordinateHyperplaneEquiv m).toContinuousLinearEquiv

@[simp] theorem coframeOldHyperplaneEquiv_apply {m : ℕ}
    (c : E ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))
    (v : (unitCoefficientCovector c (lastCoordinateCovector m)).ker) (i : Fin m) :
    coframeOldHyperplaneEquiv c v i = c (v : E) i.castSucc := rfl

@[simp] theorem coframeOldHyperplaneEquiv_symm_coe {m : ℕ}
    (c : E ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1))) (v : EuclideanSpace ℝ (Fin m)) :
    ((coframeOldHyperplaneEquiv c).symm v : E) =
      c.symm (WithLp.toLp 2 (Fin.snoc (fun i ↦ v i) 0)) := rfl

/-- The coframe restricted to its actual good hyperplane is exactly the old
coordinate inclusion after the explicit drop-last-coordinate equivalence. -/
theorem coframeOldHyperplaneEquiv_coefficient {m : ℕ}
    (c : E ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1))) :
    c.toContinuousLinearMap.comp (unitCoefficientCovector c (lastCoordinateCovector m)).ker.subtypeL =
      (oldCoordinateInjection m).comp (coframeOldHyperplaneEquiv c).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro v
  exact (congrArg (fun w : (lastCoordinateCovector m).ker ↦
    (w : EuclideanSpace ℝ (Fin (m + 1))))
      ((coordinateHyperplaneEquiv m).symm_apply_apply
        (unitCoefficientKernelEquiv c (lastCoordinateCovector m)
          (lastCoordinateCovector_ne_zero m) v))).symm

/-- The original `L` in phase stability can be taken from the actual coframe
inverse; no separate kernel-equivalence bound is needed. -/
theorem coframeOldHyperplaneEquiv_inverse_norm_le {m : ℕ}
    (c : E ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1))) :
    ‖(coframeOldHyperplaneEquiv c).symm.toContinuousLinearMap‖ ≤
      ‖c.symm.toContinuousLinearMap‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  change ‖c.symm (WithLp.toLp 2 (Fin.snoc (fun i ↦ v i) 0))‖ ≤
    ‖c.symm.toContinuousLinearMap‖ * ‖v‖
  have h := c.symm.toContinuousLinearMap.le_opNorm
    (((coordinateHyperplaneEquiv m).symm v : (lastCoordinateCovector m).ker) :
      EuclideanSpace ℝ (Fin (m + 1)))
  have hv : ‖(((coordinateHyperplaneEquiv m).symm v : (lastCoordinateCovector m).ker) :
      EuclideanSpace ℝ (Fin (m + 1)))‖ = ‖v‖ :=
    (coordinateHyperplaneEquiv m).symm.norm_map v
  rw [hv] at h
  exact h

end GlobalEmbedding.Initialization
