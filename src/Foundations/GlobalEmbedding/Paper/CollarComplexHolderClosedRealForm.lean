import GlobalEmbedding.Paper.CollarHolderIsometricTargetMap
import GlobalEmbedding.Paper.CollarComplexHolderRealForm

/-!
# Actual closed real subspace and original real-ball isometry for complex little Hölder space

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 524–534. This constructs the exact real-form data required by the analytic IFT.
-/

open Set WithLp

namespace GlobalEmbedding.Paper

/-- The original real little Hölder space is linearly isometrically equivalent to the actual
closed real submodule of pointwise-real complex little Hölder functions. Actual continuous
real and imaginary coordinates into this submodule decompose every complex function.

Source: Proposition `prop:collar`, proof lines 524–534. Actual pointwise real inclusion and
coordinates already exist. The finite-value real inclusion is a linear isometry; compose it
with the orthogonal real coordinates and apply the actual isometric target-map theorem. Its
pointwise lift identifies it with the existing real inclusion, so the full original norms
agree. Take the actual range real submodule and restrict this isometry onto its range. Its
surjectivity gives the actual linear isometry equivalence. Compose the real/imaginary maps
with this inclusion into the range. The proved decomposition supplies their decomposition.
Finally range membership is exactly zero pointwise imaginary part, using injectivity of the
actual function map. Thus neither the real form nor its norm identification is assumed. -/
theorem collar_complex_holder_closed_real_form {a N k : ℕ} {α : ℝ} :
    ∃ R : Submodule ℝ (CollarComplexHolderSpace a N k α),
      IsClosed (R : Set (CollarComplexHolderSpace a N k α)) ∧
      ∃ (e : LittlePeriodicCAlphaFunction a N k α ≃ₗᵢ[ℝ] R)
        (r s : CollarComplexHolderSpace a N k α →L[ℝ] R),
        (∀ u y, collarComplexHolderFunction (e u : CollarComplexHolderSpace a N k α) y =
          toLp 2 (fun i : Fin N ↦ ((u : PeriodicCAlphaFunction a N k α).toFun y i : ℂ))) ∧
        (∀ f : CollarComplexHolderSpace a N k α,
          f ∈ R ↔ ∀ y i, (collarComplexHolderFunction f y i).im = 0) ∧
        (∀ f, (r f : CollarComplexHolderSpace a N k α) +
          Complex.I • (s f : CollarComplexHolderSpace a N k α) = f) ∧
        (∀ f y, collarComplexHolderFunction (r f : CollarComplexHolderSpace a N k α) y =
          toLp 2 (fun i : Fin N ↦ ((collarComplexHolderFunction f y i).re : ℂ))) ∧
        (∀ f y, collarComplexHolderFunction (s f : CollarComplexHolderSpace a N k α) y =
          toLp 2 (fun i : Fin N ↦ ((collarComplexHolderFunction f y i).im : ℂ))) := by
  obtain ⟨ι, r, s, hι, hr, hs, hd, _, _, hclosed⟩ :=
    collar_complex_holder_real_form (a := a) (N := N) (k := k) (α := α)
  let Jₗ : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℂ (Fin N) :=
    { toFun := fun x ↦ toLp 2 (fun i ↦ (x i : ℂ))
      map_add' := by intro x y; ext i; simp
      map_smul' := by intro c x; ext i; simp }
  have hJnorm (x : EuclideanSpace ℝ (Fin N)) : ‖Jₗ x‖ = ‖x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [EuclideanSpace.norm_sq_eq]
    change (∑ i : Fin N, ‖(x i : ℂ)‖ ^ 2) = ∑ i : Fin N, ‖x i‖ ^ 2
    simp only [Complex.norm_real]
  let J : EuclideanSpace ℝ (Fin N) →ₗᵢ[ℝ] EuclideanSpace ℂ (Fin N) :=
    { toLinearMap := Jₗ, norm_map' := hJnorm }
  let E := collarComplexHolderCoordinates N
  let K := E.toLinearIsometry.comp J
  obtain ⟨L, hL⟩ := collar_holder_isometric_target_map (a := a) (k := k) (α := α) K
  have hLf (u : LittlePeriodicCAlphaFunction a N k α) (y : EuclideanSpace ℝ (Fin a)) :
      collarComplexHolderFunction (a := a) (N := N) (k := k) (α := α) (L u) y =
        toLp 2 (fun i : Fin N ↦ ((u : PeriodicCAlphaFunction a N k α).toFun y i : ℂ)) := by
    change E.symm ((L u).val.toFun y) = _
    rw [congrFun (hL u) y]
    exact E.symm_apply_apply _
  have heq (u : LittlePeriodicCAlphaFunction a N k α) : ι u = L u := by
    apply collarComplexHolderFunction_injective
    funext y
    rw [hι, hLf]
  have hn (u : LittlePeriodicCAlphaFunction a N k α) : ‖ι u‖ = ‖u‖ := by
    rw [heq]
    exact L.norm_map u
  let R := ι.toLinearMap.range
  let j : LittlePeriodicCAlphaFunction a N k α →ₗᵢ[ℝ] R :=
    { toLinearMap := ι.toLinearMap.rangeRestrict, norm_map' := hn }
  have hj : Function.Surjective j := by
    rintro ⟨f, u, hu⟩
    exact ⟨u, Subtype.ext hu⟩
  let e := LinearIsometryEquiv.ofSurjective j hj
  let rR := j.toContinuousLinearMap.comp r
  let sR := j.toContinuousLinearMap.comp s
  have hR : IsClosed (R : Set (CollarComplexHolderSpace a N k α)) := hclosed
  have hmem (f : CollarComplexHolderSpace a N k α) :
      f ∈ R ↔ ∀ y i, (collarComplexHolderFunction f y i).im = 0 := by
    constructor
    · rintro ⟨u, rfl⟩
      intro y i
      change (collarComplexHolderFunction (ι u) y i).im = 0
      rw [hι]
      exact Complex.ofReal_im _
    · intro hz
      have hs0 : s f = 0 := by
        apply Subtype.ext
        apply periodicCAlpha_toFun_injective
        funext y
        rw [hs]
        ext i
        change (collarComplexHolderFunction f y i).im =
          (0 : PeriodicCAlphaFunction a N k α).toFun y i
        rw [(periodicCAlpha_pointwise_operations a N k α).1]
        exact hz y i
      refine ⟨r f, ?_⟩
      change ι (r f) = f
      have he := hd f
      simpa only [hs0, map_zero, smul_zero, add_zero] using he
  refine ⟨R, hR, e, rR, sR, ?_, hmem, ?_, ?_, ?_⟩
  · intro u y
    exact hι u y
  · intro f
    exact hd f
  · intro f y
    change collarComplexHolderFunction (ι (r f)) y = _
    rw [hι, hr]
  · intro f y
    change collarComplexHolderFunction (ι (s f)) y = _
    rw [hι, hs]

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_complex_holder_closed_real_form
