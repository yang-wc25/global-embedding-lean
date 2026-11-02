import GlobalEmbedding.Paper.CollarComplexHolderSpace

/-!
# The actual real form in the complex little Hölder space

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. The real inclusion and real/imaginary projections act on actual target
values and on the original little closures, rather than on an assumed abstract real form.
-/

open Set WithLp

namespace GlobalEmbedding.Paper

/-- The actual complex little Hölder space has the existing real little space as a closed
real form, with continuous actual pointwise inclusion, real and imaginary projections.

Source: Proposition `prop:collar`, complexification in the joint-analyticity argument.
The finite-dimensional real-linear target maps ofReal, Re and Im are continuous. Express
them in the orthogonal real coordinates and apply the proved actual Holder target-map theorem.
Their lift identities give exactly the corresponding pointwise maps on actual functions.
The usual complex coordinate identities therefore give decomposition and its uniqueness by
underlying-function injectivity. Re∘inclusion is the identity. The inclusion range is exactly
the fixed set of the continuous projection inclusion∘Re, hence is closed. Every carrier here
is the actual original smooth closure, with no extra completeness or real-form assumption.
-/
theorem collar_complex_holder_real_form {a N k : ℕ} {α : ℝ} :
    ∃ (ι : LittlePeriodicCAlphaFunction a N k α →L[ℝ] CollarComplexHolderSpace a N k α)
      (r s : CollarComplexHolderSpace a N k α →L[ℝ]
        LittlePeriodicCAlphaFunction a N k α),
      (∀ u x, collarComplexHolderFunction (ι u) x =
        toLp 2 (fun i : Fin N ↦ ((u : PeriodicCAlphaFunction a N k α).toFun x i : ℂ))) ∧
      (∀ f x, (r f : PeriodicCAlphaFunction a N k α).toFun x =
        toLp 2 (fun i : Fin N ↦ (collarComplexHolderFunction f x i).re)) ∧
      (∀ f x, (s f : PeriodicCAlphaFunction a N k α).toFun x =
        toLp 2 (fun i : Fin N ↦ (collarComplexHolderFunction f x i).im)) ∧
      (∀ f, ι (r f) + Complex.I • ι (s f) = f) ∧
      (∀ f u v, ι u + Complex.I • ι v = f → u = r f ∧ v = s f) ∧
      Function.Injective ι ∧ IsClosed (Set.range ι) := by
  let J : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℂ (Fin N) :=
    ({ toFun := fun x ↦ toLp 2 (fun i ↦ (x i : ℂ))
       map_add' := by intro x y; ext i; simp
       map_smul' := by intro c x; ext i; simp } :
      EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℂ (Fin N)).toContinuousLinearMap
  let R : EuclideanSpace ℂ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
    ({ toFun := fun x ↦ toLp 2 (fun i ↦ (x i).re)
       map_add' := by intro x y; ext i; simp
       map_smul' := by intro c x; ext i; simp } :
      EuclideanSpace ℂ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)).toContinuousLinearMap
  let S : EuclideanSpace ℂ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
    ({ toFun := fun x ↦ toLp 2 (fun i ↦ (x i).im)
       map_add' := by intro x y; ext i; simp
       map_smul' := by intro c x; ext i; simp } :
      EuclideanSpace ℂ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)).toContinuousLinearMap
  let e := collarComplexHolderCoordinates N
  obtain ⟨_, ι₀, _, _, hι, _⟩ := collar_holder_target_map
    (a := a) (k := k) (α := α) (e.toLinearIsometry.toContinuousLinearMap.comp J)
  obtain ⟨_, r₀, _, _, hr, _⟩ := collar_holder_target_map
    (a := a) (k := k) (α := α) (R.comp e.symm.toLinearIsometry.toContinuousLinearMap)
  obtain ⟨_, s₀, _, _, hs, _⟩ := collar_holder_target_map
    (a := a) (k := k) (α := α) (S.comp e.symm.toLinearIsometry.toContinuousLinearMap)
  let ι : LittlePeriodicCAlphaFunction a N k α →L[ℝ] CollarComplexHolderSpace a N k α := ι₀
  let r : CollarComplexHolderSpace a N k α →L[ℝ]
      LittlePeriodicCAlphaFunction a N k α := r₀
  let s : CollarComplexHolderSpace a N k α →L[ℝ]
      LittlePeriodicCAlphaFunction a N k α := s₀
  have hιfun (u : LittlePeriodicCAlphaFunction a N k α) (x : EuclideanSpace ℝ (Fin a)) :
      collarComplexHolderFunction (ι u) x =
        toLp 2 (fun i : Fin N ↦ ((u : PeriodicCAlphaFunction a N k α).toFun x i : ℂ)) := by
    change e.symm ((ι₀ u).val.toFun x) = _
    rw [hι u]
    exact e.symm_apply_apply _
  have hrfun (f : CollarComplexHolderSpace a N k α) (x : EuclideanSpace ℝ (Fin a)) :
      (r f : PeriodicCAlphaFunction a N k α).toFun x =
        toLp 2 (fun i : Fin N ↦ (collarComplexHolderFunction f x i).re) :=
    congrFun (hr f) x
  have hsfun (f : CollarComplexHolderSpace a N k α) (x : EuclideanSpace ℝ (Fin a)) :
      (s f : PeriodicCAlphaFunction a N k α).toFun x =
        toLp 2 (fun i : Fin N ↦ (collarComplexHolderFunction f x i).im) :=
    congrFun (hs f) x
  have hdecomp (f : CollarComplexHolderSpace a N k α) : ι (r f) + Complex.I • ι (s f) = f := by
    apply collarComplexHolderFunction_injective
    rw [collarComplexHolderFunction_add, collarComplexHolderFunction_smul]
    funext x
    rw [Pi.add_apply, Pi.smul_apply, hιfun, hιfun, hrfun, hsfun]
    ext i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    simpa only [mul_comm Complex.I] using
      Complex.re_add_im (collarComplexHolderFunction f x i)
  have hunique (f : CollarComplexHolderSpace a N k α)
      (u v : LittlePeriodicCAlphaFunction a N k α)
      (h : ι u + Complex.I • ι v = f) : u = r f ∧ v = s f := by
    have hf (x : EuclideanSpace ℝ (Fin a)) (i : Fin N) :
        (((u : PeriodicCAlphaFunction a N k α).toFun x i : ℝ) : ℂ) + Complex.I *
          (((v : PeriodicCAlphaFunction a N k α).toFun x i : ℝ) : ℂ) =
        collarComplexHolderFunction f x i := by
      have heq := congrArg (fun z ↦ collarComplexHolderFunction z x i) h
      rw [collarComplexHolderFunction_add, collarComplexHolderFunction_smul] at heq
      simpa only [Pi.add_apply, Pi.smul_apply, hιfun, PiLp.add_apply,
        PiLp.smul_apply, ofLp_toLp, smul_eq_mul] using heq
    constructor
    · apply Subtype.ext
      apply periodicCAlpha_toFun_injective
      funext x
      rw [hrfun]
      ext i
      simpa using congrArg Complex.re (hf x i)
    · apply Subtype.ext
      apply periodicCAlpha_toFun_injective
      funext x
      rw [hsfun]
      ext i
      simpa using congrArg Complex.im (hf x i)
  have hrι (u : LittlePeriodicCAlphaFunction a N k α) : r (ι u) = u := by
    apply Subtype.ext
    apply periodicCAlpha_toFun_injective
    funext x
    rw [hrfun, hιfun]
    ext i
    simp
  have hinj : Function.Injective ι := by
    intro u v huv
    simpa only [hrι] using congrArg r huv
  have hrange : Set.range ι = {f | ι (r f) = f} := by
    ext f
    constructor
    · rintro ⟨u, rfl⟩
      exact congrArg ι (hrι u)
    · intro hf
      exact ⟨r f, hf⟩
  refine ⟨ι, r, s, hιfun, hrfun, hsfun, hdecomp, hunique, hinj, ?_⟩
  rw [hrange]
  exact isClosed_eq (ι.continuous.comp r.continuous) continuous_id

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_complex_holder_real_form
