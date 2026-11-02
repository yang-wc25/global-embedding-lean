import GlobalEmbedding.Paper.PlanarHopfAverageCalculus
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Genuine finite positive moment bumps on the native Hopf sphere

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines345–346.
Actual smooth bumps and compactness produce the finite family; it is not supplied as data.
-/

noncomputable section
open Set Filter Function MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace BigOperators

namespace GlobalEmbedding.Paper

variable {C : ℕ} [Fact (0 < C)]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The literal bump moment uses the square of the actual flat curvature cutoff. -/
def matrixOrbitBumpMoment (κ : PlanarHopfSphere C → ℝ) (A : PlanarHopfSphere C → E)
    (h : PlanarHopfSphere C → ℝ) : PlanarHopfSphere C → E :=
  orbitAverage planarHopfFlow (fun z ↦ (expNegInvGlue (κ z ^ 2) ^ 2 * h z ^ 2) • A z)

/-- Each actual smooth bump has a native smooth actual period moment. -/
theorem matrixOrbitBumpMoment_contMDiff (κ : PlanarHopfSphere C → ℝ)
    (A : PlanarHopfSphere C → E) (h : PlanarHopfSphere C → ℝ)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ)
    (hA : ContMDiff (planarHopfModel C) 𝓘(ℝ, E) ∞ A)
    (hh : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ h) :
    ContMDiff (planarHopfModel C) 𝓘(ℝ, E) ∞ (matrixOrbitBumpMoment κ A h) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact planarHopfAverage_contMDiff _
    ((((expNegInvGlue.contDiff.contMDiff.comp (hκ.pow 2)).pow 2).mul (hh.pow 2)).smul hA)

omit [Fact (0 < C)] [FiniteDimensional ℝ E] in
/-- The actual bump moment is invariant along the actual Hopf orbit. -/
theorem matrixOrbitBumpMoment_flow (κ : PlanarHopfSphere C → ℝ)
    (A : PlanarHopfSphere C → E) (h : PlanarHopfSphere C → ℝ)
    (t : ℝ) (z : PlanarHopfSphere C) :
    matrixOrbitBumpMoment κ A h (planarHopfFlow t z) = matrixOrbitBumpMoment κ A h z :=
  planarHopfAverage_flow _ z t

/-- A genuine orbit point with positive support gives an actual smooth positive-moment bump. -/
theorem matrix_positive_orbit_bump (κ : PlanarHopfSphere C → ℝ)
    (A : PlanarHopfSphere C → E)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ)
    (hA : ContMDiff (planarHopfModel C) 𝓘(ℝ, E) ∞ A)
    (z : PlanarHopfSphere C) (u : E) (t : ℝ)
    (hk : κ (planarHopfFlow t z) ≠ 0) (hp : 0 < ⟪A (planarHopfFlow t z), u⟫) :
    ∃ h : PlanarHopfSphere C → ℝ,
      ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ h ∧
        0 < ⟪matrixOrbitBumpMoment κ A h z, u⟫ := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let q := planarHopfFlow t z
  let O : Set (PlanarHopfSphere C) := {w | 0 < ⟪A w, u⟫}
  have hO : IsOpen O := isOpen_lt continuous_const (hA.continuous.inner continuous_const)
  obtain ⟨b, _, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport
    (I := planarHopfModel C) q).mem_iff.mp (hO.mem_nhds hp)
  refine ⟨b, b.contMDiff, ?_⟩
  let F : PlanarHopfSphere C → E :=
    fun w ↦ (expNegInvGlue (κ w ^ 2) ^ 2 * b w ^ 2) • A w
  have hF : Continuous F :=
    (((expNegInvGlue.contDiff (n := 0)).continuous.comp (hκ.continuous.pow 2)).pow 2 |>.mul
      (b.continuous.pow 2)).smul hA.continuous
  have hnonneg (w : PlanarHopfSphere C) : 0 ≤ ⟪F w, u⟫ := by
    by_cases hw : b w = 0
    · simp [F, hw]
    · have hi : 0 < ⟪A w, u⟫ := hb (subset_closure hw)
      simp only [F, real_inner_smul_left]
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hi.le
  have hRq : Continuous (fun s : ℝ ↦ planarHopfFlow s q) :=
    (planarHopfFlow_contMDiff C).continuous.comp (continuous_id.prodMk continuous_const)
  have hpos : 0 < ∫ s in (0 : ℝ)..1, ⟪F (planarHopfFlow s q), u⟫ := by
    apply intervalIntegral.integral_pos (by norm_num)
      ((hF.comp hRq).inner continuous_const).continuousOn (fun s _ ↦ hnonneg _)
    refine ⟨0, by norm_num, ?_⟩
    simp only [Function.comp_apply, planarHopfFlow_zero]
    simp only [F, b.eq_one, one_pow, mul_one, real_inner_smul_left]
    exact mul_pos (sq_pos_of_pos (expNegInvGlue.pos_of_pos (sq_pos_of_ne_zero hk))) hp
  have hFi : IntervalIntegrable (fun s ↦ F (planarHopfFlow s q)) volume 0 1 :=
    (hF.comp hRq).intervalIntegrable _ _
  have he : (∫ s in (0 : ℝ)..1, ⟪F (planarHopfFlow s q), u⟫) =
      ⟪∫ s in (0 : ℝ)..1, F (planarHopfFlow s q), u⟫ := by
    simpa only [innerSL_apply_apply, real_inner_comm] using
      (innerSL ℝ u).intervalIntegral_comp_comm hFi
  have hmoment : 0 < ⟪matrixOrbitBumpMoment κ A b q, u⟫ := by
    change 0 < ⟪∫ s in (0 : ℝ)..1, F (planarHopfFlow s q), u⟫
    rw [← he]
    exact hpos
  simpa only [q, matrixOrbitBumpMoment_flow] using hmoment

/-- Compactness selects actual global smooth bumps, including the constant one, with positive
actual moment support in every nonzero direction at every point of the native Hopf sphere. -/
theorem matrix_finite_positive_orbit_bumps (κ : PlanarHopfSphere C → ℝ)
    (A : PlanarHopfSphere C → E)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ)
    (hA : ContMDiff (planarHopfModel C) 𝓘(ℝ, E) ∞ A)
    (hspan : ∀ z, ∀ u : E, u ≠ 0 → ∃ t : ℝ,
      κ (planarHopfFlow t z) ≠ 0 ∧ 0 < ⟪A (planarHopfFlow t z), u⟫) :
    ∃ H : Finset (PlanarHopfSphere C → ℝ), (fun _ ↦ 1) ∈ H ∧
      (∀ h ∈ H, ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ h) ∧
      ∀ z, ∀ u : E, u ≠ 0 → ∃ h ∈ H, 0 < ⟪matrixOrbitBumpMoment κ A h z, u⟫ := by
  classical
  let I := {h : PlanarHopfSphere C → ℝ //
    ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ h}
  let V : I → Set (PlanarHopfSphere C × E) :=
    fun h ↦ {p | 0 < ⟪matrixOrbitBumpMoment κ A h.1 p.1, p.2⟫}
  have hV (h : I) : IsOpen (V h) := isOpen_lt continuous_const
    (((matrixOrbitBumpMoment_contMDiff κ A h.1 hκ hA h.2).continuous.comp
      continuous_fst).inner continuous_snd)
  let K : Set (PlanarHopfSphere C × E) := univ ×ˢ Metric.sphere (0 : E) 1
  have hK : IsCompact K := isCompact_univ.prod (isCompact_sphere (0 : E) 1)
  have hcover : K ⊆ ⋃ h : I, V h := by
    rintro ⟨z, u⟩ hp
    have hn : ‖u‖ = 1 := mem_sphere_zero_iff_norm.mp hp.2
    have hu : u ≠ 0 := by intro hh; simp [hh] at hn
    obtain ⟨t, hk, hi⟩ := hspan z u hu
    obtain ⟨h, hh, hpos⟩ := matrix_positive_orbit_bump κ A hκ hA z u t hk hi
    exact mem_iUnion.mpr ⟨⟨h, hh⟩, hpos⟩
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover V hV hcover
  let H := insert (fun _ : PlanarHopfSphere C ↦ (1 : ℝ)) (S.image Subtype.val)
  refine ⟨H, Finset.mem_insert_self _ _, ?_, ?_⟩
  · intro h hh
    rcases Finset.mem_insert.mp hh with hh | hh
    · subst h
      exact contMDiff_const
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hh
      exact i.2
  · intro z u hu
    have hn : ‖‖u‖⁻¹ • u‖ = 1 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu)]
    have hp : (z, ‖u‖⁻¹ • u) ∈ K := ⟨mem_univ _, mem_sphere_zero_iff_norm.mpr hn⟩
    obtain ⟨h, hh, hi⟩ := Set.mem_iUnion₂.mp (hS hp)
    refine ⟨h.1, Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨h, hh, rfl⟩), ?_⟩
    change 0 < ⟪matrixOrbitBumpMoment κ A h.1 z, ‖u‖⁻¹ • u⟫ at hi
    rw [real_inner_smul_right] at hi
    exact (mul_pos_iff_of_pos_left (inv_pos.mpr (norm_pos_iff.mpr hu))).mp hi

#print axioms matrix_finite_positive_orbit_bumps
#print axioms matrix_positive_orbit_bump
#print axioms matrixOrbitBumpMoment_contMDiff

end GlobalEmbedding.Paper
