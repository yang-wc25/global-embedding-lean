import GlobalEmbedding.Paper.FreeHopfProductRetraction

/-!
# Native analytic inclusion and actual Hopf action

Source: `literature/parallelizable-stable-plus-one/main.tex`, prop:collar, lines516–540.
DAG: `collar-native-analytic-hopf-action`; exclusive bounded geometry owner W2.
All carriers, native atlases, inclusion and sphere action are the existing actual objects.
-/

noncomputable section
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- The existing native finite sphere product is genuinely real analytic. This is
the accepted arbitrary-order product atlas theorem at omega, using the actual
analytic sphere atlas from Mathlib. Source: prop:collar, lines516–540. -/
theorem collarHopfProduct_native_omega {a : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] : IsManifold (freeHopfModel C) ω (FreeHopfProduct C) :=
  free_finite_product_isManifold _ _ ω

/-- The same actual factor inclusion is analytic for its native sphere model,
including zero individual complex coordinates. Source: prop:collar, lines516–540. -/
theorem collarHopfSphere_inclusion_omega (C : ℕ) [Fact (0 < C)] :
    ContMDiff (planarHopfModel C) 𝓘(ℝ, PlanarHopfAmbient C) ω
      (fun z : PlanarHopfSphere C ↦ (z : PlanarHopfAmbient C)) :=
  contMDiff_coe_sphere

/-- The existing whole-product inclusion has native analytic regularity. Its
components are the actual analytic sphere inclusions after native coordinate
projections; the empty product is included. Source: prop:collar, lines516–540. -/
theorem collarHopfAmbientInclusion_omega {a : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] :
    ContMDiff (freeHopfModel C) 𝓘(ℝ, FreeHopfAmbientSpace C) ω
      (freeHopfAmbientInclusion C) := by
  apply contMDiff_pi_module_iff.2
  intro i
  have hp : ContMDiff (freeHopfModel C) (planarHopfModel (C i)) ω
      (fun x : FreeHopfProduct C ↦ x i) := by
    rw [show freeHopfModel C = ModelWithCorners.pi (fun i ↦ planarHopfModel (C i)) from
      (free_finite_product_model_eq _).symm]
    exact contMDiff_apply
  exact (collarHopfSphere_inclusion_omega (C i)).comp hp

/-- The literal ambient Hopf expression is jointly real analytic in all real
factor times and all actual ambient vectors, including zero vectors. There is no
second action definition: this is precisely the exponential scalar formula whose
restriction is the existing Hopf action. Source: prop:collar, lines516–540. -/
theorem collarHopfAmbientAction_contDiff_omega {a : ℕ} (C : Fin a → ℕ) :
    ContDiff ℝ ω (fun p : (Fin a → ℝ) × FreeHopfAmbientSpace C ↦
      fun i ↦ Complex.exp ((2 * Real.pi * p.1 i : ℝ) * Complex.I) • p.2 i) := by
  apply contDiff_pi.mpr
  intro i
  have ht : ContDiff ℝ ω (fun p : (Fin a → ℝ) × FreeHopfAmbientSpace C ↦ p.1 i) :=
    (contDiff_apply ℝ (fun _ : Fin a ↦ ℝ) i).comp contDiff_fst
  have he : ContDiff ℝ ω (fun p : (Fin a → ℝ) × FreeHopfAmbientSpace C ↦
      Complex.exp ((2 * Real.pi * p.1 i : ℝ) * Complex.I)) :=
    ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul ht)).mul contDiff_const).cexp
  exact he.smul ((contDiff_apply ℝ (fun i ↦ PlanarHopfAmbient (C i)) i).comp contDiff_snd)

/-- The literal analytic ambient expression restricts exactly to the already
defined original period-one product action; the 2pi multiplier is unchanged.
Source: prop:collar, lines516–540. -/
theorem collarHopfAmbientAction_inclusion {a : ℕ} (C : Fin a → ℕ)
    (t : Fin a → ℝ) (x : FreeHopfProduct C) :
    (fun i ↦ Complex.exp ((2 * Real.pi * t i : ℝ) * Complex.I) •
      freeHopfAmbientInclusion C x i) =
      freeHopfAmbientInclusion C (freeHopfRealAction C t x) := rfl

/-- The actual ambient value of the existing sphere-product action is jointly
native analytic, by composing the genuine ambient analytic expression with the
same analytic whole-product inclusion. Source: prop:collar, lines516–540. -/
theorem collarHopfRealAction_ambient_omega {a : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] :
    ContMDiff (𝓘(ℝ, Fin a → ℝ).prod (freeHopfModel C))
      𝓘(ℝ, FreeHopfAmbientSpace C) ω
      (fun p : (Fin a → ℝ) × FreeHopfProduct C ↦
        freeHopfAmbientInclusion C (freeHopfRealAction C p.1 p.2)) := by
  exact (collarHopfAmbientAction_contDiff_omega C).contMDiff.comp
    (contMDiff_fst.prodMk_space ((collarHopfAmbientInclusion_omega C).comp contMDiff_snd))

/-- The SAME existing simultaneous native sphere-product Hopf action is jointly
analytic. Restrict each actual ambient component by the genuine sphere codomain
criterion, then use the unchanged native finite product model. No analytic
action or desired equivariance is assumed. Source: prop:collar, lines516–540. -/
theorem collarHopfRealAction_omega {a : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] :
    ContMDiff (𝓘(ℝ, Fin a → ℝ).prod (freeHopfModel C)) (freeHopfModel C) ω
      (fun p : (Fin a → ℝ) × FreeHopfProduct C ↦ freeHopfRealAction C p.1 p.2) := by
  have ha := collarHopfRealAction_ambient_omega C
  rw [show freeHopfModel C = ModelWithCorners.pi (fun i ↦ planarHopfModel (C i)) from
    (free_finite_product_model_eq _).symm] at ha ⊢
  have : IsManifold (ModelWithCorners.pi (fun i ↦ planarHopfModel (C i))) ω
      (FreeHopfProduct C) := by
    rw [← show freeHopfModel C = ModelWithCorners.pi (fun i ↦ planarHopfModel (C i)) from
      (free_finite_product_model_eq _).symm]
    exact collarHopfProduct_native_omega C
  apply contMDiff_pi_iff.2
  intro i
  apply ContMDiff.codRestrict_sphere
  exact (contMDiff_pi_module_iff.mp ha) i

end GlobalEmbedding.Paper
