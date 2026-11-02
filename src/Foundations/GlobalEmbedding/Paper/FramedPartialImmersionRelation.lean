import GlobalEmbedding.Paper.FramedDistribution
import GlobalEmbedding.Paper.PlanarJetFieldEvaluation
import Mathlib.LinearAlgebra.Dimension.Constructions
import GlobalEmbedding.Paper.FramedPartialImmersionLinear
import GlobalEmbedding.External.SphereEversion.Global.Relation

/-!
# The genuine framed partial-immersion relation

Source: `literature/parallelizable-stable-plus-one/main.tex`, Lemma `lem:planar`.
The relation tests the actual derivative on the prescribed tangent subspace.
-/

open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {b : ℕ}

/-- The framed fiber has its prescribed rank, including rank zero. -/
theorem framedPartial_fiber_finrank (V : FramedDistribution I (M := M) b) (x : M) :
    Module.finrank ℝ (FramedDistribution.fiber I V x) = b := by
  simpa [FramedDistribution.fiber] using! finrank_span_eq_card (V.independent x)

/-- Injectivity on the framed subspace is exactly independence of the frame images. -/
theorem framedPartial_injective_iff (V : FramedDistribution I (M := M) b) (x : M)
    (φ : TangentSpace I x →L[ℝ] F) :
    Function.Injective (φ.comp (FramedDistribution.fiber I V x).subtypeL) ↔
      LinearIndependent ℝ (fun i ↦ φ (V.frame i x)) := by
  constructor
  · intro h
    apply (V.independent x).map_injOn φ.toLinearMap
    intro u hu v hv huv
    exact congrArg Subtype.val (h (a₁ := ⟨u, hu⟩) (a₂ := ⟨v, hv⟩) huv)
  · intro h
    have hi := φ.toLinearMap.injOn_of_disjoint_ker le_rfl
      (Submodule.range_ker_disjoint (f := φ.toLinearMap) h)
    intro u v huv
    apply Subtype.ext
    exact hi u.property v.property huv

/-- The actual one-jet relation of injectivity on the framed distribution. -/
def framedPartialImmersionRelation (V : FramedDistribution I (M := M) b) :
    RelMfld I M 𝓘(ℝ, F) F :=
  {σ | Function.Injective (σ.2.comp (FramedDistribution.fiber I V σ.1.1).subtypeL)}

/-- The framed partial-immersion condition is an open condition on genuine one-jets. -/
theorem framedPartialImmersionRelation_open (V : FramedDistribution I (M := M) b) :
    IsOpen (framedPartialImmersionRelation (F := F) V) := by
  have hc : Continuous fun σ : OneJetBundle I M 𝓘(ℝ, F) F ↦
      fun i : Fin b ↦ NormedSpace.fromTangentSpace σ.1.2 (σ.2 (V.frame i σ.1.1)) :=
    continuous_pi fun i ↦ (contMDiff_oneJetFieldEval (F := F) (V.frame i)).continuous
  convert (isOpen_setOfPred_linearIndependent (𝕜 := ℝ) (E := F) (ι := Fin b)).preimage hc using 1
  ext σ
  change Function.Injective (σ.2.comp (FramedDistribution.fiber I V σ.1.1).subtypeL) ↔
    LinearIndependent ℝ (fun i ↦ NormedSpace.fromTangentSpace σ.1.2 (σ.2 (V.frame i σ.1.1)))
  constructor
  · intro hi
    apply (framedPartial_injective_iff V σ.1.1
      ((NormedSpace.fromTangentSpace σ.1.2).toContinuousLinearMap.comp σ.2)).mp
    intro u v huv
    exact hi ((NormedSpace.fromTangentSpace σ.1.2).injective huv)
  · intro hi
    have hi' := (framedPartial_injective_iff V σ.1.1
      ((NormedSpace.fromTangentSpace σ.1.2).toContinuousLinearMap.comp σ.2)).mpr hi
    intro u v huv
    exact hi' (congrArg (NormedSpace.fromTangentSpace σ.1.2) huv)

set_option backward.isDefEq.respectTransparency false in
/-- The native framed relation is ample when its prescribed rank is below target dimension. -/
theorem framedPartialImmersionRelation_ample [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (V : FramedDistribution I (M := M) b) (h : b < Module.finrank ℝ F) :
    (framedPartialImmersionRelation (F := F) V).Ample := by
  rw [RelMfld.ample_iff]
  intro σ p hσ
  have hr : Module.finrank ℝ (FramedDistribution.fiber I V σ.1.1) < Module.finrank ℝ F := by
    rwa [framedPartial_fiber_finrank V]
  have : FiniteDimensional ℝ (TangentSpace I σ.1.1) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  change AmpleSet {w : F | Function.Injective
    ((p.update σ.2 w).comp (FramedDistribution.fiber I V σ.1.1).subtypeL)}
  exact framedPartial_slice_ample (E := TangentSpace I σ.1.1) p
    (FramedDistribution.fiber I V σ.1.1) hr hσ

end GlobalEmbedding.Paper
