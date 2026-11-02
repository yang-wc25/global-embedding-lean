import GlobalEmbedding.External.SphereEversion.Global.Gromov

/-!
# Genuine smooth-map extraction from the open ample maps h-principle

Source: the maps h-principle in the pinned SphereEversion provider, applied with empty
relative set and constant positive tolerance. Used for the first assertion of `lem:planar`.
-/

open scoped Topology Manifold ContDiff

namespace GlobalEmbedding.Paper

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Actual holonomic map extraction, with no compactness or nonemptiness assumption. -/
theorem openAmpleMap_exists_smooth_solution
    (R : RelMfld I M 𝓘(ℝ, F) F) (hRopen : IsOpen R) (hRample : R.Ample)
    (S : FormalSol R) :
    ∃ f : M → F, ContMDiff I 𝓘(ℝ, F) ∞ f ∧
      ∀ x, oneJetExt I 𝓘(ℝ, F) f x ∈ R := by
  have hh := hRample.satisfiesHPrinciple hRopen (A := ∅) (δ := fun _ ↦ 1)
    isClosed_empty (fun _ ↦ zero_lt_one) continuous_const
  obtain ⟨T, _, hT, _, _⟩ := hh S (by simp)
  refine ⟨(T 1).bs, (T 1).contMDiff_bs, fun x ↦ ?_⟩
  rw [OneJetSec.isHolonomicAt_iff.mp (hT x)]
  exact (T 1).is_sol x

end GlobalEmbedding.Paper
