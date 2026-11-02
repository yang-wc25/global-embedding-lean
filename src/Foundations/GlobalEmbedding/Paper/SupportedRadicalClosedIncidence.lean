import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Maps.Proper.Basic

/-!+# Closedness of the actual common-radical incidence

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:supported-rank`,
lines 1005–1006. Normalize a nonzero radical vector to the actual unit sphere, whose compactness
makes the projection of the closed zero incidence closed. Actual continuous kernel-block
families can then pull this set back. No supported-locus closedness is assumed.
-/

open Set Metric

namespace GlobalEmbedding.Paper

variable {K V : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- An actual common radical vector with unit norm, for the actual operator family.
Source: `prop:supported-rank`, compact normalization of the common radical line. -/
def HasUnitCommonRadical (Q : K →L[ℝ] (V →L[ℝ] V)) : Prop :=
  ∃ v : V, ‖v‖ = 1 ∧ ∀ k : K, Q k v = 0

/-- A nonzero common radical vector can be normalized without changing any kernel equation.
Source: `prop:supported-rank`, unit representatives of radical lines. -/
theorem hasUnitCommonRadical_iff (Q : K →L[ℝ] (V →L[ℝ] V)) :
    HasUnitCommonRadical Q ↔ ∃ v : V, v ≠ 0 ∧ ∀ k : K, Q k v = 0 := by
  constructor
  · rintro ⟨v, hv, hk⟩
    refine ⟨v, ?_, hk⟩
    intro hzero
    simp [hzero] at hv
  · rintro ⟨v, hv, hk⟩
    refine ⟨‖v‖⁻¹ • v, ?_, ?_⟩
    · rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)
    · intro k
      simp only [map_smul, hk, smul_zero]

/-- The actual unit-radical locus is closed in finite-dimensional source geometry.
Proof: the common-zero incidence on the compact unit sphere is closed, and projection along
that sphere is a closed map. Source: `prop:supported-rank`, relative closedness. -/
theorem isClosed_hasUnitCommonRadical [FiniteDimensional ℝ V] :
    IsClosed {Q : K →L[ℝ] (V →L[ℝ] V) | HasUnitCommonRadical Q} := by
  let S := sphere (0 : V) 1
  have hS : IsCompact S := isCompact_sphere 0 1
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let T : Set ((K →L[ℝ] (V →L[ℝ] V)) × S) :=
    {p | ∀ k : K, p.1 k p.2.1 = 0}
  have hT : IsClosed T := by
    change IsClosed {p : (K →L[ℝ] (V →L[ℝ] V)) × S | ∀ k : K, p.1 k p.2.1 = 0}
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro k
    apply isClosed_eq _ continuous_const
    exact (continuous_fst.clm_apply continuous_const).clm_apply
      (continuous_subtype_val.comp continuous_snd)
  have hproj := isClosedMap_fst_of_compactSpace T hT
  convert hproj using 1
  ext Q
  constructor
  · rintro ⟨v, hv, hk⟩
    refine ⟨(Q, ⟨v, ?_⟩), hk, rfl⟩
    simpa [S, mem_sphere_iff_norm] using hv
  · rintro ⟨⟨Q', v⟩, hk, hQ⟩
    change Q' = Q at hQ
    subst Q'
    exact ⟨v.1, by simpa only [S, mem_sphere_iff_norm, sub_zero] using v.2, hk⟩

/-- Every actual continuous parameterized operator family inherits closed common-radical
incidence. Source: `prop:supported-rank`, local onto-kernel graph coordinates. -/
theorem isClosed_hasUnitCommonRadical_preimage [FiniteDimensional ℝ V]
    {X : Type*} [TopologicalSpace X] (Q : X → K →L[ℝ] (V →L[ℝ] V))
    (hQ : Continuous Q) : IsClosed {x : X | HasUnitCommonRadical (Q x)} :=
  isClosed_hasUnitCommonRadical.preimage hQ

end GlobalEmbedding.Paper
