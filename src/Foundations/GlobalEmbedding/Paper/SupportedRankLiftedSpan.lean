import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Prod
import Mathlib.Basic.Real.Basic

/-!
# The independent t-direction in the original legal kernel-variation span

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of
`prop:supported-rank`, lines 1021–1027. This module only performs the actual
`ξ=z+te` direct-sum bookkeeping. The actual quadratic raw-span and evaluation-span
theorems are supplied by W4's sole local-syzygy provider.
-/

namespace GlobalEmbedding.Paper

variable {U K : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup K] [Module ℝ K]

/-- The literal lifted column `k↦a(z)(k)•(z,t)` in the original fixed splitting.
Source: `prop:supported-rank`, the maps `Q↦ξ Q(z,z)`. -/
def supportedRankLiftedColumn (a : U → Module.Dual ℝ K) (z : U) (t : ℝ) :
    K →ₗ[ℝ] U × ℝ :=
  (a z).smulRight (z, t)

/-- The actual lifted-column span, with all original real t values.
Source: `prop:supported-rank`, legal span before the support-motion quotient. -/
def supportedRankLiftedSpan (a : U → Module.Dual ℝ K) (Ω : Set U) :
    Submodule ℝ (K →ₗ[ℝ] U × ℝ) :=
  Submodule.span ℝ (Set.range fun p : Ω × ℝ ↦ supportedRankLiftedColumn a p.1 p.2)

private theorem liftedColumn_zero (a : U → Module.Dual ℝ K) (z : U) :
    supportedRankLiftedColumn a z 0 = ((a z).smulRight z).prod 0 := by
  ext k <;> simp [supportedRankLiftedColumn]

private theorem liftedColumn_one_sub_zero (a : U → Module.Dual ℝ K) (z : U) :
    supportedRankLiftedColumn a z 1 - supportedRankLiftedColumn a z 0 =
      (0 : K →ₗ[ℝ] U).prod (a z) := by
  ext k <;> simp [supportedRankLiftedColumn]

/-- The actual lifted span contains the raw U-valued span and an independent full
copy of `K*`, once the same actual evaluation functionals span `K*`.

Proof: `t=0` gives each raw column with zero vertical component. Subtracting `t=0`
from `t=1` gives the vertical evaluation functional. Span induction gives every raw
and every vertical vector. Their literal product map is injective, so native finite
dimension monotonicity and the product/dual dimension formulas give the sum bound.
The evaluation-span hypothesis is an internal input proved for the actual quadratic
family by the sole syzygy provider, never an added original-target hypothesis.
Source: `prop:supported-rank`, lines 1021–1027. -/
theorem supportedRankLiftedSpan_finrank [FiniteDimensional ℝ U] [FiniteDimensional ℝ K]
    (a : U → Module.Dual ℝ K) (Ω : Set U)
    (ha : Submodule.span ℝ (a '' Ω) = ⊤) :
    Module.finrank ℝ (Submodule.span ℝ ((fun z : U ↦ (a z).smulRight z) '' Ω)) +
      Module.finrank ℝ K ≤ Module.finrank ℝ (supportedRankLiftedSpan a Ω) := by
  let R := Submodule.span ℝ ((fun z : U ↦ (a z).smulRight z) '' Ω)
  let L := supportedRankLiftedSpan a Ω
  have hcolumn (z : U) (hz : z ∈ Ω) (t : ℝ) : supportedRankLiftedColumn a z t ∈ L :=
    Submodule.subset_span ⟨(⟨z, hz⟩, t), rfl⟩
  have hraw : ∀ f : K →ₗ[ℝ] U, f ∈ R → f.prod (0 : Module.Dual ℝ K) ∈ L := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
        obtain ⟨z, hz, rfl⟩ := hf
        rw [← liftedColumn_zero]
        exact hcolumn z hz 0
    | zero =>
        change (0 : K →ₗ[ℝ] U × ℝ) ∈ L
        exact L.zero_mem
    | add f g hf hg ihf ihg =>
        convert L.add_mem ihf ihg using 1
        ext k <;> simp
    | smul c f hf ih =>
        convert L.smul_mem c ih using 1
        ext k <;> simp
  have hvertical : ∀ μ : Module.Dual ℝ K, (0 : K →ₗ[ℝ] U).prod μ ∈ L := by
    intro μ
    have hμ : μ ∈ Submodule.span ℝ (a '' Ω) := by rw [ha]; trivial
    induction hμ using Submodule.span_induction with
    | mem μ hμ =>
        obtain ⟨z, hz, rfl⟩ := hμ
        rw [← liftedColumn_one_sub_zero]
        exact L.sub_mem (hcolumn z hz 1) (hcolumn z hz 0)
    | zero =>
        change (0 : K →ₗ[ℝ] U × ℝ) ∈ L
        exact L.zero_mem
    | add μ η hμ hη ihμ ihη =>
        convert L.add_mem ihμ ihη using 1
        ext k <;> simp
    | smul c μ hμ ih =>
        convert L.smul_mem c ih using 1
        ext k <;> simp
  let j : (R × Module.Dual ℝ K) →ₗ[ℝ] (K →ₗ[ℝ] U × ℝ) :=
    { toFun := fun p ↦ (p.1 : K →ₗ[ℝ] U).prod p.2
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hj : Function.Injective j := by
    intro x y h
    apply Prod.ext
    · apply Subtype.ext
      ext k
      exact congrArg (fun f : K →ₗ[ℝ] U × ℝ ↦ (f k).1) h
    · ext k
      exact congrArg (fun f : K →ₗ[ℝ] U × ℝ ↦ (f k).2) h
  have hjmem : ∀ p, j p ∈ L := by
    intro p
    have heq : j p = (p.1 : K →ₗ[ℝ] U).prod 0 + (0 : K →ₗ[ℝ] U).prod p.2 := by
      apply LinearMap.ext
      intro k
      change ((p.1 : K →ₗ[ℝ] U) k, p.2 k) =
        ((p.1 : K →ₗ[ℝ] U) k, 0) + (0, p.2 k)
      simp
    rw [heq]
    exact L.add_mem (hraw p.1 p.1.property) (hvertical p.2)
  let jL := j.codRestrict L hjmem
  have hjL : Function.Injective jL := by
    intro x y h
    exact hj (congrArg (fun z : L ↦ z.val) h)
  have hdim := LinearMap.finrank_le_finrank_of_injective hjL
  simpa only [Module.finrank_prod, Subspace.dual_finrank_eq] using hdim

#print axioms supportedRankLiftedColumn
#print axioms supportedRankLiftedSpan
#print axioms supportedRankLiftedSpan_finrank

end GlobalEmbedding.Paper
