import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-!
# Lift pointwise multilinear coefficients into an actual normed function space

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. Constructing a Banach-valued coefficient requires actual multilinearity
and a norm bound in that function space, in addition to existence of individual smooth slices.
-/

namespace GlobalEmbedding.Paper

/-- Algebraic pointwise multilinearity, actual slice lifts and a uniform product-norm estimate
construct a continuous multilinear coefficient in the target normed function space.

Source: Proposition `prop:collar`, proof lines 530–534, coefficient power-series construction.
Choose a lift in H for each parameter tuple. Injectivity of the underlying-function linear map
makes that choice unique; applying it to each additive and scalar identity transports pointwise
multilinearity to H. The supplied product-norm bound is then precisely the bound required by
MultilinearMap.mkContinuous, and its norm estimate gives operator norm at most K. Completeness
is not required for constructing these coefficients, only later for summing the resulting series.
The slice existence and norm estimate must be provided from the actual coefficient functions;
no preexisting continuous multilinear H-valued map is assumed.
-/
theorem collar_multilinear_coefficient_lift
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {n : ℕ} {E : Fin n → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    {H V X : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    [AddCommGroup V] [Module 𝕜 V]
    (ι : H →ₗ[𝕜] (X → V)) (hι : Function.Injective ι)
    (G : MultilinearMap 𝕜 E (X → V))
    (hlift : ∀ m : (i : Fin n) → E i, ∃ h : H, ι h = G m)
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ (m : (i : Fin n) → E i) (h : H), ι h = G m →
      ‖h‖ ≤ K * ∏ i : Fin n, ‖m i‖) :
    ∃ p : ContinuousMultilinearMap 𝕜 E H, (∀ m, ι (p m) = G m) ∧ ‖p‖ ≤ K := by
  classical
  let f : ((i : Fin n) → E i) → H := fun m ↦ Classical.choose (hlift m)
  have hf (m : (i : Fin n) → E i) : ι (f m) = G m :=
    Classical.choose_spec (hlift m)
  let p : MultilinearMap 𝕜 E H :=
    { toFun := f
      map_update_add' := by
        intro _ m i x y
        apply hι
        rw [ι.map_add, hf, hf, hf]
        exact G.map_update_add m i x y
      map_update_smul' := by
        intro _ m i c x
        apply hι
        rw [ι.map_smul, hf, hf]
        exact G.map_update_smul m i c x }
  have hpbound (m : (i : Fin n) → E i) : ‖p m‖ ≤ K * ∏ i : Fin n, ‖m i‖ :=
    hbound m (f m) (hf m)
  refine ⟨p.mkContinuous K hpbound, hf, ?_⟩
  exact p.mkContinuous_norm_le hK hpbound

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_multilinear_coefficient_lift
