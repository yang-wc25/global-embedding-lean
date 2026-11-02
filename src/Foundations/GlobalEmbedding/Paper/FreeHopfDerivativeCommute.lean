import GlobalEmbedding.Paper.FreeHopfOrbitLift
import GlobalEmbedding.Paper.PlanarOrbitDerivativeSmooth

/-!
# Genuine commutation of the actual smooth Hopf partial derivatives

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines216–232 and430–495.
DAG node: `free-hopf-derivative-commute`.
-/

noncomputable section

open Set Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Actual Hopf differentiation commutes with a genuine fixed continuous linear map. -/
theorem freeHopfDeriv_clm {a : ℕ} (C : Fin a → ℕ) [∀ i, Fact (0 < C i)]
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (i : Fin a) (L : F →L[ℝ] G)
    (f : FreeHopfProduct C → F) (hf : ContMDiff (freeHopfModel C) 𝓘(ℝ, F) ∞ f)
    (x : FreeHopfProduct C) :
    freeHopfDeriv C i (fun z ↦ L (f z)) x = L (freeHopfDeriv C i f x) := by
  have hd := hasDerivAt_orbit (freeHopfProductFlow C i) (freeHopfProductFlow_contMDiff C i)
    (freeHopfProductFlow_add C i) f hf 0 x
  have hh := L.hasFDerivAt.comp_hasDerivAt 0 hd
  simpa only [freeHopfDeriv, orbitDeriv, Function.comp_def, freeHopfProductFlow_zero]
    using hh.deriv

/-- The actual Hopf partial derivatives commute for every native smooth Euclidean map.

Proof: use the genuine multi-orbit lift through x at zero and its actual unit-direction
pushforward. The accepted native lift/Schwarz theorem proves commutation of the actual
generator derivatives. The genuine generator/orbit derivative equality, applied also to
the actual smooth first derivatives, identifies both nested expressions with the literal
Hopf partials. No commuting-derivation hypothesis is added to the source or final target.
Source: commuting factors in setup:partial and the old metric rows of thm:free. -/
theorem freeHopfDeriv_commute_euclidean {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] (f : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hf : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ f)
    (i j : Fin a) (x : FreeHopfProduct C) :
    freeHopfDeriv C i (freeHopfDeriv C j f) x =
      freeHopfDeriv C j (freeHopfDeriv C i f) x := by
  have hc := balanced_directional_commute_of_lift f hf
    (freeHopfGeneratorSection C i) (freeHopfGeneratorSection C j)
    (freeHopfOrbitLift C x) univ isOpen_univ
    (freeHopfOrbitLift_contMDiff C x).contMDiffOn 0 (mem_univ 0)
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    (fun y _ ↦ freeHopfGenerator_eq_orbitLift_mfderiv C x y i)
    (fun y _ ↦ freeHopfGenerator_eq_orbitLift_mfderiv C x y j)
  rw [freeHopfOrbitLift_zero] at hc
  have he (k : Fin a) : balancedDirectionalDerivative f (freeHopfGenerator C k) =
      freeHopfDeriv C k f :=
    funext (fun z ↦ freeHopfGenerator_mvfderiv C k f hf z)
  have hs (k : Fin a) :
      ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
        (freeHopfDeriv C k f) :=
    contMDiff_orbitDeriv (freeHopfProductFlow C k) (freeHopfProductFlow_contMDiff C k) f hf
  change balancedDirectionalDerivative (balancedDirectionalDerivative f (freeHopfGenerator C j))
      (freeHopfGenerator C i) x =
    balancedDirectionalDerivative (balancedDirectionalDerivative f (freeHopfGenerator C i))
      (freeHopfGenerator C j) x at hc
  rw [he j, he i] at hc
  change mvfderiv (freeHopfModel C) (freeHopfDeriv C j f) x (freeHopfGenerator C i x) =
    mvfderiv (freeHopfModel C) (freeHopfDeriv C i f) x (freeHopfGenerator C j x) at hc
  rw [freeHopfGenerator_mvfderiv C i _ (hs j),
    freeHopfGenerator_mvfderiv C j _ (hs i)] at hc
  exact hc

/-- Actual Hopf partials commute for every native smooth finite-dimensional real target,
including scalar observables, without an extra commutation hypothesis.

Use actual fixed finite-dimensional continuous linear coordinates, the proved CLM chain
rule and the genuine Euclidean commutation theorem. Injectivity of the actual coordinate
equivalence transports equality to the original target. Source: setup:partial. -/
theorem freeHopfDeriv_commute {a : ℕ} (C : Fin a → ℕ) [∀ i, Fact (0 < C i)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (f : FreeHopfProduct C → F) (hf : ContMDiff (freeHopfModel C) 𝓘(ℝ, F) ∞ f)
    (i j : Fin a) (x : FreeHopfProduct C) :
    freeHopfDeriv C i (freeHopfDeriv C j f) x =
      freeHopfDeriv C j (freeHopfDeriv C i f) x := by
  let e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ F)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  have hc := freeHopfDeriv_commute_euclidean C (fun z ↦ e (f z))
    (e.contDiff.contMDiff.comp hf) i j x
  have he (k : Fin a) : freeHopfDeriv C k (fun z ↦ e (f z)) =
      (fun z ↦ e (freeHopfDeriv C k f z)) :=
    funext (fun z ↦ freeHopfDeriv_clm C k e.toContinuousLinearMap f hf z)
  have hs (k : Fin a) : ContMDiff (freeHopfModel C) 𝓘(ℝ, F) ∞ (freeHopfDeriv C k f) :=
    contMDiff_orbitDeriv (freeHopfProductFlow C k) (freeHopfProductFlow_contMDiff C k) f hf
  rw [he j, he i] at hc
  change freeHopfDeriv C i (fun z ↦ e.toContinuousLinearMap (freeHopfDeriv C j f z)) x =
    freeHopfDeriv C j (fun z ↦ e.toContinuousLinearMap (freeHopfDeriv C i f z)) x at hc
  rw [freeHopfDeriv_clm C i e.toContinuousLinearMap _ (hs j),
    freeHopfDeriv_clm C j e.toContinuousLinearMap _ (hs i)] at hc
  exact e.injective hc

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.freeHopfDeriv_clm
#print axioms GlobalEmbedding.Paper.freeHopfDeriv_commute_euclidean
#print axioms GlobalEmbedding.Paper.freeHopfDeriv_commute
