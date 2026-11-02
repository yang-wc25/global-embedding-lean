import GlobalEmbedding.Paper.HopfCollarTimeDifferentiation
import GlobalEmbedding.Paper.FreeHopfDerivativeCommute
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Actual time-Gram differentiation and the original equation(5.4)

Source: `main.tex`, prop:collar, lines549–565.
DAG: `collar-hopf-metric-differentiation`; sole W2.
All derivatives are actual derivatives of the SAME G. No metric constraints,
PDE rows, initial-normal identities or commuting derivative axioms are inputs.
-/

noncomputable section
open Set WithLp Manifold
open scoped ContDiff Topology

namespace GlobalEmbedding.Paper

/-- The actual second real derivative of the SAME original collar map.
This is only a transparent abbreviation for the literal derivative in (5.3). -/
abbrev hopfCollarRRDeriv {a N : ℕ} {C : Fin a → ℕ}
    (G : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (r : ℝ) (x : FreeHopfProduct C) : EuclideanSpace ℝ (Fin N) :=
  deriv (fun s : ℝ ↦ hopfCollarRDeriv G s x) r

/-- The real inner-product derivative rule in the original Hopf direction,
requiring only actual differentiability of the pulled-back observables.
Reuse the accepted actual orbit derivative identity and native fderiv_inner_apply;
this does not assume separate native smoothness of a derivative field. -/
theorem freeHopfDeriv_inner_of_orbit {a N : ℕ} (C : Fin a → ℕ)
    (U V : FreeHopfProduct C → EuclideanSpace ℝ (Fin N)) (x : FreeHopfProduct C)
    (hU : DifferentiableAt ℝ (U ∘ freeHopfOrbitLift C x) 0)
    (hV : DifferentiableAt ℝ (V ∘ freeHopfOrbitLift C x) 0) (i : Fin a) :
    freeHopfDeriv C i (fun z ↦ inner ℝ (U z) (V z)) x =
      inner ℝ (U x) (freeHopfDeriv C i V x) +
        inner ℝ (freeHopfDeriv C i U x) (V x) := by
  have hc := freeHopfDeriv_orbit_of_differentiable C
    (fun z ↦ inner ℝ (U z) (V z)) x 0 (hU.inner ℝ hV) i
  have hu := freeHopfDeriv_orbit_of_differentiable C U x 0 hU i
  have hv := freeHopfDeriv_orbit_of_differentiable C V x 0 hV i
  rw [freeHopfOrbitLift_zero] at hc hu hv
  change freeHopfDeriv C i (fun z ↦ inner ℝ (U z) (V z)) x =
    fderiv ℝ (fun t ↦ inner ℝ ((U ∘ freeHopfOrbitLift C x) t)
      ((V ∘ freeHopfOrbitLift C x) t)) 0 (EuclideanSpace.single i 1) at hc
  rw [fderiv_inner_apply ℝ hU hV, ← hu, ← hv] at hc
  simpa only [Function.comp_apply, freeHopfOrbitLift_zero] using hc

/-- The actual first time derivative of the old Gram pairing. Both original
time/Y derivatives are provided by the accepted genuine native bridge. -/
theorem hopfCollar_gram_hasDerivAt {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] (r0 : ℝ)
    (G : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hG : ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ω G (Ioo (-r0) r0 ×ˢ univ))
    (r : ℝ) (hr : r ∈ Ioo (-r0) r0) (x : FreeHopfProduct C) (i j : Fin a) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ (freeHopfDeriv C i (fun z ↦ G (s, z)) x)
        (freeHopfDeriv C j (fun z ↦ G (s, z)) x))
      (inner ℝ (freeHopfDeriv C i (fun z ↦ G (r, z)) x)
          (freeHopfDeriv C j (hopfCollarRDeriv G r) x) +
        inner ℝ (freeHopfDeriv C i (hopfCollarRDeriv G r) x)
          (freeHopfDeriv C j (fun z ↦ G (r, z)) x)) r :=
  (hopfCollar_time_hopf_hasDerivAt C r0 G hG r hr x i).inner ℝ
    (hopfCollar_time_hopf_hasDerivAt C r0 G hG r hr x j)

/-- The actual derivative of that first time derivative, with all terms of
the ordinary second inner-product rule. Apply the SAME accepted time/Y bridge
to actual G_r using its proved genuine orbit analyticity. Identify the first
derivative on an actual neighborhood in the SAME interval. -/
theorem hopfCollar_gram_deriv_hasDerivAt {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] (r0 : ℝ)
    (G : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hG : ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ω G (Ioo (-r0) r0 ×ˢ univ))
    (r : ℝ) (hr : r ∈ Ioo (-r0) r0) (x : FreeHopfProduct C) (i j : Fin a) :
    HasDerivAt (deriv (fun s : ℝ ↦ inner ℝ (freeHopfDeriv C i (fun z ↦ G (s, z)) x)
        (freeHopfDeriv C j (fun z ↦ G (s, z)) x)))
      (inner ℝ (freeHopfDeriv C i (fun z ↦ G (r, z)) x)
          (freeHopfDeriv C j (hopfCollarRRDeriv G r) x) +
        2 * inner ℝ (freeHopfDeriv C i (hopfCollarRDeriv G r) x)
          (freeHopfDeriv C j (hopfCollarRDeriv G r) x) +
        inner ℝ (freeHopfDeriv C i (hopfCollarRRDeriv G r) x)
          (freeHopfDeriv C j (fun z ↦ G (r, z)) x)) r := by
  let R := fun z : ℝ × FreeHopfProduct C ↦ hopfCollarRDeriv G z.1 z.2
  have ha (s : ℝ) (hs : s ∈ Ioo (-r0) r0) (y : EuclideanSpace ℝ (Fin a)) :=
    hopfCollar_orbit_analyticAt C r0 G hG s hs x y
  have haR (s : ℝ) (hs : s ∈ Ioo (-r0) r0) (y : EuclideanSpace ℝ (Fin a)) :=
    hopfCollarRDeriv_orbit_analyticAt C G r0 x ha s hs y
  have hi := hopfCollar_time_hopf_hasDerivAt C r0 G hG r hr x i
  have hj := hopfCollar_time_hopf_hasDerivAt C r0 G hG r hr x j
  have hri := hopfCollar_time_hopf_hasDerivAt_of_orbits C R r0 x haR r hr i
  have hrj := hopfCollar_time_hopf_hasDerivAt_of_orbits C R r0 x haR r hr j
  have hd := (hi.inner ℝ hrj).add (hri.inner ℝ hj)
  have hfirst : (deriv (fun s : ℝ ↦ inner ℝ (freeHopfDeriv C i (fun z ↦ G (s, z)) x)
      (freeHopfDeriv C j (fun z ↦ G (s, z)) x))) =ᶠ[𝓝 r]
      (fun s : ℝ ↦ inner ℝ (freeHopfDeriv C i (fun z ↦ G (s, z)) x)
          (freeHopfDeriv C j (hopfCollarRDeriv G s) x) +
        inner ℝ (freeHopfDeriv C i (hopfCollarRDeriv G s) x)
          (freeHopfDeriv C j (fun z ↦ G (s, z)) x)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
    exact (hopfCollar_gram_hasDerivAt C r0 G hG s hs x i j).deriv
  have hd' := hd.congr_of_eventuallyEq hfirst
  have hRR : hopfCollarRDeriv R r = hopfCollarRRDeriv G r := rfl
  have hR : (fun z ↦ R (r, z)) = hopfCollarRDeriv G r := rfl
  rw [hRR, hR] at hd'
  exact hd'.congr_deriv (by ring)

/-- The literal original equation(5.4), with actual derivatives of the SAME G.

The genuine second-time inner-product rule above supplies all four terms.
The actual G_rr orbit field is analytic by applying the accepted derivative
field theorem twice. Native spatial inner differentiation expands the two
original Yi pairings; accepted original Hopf commutation identifies the second
columns. Real inner symmetry and scalar algebra give precisely (5.4).
No PDE, metric constraint, normality or formal derivative relation is assumed. -/
theorem hopfCollar_metric_second_deriv {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] (r0 : ℝ)
    (G : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hG : ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ω G (Ioo (-r0) r0 ×ˢ univ))
    (r : ℝ) (hr : r ∈ Ioo (-r0) r0) (x : FreeHopfProduct C) (i j : Fin a) :
    deriv (deriv (fun s : ℝ ↦ inner ℝ (freeHopfDeriv C i (fun z ↦ G (s, z)) x)
        (freeHopfDeriv C j (fun z ↦ G (s, z)) x))) r =
      2 * inner ℝ (freeHopfDeriv C i (hopfCollarRDeriv G r) x)
        (freeHopfDeriv C j (hopfCollarRDeriv G r) x) +
      freeHopfDeriv C i (fun z ↦ inner ℝ (hopfCollarRRDeriv G r z)
        (freeHopfDeriv C j (fun y ↦ G (r, y)) z)) x +
      freeHopfDeriv C j (fun z ↦ inner ℝ (hopfCollarRRDeriv G r z)
        (freeHopfDeriv C i (fun y ↦ G (r, y)) z)) x -
      2 * inner ℝ (hopfCollarRRDeriv G r x)
        (freeHopfDeriv C i (freeHopfDeriv C j (fun z ↦ G (r, z))) x) := by
  let S := fun z : FreeHopfProduct C ↦ G (r, z)
  let A := hopfCollarRDeriv G r
  let B := hopfCollarRRDeriv G r
  let R := fun z : ℝ × FreeHopfProduct C ↦ hopfCollarRDeriv G z.1 z.2
  have hSω : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ω S :=
    hG.comp_contMDiff (contMDiff_const.prodMk contMDiff_id)
      (fun _ ↦ ⟨hr, mem_univ _⟩)
  have hS := hSω.of_le (show (∞ : ℕ∞ω) ≤ ω by simp)
  have hY (k : Fin a) : ContMDiff (freeHopfModel C)
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (freeHopfDeriv C k S) :=
    contMDiff_orbitDeriv (freeHopfProductFlow C k)
      (freeHopfProductFlow_contMDiff C k) S hS
  have hYdiff (k : Fin a) :
      DifferentiableAt ℝ ((freeHopfDeriv C k S) ∘ freeHopfOrbitLift C x) 0 :=
    ((hY k).comp (freeHopfOrbitLift_contMDiff C x)).contDiff.differentiable (by simp) 0
  have ha (s : ℝ) (hs : s ∈ Ioo (-r0) r0) (y : EuclideanSpace ℝ (Fin a)) :=
    hopfCollar_orbit_analyticAt C r0 G hG s hs x y
  have haR (s : ℝ) (hs : s ∈ Ioo (-r0) r0) (y : EuclideanSpace ℝ (Fin a)) :=
    hopfCollarRDeriv_orbit_analyticAt C G r0 x ha s hs y
  have haRR := hopfCollarRDeriv_orbit_analyticAt C R r0 x haR r hr 0
  have hBdiff : DifferentiableAt ℝ (B ∘ freeHopfOrbitLift C x) 0 :=
    hopfCollar_slice_orbit_differentiableAt C
      (fun z ↦ hopfCollarRRDeriv G z.1 z.2) r x 0 haRR
  have hi := freeHopfDeriv_inner_of_orbit C B (freeHopfDeriv C j S) x hBdiff (hYdiff j) i
  have hj := freeHopfDeriv_inner_of_orbit C B (freeHopfDeriv C i S) x hBdiff (hYdiff i) j
  have ht := (hopfCollar_gram_deriv_hasDerivAt C r0 G hG r hr x i j).deriv
  change deriv (deriv (fun s : ℝ ↦ inner ℝ (freeHopfDeriv C i (fun z ↦ G (s, z)) x)
    (freeHopfDeriv C j (fun z ↦ G (s, z)) x))) r =
      inner ℝ (freeHopfDeriv C i S x) (freeHopfDeriv C j B x) +
      2 * inner ℝ (freeHopfDeriv C i A x) (freeHopfDeriv C j A x) +
      inner ℝ (freeHopfDeriv C i B x) (freeHopfDeriv C j S x) at ht
  rw [freeHopfDeriv_commute_euclidean C S hS j i] at hj
  have hcomm := real_inner_comm (freeHopfDeriv C i S x) (freeHopfDeriv C j B x)
  change _ = 2 * inner ℝ (freeHopfDeriv C i A x) (freeHopfDeriv C j A x) +
    freeHopfDeriv C i (fun z ↦ inner ℝ (B z) (freeHopfDeriv C j S z)) x +
    freeHopfDeriv C j (fun z ↦ inner ℝ (B z) (freeHopfDeriv C i S z)) x -
    2 * inner ℝ (B x) (freeHopfDeriv C i (freeHopfDeriv C j S) x)
  linarith

end GlobalEmbedding.Paper
