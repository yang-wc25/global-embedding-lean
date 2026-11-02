import GlobalEmbedding.Paper.HopfCollarTimeDifferentiation
import GlobalEmbedding.Paper.FreeHopfDerivativeCommute

/-!
# The actual collar normal is perpendicular to every old second column

Source: `main.tex`, prop:collar metric(5.1) and cor:selector, lines549–584.
DAG: `collar-hopf-radial-normal-orthogonality`; sole W2.
This is a CONSEQUENCE of actual collar properties for the selector consumer.
The separate original inverse-PDE metric propagation must construct those
properties and does not assume the desired metric identities.
-/

noncomputable section
open Set WithLp Manifold
open scoped ContDiff Topology

namespace GlobalEmbedding.Paper

/-- On the SAME actual native analytic collar, G_r is perpendicular to every
original ordered second Hopf derivative, including diagonals.

Differentiate actual mixed zero in both original Hopf directions. The genuine
time/Y bridge differentiates the constant old Gram in time. Existing actual
Hopf commutation and real inner symmetry identify the two second columns, so
these three true differential identities force the radial pairing to vanish.
No radial-normality or commutation identity is supplied as an extra premise.
The old-only cyclic identity and the true partial second form remain W3's scope. -/
theorem hopfCollar_r_second_inner_eq_zero {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] (r0 : ℝ)
    (G : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hG : AnalyticHopfCollarProperties C r0 G)
    (r : ℝ) (hr : r ∈ Ioo (-r0) r0) (x : FreeHopfProduct C) (i j : Fin a) :
    inner ℝ (hopfCollarRDeriv G r x)
      (freeHopfDeriv C i (freeHopfDeriv C j (fun y ↦ G (r, y))) x) = 0 := by
  let S := fun y : FreeHopfProduct C ↦ G (r, y)
  let A := hopfCollarRDeriv G r
  have hSω : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ω S :=
    hG.1.comp_contMDiff (contMDiff_const.prodMk contMDiff_id)
      (fun _ ↦ ⟨hr, mem_univ _⟩)
  have hS := hSω.of_le (show (∞ : ℕ∞ω) ≤ ω by simp)
  have hY (k : Fin a) : ContMDiff (freeHopfModel C)
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (freeHopfDeriv C k S) :=
    contMDiff_orbitDeriv (freeHopfProductFlow C k)
      (freeHopfProductFlow_contMDiff C k) S hS
  have haG (s : ℝ) (hs : s ∈ Ioo (-r0) r0) (y : EuclideanSpace ℝ (Fin a)) :=
    hopfCollar_orbit_analyticAt C r0 G hG.1 s hs x y
  have haA := hopfCollarRDeriv_orbit_analyticAt C G r0 x haG r hr 0
  have hAdiff : DifferentiableAt ℝ (A ∘ freeHopfOrbitLift C x) 0 :=
    hopfCollar_slice_orbit_differentiableAt C
      (fun z ↦ hopfCollarRDeriv G z.1 z.2) r x 0 haA
  have hAflow (k : Fin a) : HasDerivAt (fun t : ℝ ↦ A (freeHopfProductFlow C k t x))
      (freeHopfDeriv C k A x) 0 := by
    have hd := freeHopf_orbit_hasDerivAt_of_differentiable C A x 0 hAdiff k
    have hv := freeHopfDeriv_orbit_of_differentiable C A x 0 hAdiff k
    rw [freeHopfOrbitLift_zero] at hd hv
    rw [← hv] at hd
    exact hd
  have hcross (l k : Fin a) :
      inner ℝ (A x) (freeHopfDeriv C l (freeHopfDeriv C k S) x) +
        inner ℝ (freeHopfDeriv C l A x) (freeHopfDeriv C k S x) = 0 := by
    have hq := hasDerivAt_orbit (freeHopfProductFlow C l)
      (freeHopfProductFlow_contMDiff C l) (freeHopfProductFlow_add C l)
      (freeHopfDeriv C k S) (hY k) 0 x
    have h := ((hAflow l).inner ℝ hq).deriv
    have heq : (fun t : ℝ ↦ inner ℝ (A (freeHopfProductFlow C l t x))
        (freeHopfDeriv C k S (freeHopfProductFlow C l t x))) = fun _ ↦ (0 : ℝ) := by
      funext t
      exact (real_inner_comm _ _).trans ((hG.2 r hr (freeHopfProductFlow C l t x)).2.1 k)
    rw [heq, deriv_const] at h
    simpa only [freeHopfDeriv, freeHopfProductFlow_zero] using h.symm
  have hti := hopfCollar_time_hopf_hasDerivAt C r0 G hG.1 r hr x i
  have htj := hopfCollar_time_hopf_hasDerivAt C r0 G hG.1 r hr x j
  have htGram := (hti.inner ℝ htj).deriv
  have hconst : (fun s : ℝ ↦ inner ℝ (freeHopfDeriv C i (fun z ↦ G (s, z)) x)
      (freeHopfDeriv C j (fun z ↦ G (s, z)) x)) =ᶠ[𝓝 r]
      fun _ ↦ (1 : Matrix (Fin a) (Fin a) ℝ) i j := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
    exact congrArg (fun B : Matrix (Fin a) (Fin a) ℝ ↦ B i j) (hG.2 s hs x).1
  have hz := hconst.deriv_eq
  rw [deriv_const] at hz
  rw [hz] at htGram
  have h₁ := hcross i j
  have h₂ := hcross j i
  rw [freeHopfDeriv_commute_euclidean C S hS j i] at h₂
  change 0 = inner ℝ (freeHopfDeriv C i S x) (freeHopfDeriv C j A x) +
    inner ℝ (freeHopfDeriv C i A x) (freeHopfDeriv C j S x) at htGram
  have hcomm := real_inner_comm (freeHopfDeriv C i S x) (freeHopfDeriv C j A x)
  change inner ℝ (A x) (freeHopfDeriv C i (freeHopfDeriv C j S) x) = 0
  linarith

end GlobalEmbedding.Paper
