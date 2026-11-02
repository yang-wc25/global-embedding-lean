import GlobalEmbedding.Paper.HopfCollarSquarePairing
import GlobalEmbedding.Paper.HopfCollarMetricDifferentiation

/-!
# Differential metric identities from the actual original square inverse PDE

Source: `main.tex`, prop:collar, (5.3)–(5.4), lines543–565.
DAG: `collar-hopf-pde-metric-identities`; sole W2.
The actual PDE supplies the derivatives of the metric constraints. No desired
metric identities, initial-normal derivatives or formal jet identities are inputs.
-/

noncomputable section
open Set WithLp Manifold
open scoped ContDiff Topology

namespace GlobalEmbedding.Paper

/-- The actual sorted second PDE rows give the original pairing for ALL
ordered indices, including diagonals. For the reversed order use precisely
the accepted native commutation of the SAME G slice and real inner symmetry. -/
theorem hopfCollar_square_pde_second_all {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] (r0 : ℝ)
    (G : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hG : ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ω G (Ioo (-r0) r0 ×ˢ univ))
    (r : ℝ) (hr : r ∈ Ioo (-r0) r0) (x : FreeHopfProduct C)
    (hT : (hopfCollarSquarePairing C G r x).IsInvertible)
    (hPDE : hopfCollarRRDeriv G r x =
      (hopfCollarSquarePairing C G r x).inverse (hopfCollarSquareForcing C G r x))
    (i j : Fin a) :
    inner ℝ (hopfCollarRRDeriv G r x)
      (freeHopfDeriv C i (freeHopfDeriv C j (fun z ↦ G (r, z))) x) =
      inner ℝ (freeHopfDeriv C i (hopfCollarRDeriv G r) x)
        (freeHopfDeriv C j (hopfCollarRDeriv G r) x) := by
  have hrows := hopfCollar_square_inverse_pde_equations C G r x hT hPDE
  by_cases hij : i ≤ j
  · exact hrows.2.2 ⟨(i, j), hij⟩
  · have hji : j ≤ i := by omega
    have hSω : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ω
        (fun z ↦ G (r, z)) := hG.comp_contMDiff (contMDiff_const.prodMk contMDiff_id)
          (fun _ ↦ ⟨hr, mem_univ _⟩)
    have hS := hSω.of_le (show (∞ : ℕ∞ω) ≤ ω by simp)
    calc
      _ = inner ℝ (hopfCollarRRDeriv G r x)
          (freeHopfDeriv C j (freeHopfDeriv C i (fun z ↦ G (r, z))) x) :=
        congrArg (inner ℝ (hopfCollarRRDeriv G r x))
          (freeHopfDeriv_commute_euclidean C _ hS i j x)
      _ = inner ℝ (freeHopfDeriv C j (hopfCollarRDeriv G r) x)
          (freeHopfDeriv C i (hopfCollarRDeriv G r) x) := hrows.2.2 ⟨(j, i), hji⟩
      _ = _ := real_inner_comm _ _

/-- The literal actual inverse PDE forces the actual squared-speed derivative
to vanish. The genuine G_r curve derivative comes from accepted orbit analyticity;
native HasDerivAt.norm_sq and the original r-row give the result directly. -/
theorem hopfCollar_square_pde_speed_hasDerivAt {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] (r0 : ℝ)
    (G : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hG : ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ω G (Ioo (-r0) r0 ×ˢ univ))
    (r : ℝ) (hr : r ∈ Ioo (-r0) r0) (x : FreeHopfProduct C)
    (hT : (hopfCollarSquarePairing C G r x).IsInvertible)
    (hPDE : hopfCollarRRDeriv G r x =
      (hopfCollarSquarePairing C G r x).inverse (hopfCollarSquareForcing C G r x)) :
    HasDerivAt (fun s : ℝ ↦ ‖hopfCollarRDeriv G s x‖ ^ 2) 0 r := by
  let R := fun z : ℝ × FreeHopfProduct C ↦ hopfCollarRDeriv G z.1 z.2
  have ha (s : ℝ) (hs : s ∈ Ioo (-r0) r0) (y : EuclideanSpace ℝ (Fin a)) :=
    hopfCollar_orbit_analyticAt C r0 G hG s hs x y
  have haR := hopfCollarRDeriv_orbit_analyticAt C G r0 x ha r hr 0
  have hd := hopfCollar_time_hasDerivAt_of_orbit C R r x haR
  have hrows := hopfCollar_square_inverse_pde_equations C G r x hT hPDE
  have hz : inner ℝ (hopfCollarRDeriv G r x) (hopfCollarRRDeriv G r x) = 0 :=
    (real_inner_comm _ _).trans hrows.1
  have hn := hd.norm_sq
  change HasDerivAt (fun s : ℝ ↦ ‖hopfCollarRDeriv G s x‖ ^ 2)
    (2 * inner ℝ (hopfCollarRDeriv G r x) (hopfCollarRRDeriv G r x)) r at hn
  simpa only [hz, mul_zero] using hn

/-- The SAME actual square inverse PDE implies that the actual first time
derivative of every old Gram entry has derivative zero at every interval point.

Every actual first acceleration pairing is the zero function on the SAME whole
slice, so its actual Hopf derivative is zero. Substitute these functions and
the genuine all-ordered second PDE row into the literal equation(5.4). The
already proved true second HasDerivAt gives the displayed differential result.
No initial metric, normality, or desired Gram derivative is assumed. -/
theorem hopfCollar_square_pde_gram_deriv_hasDerivAt {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] (r0 : ℝ)
    (G : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hG : ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ω G (Ioo (-r0) r0 ×ˢ univ))
    (r : ℝ) (hr : r ∈ Ioo (-r0) r0)
    (hT : ∀ z, (hopfCollarSquarePairing C G r z).IsInvertible)
    (hPDE : ∀ z, hopfCollarRRDeriv G r z =
      (hopfCollarSquarePairing C G r z).inverse (hopfCollarSquareForcing C G r z))
    (x : FreeHopfProduct C) (i j : Fin a) :
    HasDerivAt (deriv (fun s : ℝ ↦ inner ℝ (freeHopfDeriv C i (fun z ↦ G (s, z)) x)
      (freeHopfDeriv C j (fun z ↦ G (s, z)) x))) 0 r := by
  have hzero (k : Fin a) :
      (fun z ↦ inner ℝ (hopfCollarRRDeriv G r z)
        (freeHopfDeriv C k (fun y ↦ G (r, y)) z)) = fun _ ↦ (0 : ℝ) := by
    funext z
    exact (hopfCollar_square_inverse_pde_equations C G r z (hT z) (hPDE z)).2.1 k
  have hdZero (k : Fin a) : freeHopfDeriv C k
      (fun _ : FreeHopfProduct C ↦ (0 : ℝ)) x = 0 := by
    simp [freeHopfDeriv, orbitDeriv]
  have hsecond := hopfCollar_square_pde_second_all C r0 G hG r hr x (hT x) (hPDE x) i j
  have hf := hopfCollar_metric_second_deriv C r0 G hG r hr x i j
  rw [hzero j, hzero i, hdZero i, hdZero j, hsecond] at hf
  have hz : deriv (deriv (fun s : ℝ ↦ inner ℝ
      (freeHopfDeriv C i (fun z ↦ G (s, z)) x)
      (freeHopfDeriv C j (fun z ↦ G (s, z)) x))) r = 0 := by linarith
  have hd := hopfCollar_gram_deriv_hasDerivAt C r0 G hG r hr x i j
  exact hd.congr_deriv (hd.deriv.symm.trans hz)

end GlobalEmbedding.Paper
