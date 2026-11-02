import GlobalEmbedding.Paper.HopfCollarPDEMetricIdentities
import GlobalEmbedding.Paper.CollarHopfInitialNormalDerivative

/-!
# Propagation of the original collar metric constraints

Source: `main.tex`, prop:collar, lines539–565, equations(5.3)–(5.4).
DAG: `collar-hopf-metric-propagation`; sole W2.
The SAME actual inverse PDE and original Cauchy data imply the metric constraints
throughout the SAME interval. No desired metric or formal derivative identity is assumed.
-/

noncomputable section
open Set WithLp Manifold
open scoped ContDiff Topology

namespace GlobalEmbedding.Paper

/-- The original actual square-inverse PDE preserves all three metric constraints.

The squared speed has zero derivative by the actual radial PDE row. Its constancy
also makes its actual spatial derivative zero; the first PDE rows and the genuine
time/Hopf bridge then make each mixed metric entry constant. The literal(5.4)
gives zero second derivative of every old Gram entry. The accepted pure initial
normal derivative theorem gives initial slope zero. Apply the pinned native
interval constancy theorem twice, retaining the original interval and witnesses.
Initial Gram, normality and unit length are only initial data, never conclusions
supplied throughout the collar. All indices, including diagonals, are retained. -/
theorem hopfCollar_square_pde_metric_propagation {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] (r0 : ℝ) (hr0 : 0 < r0)
    (H ν : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hH : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ω H)
    (hν : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ω ν)
    (hGram : ∀ x, Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i H x) = 1)
    (hunit : ∀ x, ‖ν x‖ = 1)
    (hperp : ∀ x k, inner ℝ (ν x) (freeFlowColumns (freeHopfProductFlow C) H x k) = 0)
    (G : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hG : ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ω G (Ioo (-r0) r0 ×ˢ univ))
    (htrace : ∀ x, G (0, x) = H x)
    (hrtrace : ∀ x, hopfCollarRDeriv G 0 x = ν x)
    (hT : ∀ r ∈ Ioo (-r0) r0, ∀ x, (hopfCollarSquarePairing C G r x).IsInvertible)
    (hPDE : ∀ r ∈ Ioo (-r0) r0, ∀ x, hopfCollarRRDeriv G r x =
      (hopfCollarSquarePairing C G r x).inverse (hopfCollarSquareForcing C G r x)) :
    ∀ r ∈ Ioo (-r0) r0, ∀ x,
      Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i (fun z ↦ G (r, z)) x) = 1 ∧
      (∀ i, inner ℝ (freeHopfDeriv C i (fun z ↦ G (r, z)) x)
        (hopfCollarRDeriv G r x) = 0) ∧
      ‖hopfCollarRDeriv G r x‖ ^ 2 = 1 := by
  have h0 : (0 : ℝ) ∈ Ioo (-r0) r0 := ⟨by linarith, hr0⟩
  have htrace' : (fun x ↦ G (0, x)) = H := funext htrace
  have hrtrace' : hopfCollarRDeriv G 0 = ν := funext hrtrace
  have hspeedD (r : ℝ) (hr : r ∈ Ioo (-r0) r0) (x : FreeHopfProduct C) :=
    hopfCollar_square_pde_speed_hasDerivAt C r0 G hG r hr x (hT r hr x) (hPDE r hr x)
  have hspeed (r : ℝ) (hr : r ∈ Ioo (-r0) r0) (x : FreeHopfProduct C) :
      ‖hopfCollarRDeriv G r x‖ ^ 2 = 1 := by
    have hc := isOpen_Ioo.is_const_of_deriv_eq_zero
      (convex_Ioo (-r0) r0).isPreconnected
      (fun s hs ↦ (hspeedD s hs x).differentiableAt.differentiableWithinAt)
      (fun s hs ↦ (hspeedD s hs x).deriv) hr h0
    simpa only [hrtrace x, hunit x, one_pow] using hc
  have hGr (r : ℝ) (hr : r ∈ Ioo (-r0) r0) (x : FreeHopfProduct C) :
      HasDerivAt (fun s : ℝ ↦ hopfCollarRDeriv G s x) (hopfCollarRRDeriv G r x) r := by
    have ha (s : ℝ) (hs : s ∈ Ioo (-r0) r0) (y : EuclideanSpace ℝ (Fin a)) :=
      hopfCollar_orbit_analyticAt C r0 G hG s hs x y
    exact hopfCollar_time_hasDerivAt_of_orbit C
      (fun z ↦ hopfCollarRDeriv G z.1 z.2) r x
      (hopfCollarRDeriv_orbit_analyticAt C G r0 x ha r hr 0)
  have hspatialSpeed (r : ℝ) (hr : r ∈ Ioo (-r0) r0)
      (x : FreeHopfProduct C) (i : Fin a) :
      inner ℝ (freeHopfDeriv C i (hopfCollarRDeriv G r) x)
        (hopfCollarRDeriv G r x) = 0 := by
    have ha (s : ℝ) (hs : s ∈ Ioo (-r0) r0) (y : EuclideanSpace ℝ (Fin a)) :=
      hopfCollar_orbit_analyticAt C r0 G hG s hs x y
    have hd := hopfCollar_slice_orbit_differentiableAt C
      (fun z ↦ hopfCollarRDeriv G z.1 z.2) r x 0
      (hopfCollarRDeriv_orbit_analyticAt C G r0 x ha r hr 0)
    have hf := freeHopf_orbit_hasDerivAt_of_differentiable C
      (hopfCollarRDeriv G r) x 0 hd i
    have hv := freeHopfDeriv_orbit_of_differentiable C
      (hopfCollarRDeriv G r) x 0 hd i
    rw [freeHopfOrbitLift_zero] at hf hv
    rw [← hv] at hf
    have hn := hf.norm_sq.deriv
    have heq : (fun t : ℝ ↦
        ‖hopfCollarRDeriv G r (freeHopfProductFlow C i t x)‖ ^ 2) = fun _ ↦ (1 : ℝ) := by
      funext t
      exact hspeed r hr _
    rw [heq, deriv_const] at hn
    simp only [freeHopfProductFlow_zero] at hn
    have hc := real_inner_comm (hopfCollarRDeriv G r x)
      (freeHopfDeriv C i (hopfCollarRDeriv G r) x)
    linarith
  have hmixedD (r : ℝ) (hr : r ∈ Ioo (-r0) r0)
      (x : FreeHopfProduct C) (i : Fin a) :
      HasDerivAt (fun s : ℝ ↦ inner ℝ (freeHopfDeriv C i (fun z ↦ G (s, z)) x)
        (hopfCollarRDeriv G s x)) 0 r := by
    have hd := (hopfCollar_time_hopf_hasDerivAt C r0 G hG r hr x i).inner ℝ (hGr r hr x)
    have hz := (hopfCollar_square_inverse_pde_equations C G r x
      (hT r hr x) (hPDE r hr x)).2.1 i
    have hc := real_inner_comm (hopfCollarRRDeriv G r x)
      (freeHopfDeriv C i (fun z ↦ G (r, z)) x)
    exact hd.congr_deriv (by have hs := hspatialSpeed r hr x i; linarith)
  have hmixed (r : ℝ) (hr : r ∈ Ioo (-r0) r0)
      (x : FreeHopfProduct C) (i : Fin a) :
      inner ℝ (freeHopfDeriv C i (fun z ↦ G (r, z)) x) (hopfCollarRDeriv G r x) = 0 := by
    have hc := isOpen_Ioo.is_const_of_deriv_eq_zero
      (convex_Ioo (-r0) r0).isPreconnected
      (fun s hs ↦ (hmixedD s hs x i).differentiableAt.differentiableWithinAt)
      (fun s hs ↦ (hmixedD s hs x i).deriv) hr h0
    rw [htrace', hrtrace'] at hc
    exact hc.trans ((real_inner_comm _ _).trans (hperp x (Sum.inl i)))
  have hinitial := collarHopf_initial_normal_derivative_inner C H ν hH hν hperp
  have hGramD0 (r : ℝ) (hr : r ∈ Ioo (-r0) r0)
      (x : FreeHopfProduct C) (i j : Fin a) :
      deriv (fun s : ℝ ↦ inner ℝ (freeHopfDeriv C i (fun z ↦ G (s, z)) x)
        (freeHopfDeriv C j (fun z ↦ G (s, z)) x)) r = 0 := by
    have hd (s : ℝ) (hs : s ∈ Ioo (-r0) r0) :=
      hopfCollar_square_pde_gram_deriv_hasDerivAt C r0 G hG s hs
        (hT s hs) (hPDE s hs) x i j
    have hc := isOpen_Ioo.is_const_of_deriv_eq_zero
      (convex_Ioo (-r0) r0).isPreconnected
      (fun s hs ↦ (hd s hs).differentiableAt.differentiableWithinAt)
      (fun s hs ↦ (hd s hs).deriv) hr h0
    have hi := (hopfCollar_gram_hasDerivAt C r0 G hG 0 h0 x i j).deriv
    rw [htrace', hrtrace'] at hi
    have hcomm := real_inner_comm (freeHopfDeriv C i H x) (freeHopfDeriv C j ν x)
    have hzero : deriv (fun s : ℝ ↦ inner ℝ
        (freeHopfDeriv C i (fun z ↦ G (s, z)) x)
        (freeHopfDeriv C j (fun z ↦ G (s, z)) x)) 0 = 0 := by
      rw [hi]
      have hij := hinitial x i j
      have hji := hinitial x j i
      linarith
    exact hc.trans hzero
  intro r hr x
  refine ⟨?_, hmixed r hr x, hspeed r hr x⟩
  ext i j
  have hc := isOpen_Ioo.is_const_of_deriv_eq_zero
    (convex_Ioo (-r0) r0).isPreconnected
    (fun s hs ↦
      (hopfCollar_gram_hasDerivAt C r0 G hG s hs x i j).differentiableAt.differentiableWithinAt)
    (fun s hs ↦ hGramD0 s hs x i j) hr h0
  rw [htrace'] at hc
  exact hc.trans (congrArg (fun B : Matrix (Fin a) (Fin a) ℝ ↦ B i j) (hGram x))

end GlobalEmbedding.Paper
