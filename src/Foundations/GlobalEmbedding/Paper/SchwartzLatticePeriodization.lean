import GlobalEmbedding.Paper.SchwartzLatticeJetBounds
import Mathlib.Analysis.Calculus.SmoothSeries

/-! Actual smooth lattice periodization of Schwartz functions. The sum is globally
periodic; every derivative is identified by locally uniform summable bounds, never
by a compact-support or locally-finite assertion about the Schwartz function. -/

open Filter Set Metric
open scoped SchwartzMap Topology ContDiff

namespace GlobalEmbedding.Paper

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

noncomputable def schwartzLatticePeriodization (L : Submodule ℤ E)
    (f : 𝓢(E, F)) (x : E) : F := ∑' z : L, f (x + z)

/-- The actual Schwartz lattice sum is smooth, all its genuine iterated derivatives
are the corresponding absolutely convergent jet sums, and it is invariant under all
lattice shifts. Proof: bound each jet uniformly on every ball by a summable sequence;
termwise differentiation and continuity assemble actual Taylor data on that ball.
Uniqueness of derivatives identifies the jet sums; reindexing by lattice addition
proves periodicity. Zero-dimensional sources and the zero lattice are retained. -/
theorem schwartz_lattice_periodization_regular
    (L : Submodule ℤ E) [DiscreteTopology L] (f : 𝓢(E, F)) :
    ContDiff ℝ ∞ (schwartzLatticePeriodization L f) ∧
    (∀ (k : ℕ) (x : E), iteratedFDeriv ℝ k (schwartzLatticePeriodization L f) x =
      ∑' z : L, iteratedFDeriv ℝ k f (x + z)) ∧
    (∀ (z : L) (x : E), schwartzLatticePeriodization L f (x + z) =
      schwartzLatticePeriodization L f x) := by
  classical
  let p : E → FormalMultilinearSeries ℝ E F :=
    fun x k => ∑' z : L, iteratedFDeriv ℝ k f (x + z)
  have hlocal (R : ℝ) (hR : 0 < R) :
      HasFTaylorSeriesUpToOn ∞ (schwartzLatticePeriodization L f) p (Metric.ball 0 R) := by
    choose v hv hb using fun k => schwartz_lattice_jet_majorant L f k hR.le
    have hs (k : ℕ) (x : E) (hx : x ∈ Metric.ball 0 R) :
        Summable (fun z : L => iteratedFDeriv ℝ k f (x + z)) := by
      apply Summable.of_norm_bounded (hv k)
      intro z
      exact hb k z x (by simpa using (Metric.mem_ball.mp hx).le)
    have hfder (k : ℕ) (z : L) (x : E) :
        HasFDerivAt (fun y => iteratedFDeriv ℝ k f (y + z))
          (iteratedFDeriv ℝ (k + 1) f (x + z)).curryLeft x := by
      have ht : ContDiff ℝ (k + 1) (fun y : E => f (y + z)) :=
        (f.smooth (k + 1)).comp (contDiff_id.add contDiff_const)
      have H := ht.ftaylorSeries.fderiv k (by exact_mod_cast Nat.lt_succ_self k) x
      simpa only [ftaylorSeries, iteratedFDeriv_comp_add_right] using H
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      change (continuousMultilinearCurryFin0 ℝ E F).toContinuousLinearEquiv
        (∑' z : L, iteratedFDeriv ℝ 0 f (x + z)) = _
      rw [(continuousMultilinearCurryFin0 ℝ E F).toContinuousLinearEquiv.map_tsum]
      apply tsum_congr
      intro z
      change (iteratedFDeriv ℝ 0 f (x + z)).curry0 = f (x + z)
      simp [iteratedFDeriv_zero_eq_comp]
    · intro k hk x hx
      let I := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) F
      have hnorm (z : L) (y : E) (hy : y ∈ Metric.ball 0 R) :
          ‖(iteratedFDeriv ℝ (k + 1) f (y + z)).curryLeft‖ ≤ v (k + 1) z := by
        change ‖I (iteratedFDeriv ℝ (k + 1) f (y + z))‖ ≤ _
        rw [I.norm_map]
        exact hb (k + 1) z y (by simpa using (Metric.mem_ball.mp hy).le)
      have H := hasFDerivAt_tsum_of_isPreconnected (hv (k + 1)) isOpen_ball
        (convex_ball (0 : E) R).isPreconnected
        (fun z y _ => hfder k z y) hnorm
        (show (0 : E) ∈ Metric.ball 0 R by simpa)
        (hs k 0 (by simpa)) hx
      have he : (∑' z : L, (iteratedFDeriv ℝ (k + 1) f (x + z)).curryLeft) =
          (p x (k + 1)).curryLeft := by
        exact I.toContinuousLinearEquiv.map_tsum.symm
      rw [he] at H
      exact H.hasFDerivWithinAt
    · intro k hk
      refine continuousOn_tsum (u := v k) (fun z => ?_) (hv k) (fun z x hx => ?_)
      ·
        exact ((f.smooth (⊤ : ℕ∞)).continuous_iteratedFDeriv (by simp)).comp
          (continuous_id.add continuous_const) |>.continuousOn
      · exact hb k z x (by simpa using (Metric.mem_ball.mp hx).le)
  have hpoint (x : E) :
      ContDiffAt ℝ ∞ (schwartzLatticePeriodization L f) x ∧
      ∀ k : ℕ, p x k = iteratedFDeriv ℝ k (schwartzLatticePeriodization L f) x := by
    let R : ℝ := ‖x‖ + 1
    have hR : 0 < R := by dsimp [R]; positivity
    have hx : x ∈ Metric.ball (0 : E) R := by simp [R]
    have H := hlocal R hR
    refine ⟨H.contDiffOn.contDiffAt (isOpen_ball.mem_nhds hx), fun k => ?_⟩
    rw [H.eq_iteratedFDerivWithin_of_uniqueDiffOn (by simp) isOpen_ball.uniqueDiffOn hx]
    exact iteratedFDerivWithin_of_isOpen k isOpen_ball hx
  refine ⟨contDiff_iff_contDiffAt.mpr (fun x => (hpoint x).1), ?_, ?_⟩
  · intro k x
    exact ((hpoint x).2 k).symm
  · intro z x
    simpa only [schwartzLatticePeriodization, Equiv.coe_addRight, Submodule.coe_add,
      add_assoc, add_comm, add_left_comm] using
      (Equiv.addRight z).tsum_eq (fun w : L => f (x + w))

#print axioms schwartz_lattice_periodization_regular

end GlobalEmbedding.Paper
