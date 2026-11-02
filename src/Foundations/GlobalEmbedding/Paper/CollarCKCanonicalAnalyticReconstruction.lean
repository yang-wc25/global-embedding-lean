import GlobalEmbedding.Paper.CollarCKAnalyticTaylorPackaging
import GlobalEmbedding.Paper.CollarCKFormalCoefficientRealization
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Algebra.BigOperators.Fin

/-!
# Analytic realization with the actual canonical CK Taylor dictionary

Source: Gantumur, notes2, Theorem18, pp9–10.
DAG: `collar-ck-canonical-analytic-reconstruction`. W5 same-formal analytic realization.
All actual word, fiber, Taylor and formal-PDE definitions are the accepted W3/W6 definitions.
-/

noncomputable section
open scoped BigOperators Topology ENNReal NNReal
namespace GlobalEmbedding.Paper

/-- Every actual multiindex has an actual coordinate word in the shared Taylor dictionary.
Use its native finite multiset and list representation, then enumerate that list. The shared
word index sums singleton exponents, so it is exactly the original multiindex. -/
theorem collarCKWordIndex_surjective {σ : Type*} [Fintype σ] [DecidableEq σ]
    (d : σ →₀ ℕ) : ∃ w : Fin d.degree → σ, collarCKWordIndex w = d := by
  have hlist (l : List σ) :
      collarCKWordIndex l.get = (l : Multiset σ).toFinsupp := by
    induction l with
    | nil => simp [collarCKWordIndex]
    | cons x l ih =>
      simp only [collarCKWordIndex, Fin.sum_univ_succ, List.length_cons,
        List.get_eq_getElem]
      rw [show (↑(x :: l) : Multiset σ) = {x} + (l : Multiset σ) from rfl,
        map_add, Multiset.toFinsupp_singleton]
      exact congrArg (fun y ↦ Finsupp.single x 1 + y) ih
  let l := d.toMultiset.toList
  have hlen : l.length = d.degree := by
    simp only [l, Multiset.length_toList, Finsupp.card_toMultiset, Finsupp.degree_apply]
    rfl
  have hw : collarCKWordIndex l.get = d := by
    rw [hlist]
    simpa only [l, Multiset.coe_toList] using Finsupp.toMultiset_toFinsupp d
  have hresult : ∃ k, ∃ w : Fin k → σ, k = d.degree ∧ collarCKWordIndex w = d :=
    ⟨l.length, l.get, hlen, hw⟩
  obtain ⟨k, w, hk, hw⟩ := hresult
  subst k
  exact ⟨w, hw⟩

/-- The shared actual word fiber is nonempty, including the zero multiindex. -/
theorem collarCKWordFiber_nonempty {σ : Type*} [Fintype σ] [DecidableEq σ]
    (d : σ →₀ ℕ) : (collarCKWordFiber d).Nonempty := by
  classical
  obtain ⟨w, hw⟩ := collarCKWordIndex_surjective d
  exact ⟨w, by simp [collarCKWordFiber, hw]⟩

/-- A word using only spatial variables has genuine normal exponent zero. -/
theorem collarCKWordIndex_no_time {n k : ℕ} (w : Fin k → CollarCKFullIndex n)
    (hw : ∀ i, w i ≠ Sum.inl ()) : collarCKWordIndex w (Sum.inl ()) = 0 := by
  classical
  simp only [collarCKWordIndex, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i _
  exact Finsupp.single_eq_of_ne (Ne.symm (hw i))

/-- Actual shared Taylor packaging of the reconstructed analytic sum is exactly the SAME
canonical formal solution. Every abstract word-law input of the earlier reconstruction is
now discharged by the actual accepted word dictionary; the original Euclidean domain is retained.
The genuine geometric coefficient bound is the remaining intermediate W4 input. This constructs
no competing formal solution and does not assert the still-unproved nonlinear analytic PDE. -/
theorem collarCKCanonicalAnalyticReconstruction {n m : ℕ} (G : CollarCKRHS n m)
    (M s : ℝ) (hM : 0 ≤ M) (hs : 0 ≤ s)
    (hbound : ∀ (d : CollarCKFullIndex n →₀ ℕ) (j : Fin m),
      |MvPowerSeries.coeff d (collarCKFlatten (collarCKFormalSolution G) j)| ≤
        M * s ^ d.degree) :
    ∃ (p : FormalMultilinearSeries ℝ (CollarCKFullIndex n → ℝ) (Fin m → ℝ))
      (u : ℝ × EuclideanSpace ℝ (Fin n) → Fin m → ℝ) (δ : ℝ),
      0 < δ ∧ AnalyticOnNhd ℝ u (Metric.ball 0 δ) ∧
      HasFPowerSeriesAt p.sum p 0 ∧
      (∀ t x, u (t, x) = p.sum (Sum.elim (fun _ ↦ t) (fun i ↦ x i))) ∧
      (∀ x, u (0, x) = 0) ∧
      (∀ (d : CollarCKFullIndex n →₀ ℕ) (j : Fin m),
        collarCKTaylorCoeff p d j =
          MvPowerSeries.coeff d (collarCKFlatten (collarCKFormalSolution G) j)) := by
  classical
  have hcover (k : ℕ) (d : CollarCKFullIndex n →₀ ℕ) (hd : d.degree = k) :
      ∃ w : Fin k → CollarCKFullIndex n, collarCKWordIndex w = d := by
    subst k
    exact collarCKWordIndex_surjective d
  obtain ⟨p, u, δ, hδ, hu, hp, heval, hzero, hcoeff⟩ :=
    collarCKFormalJointAnalyticRealization G (fun _ w ↦ collarCKWordIndex w)
      (fun _ w ↦ collarCKWordIndex_degree w) hcover
      (fun _ w hw ↦ collarCKWordIndex_no_time w hw) M s hM hs hbound
  refine ⟨p, u, δ, hδ, hu, hp, heval, hzero, ?_⟩
  intro d j
  simpa only [collarCKTaylorCoeff, collarCKWordFiber, Finset.sum_apply] using
    hcoeff d.degree d rfl j

#print axioms collarCKWordIndex_surjective
#print axioms collarCKWordFiber_nonempty
#print axioms collarCKWordIndex_no_time
#print axioms collarCKCanonicalAnalyticReconstruction
end GlobalEmbedding.Paper
