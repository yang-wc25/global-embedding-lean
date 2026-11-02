import GlobalEmbedding.Paper.CollarHopfAmbientOrbitJetBound
import GlobalEmbedding.Paper.CollarHopfColumnOrbitJetBound
import GlobalEmbedding.Paper.CollarHopfNativeFreePersistence

/-!
# Fixed actual ambient C5 neighborhoods on the original compact Hopf product

Source: `main.tex`, prop:collar, lines520–526.
DAG: `collar-hopf-ambient-c5-neighborhood`; exclusive AS2b owner W2.
Only actual specializations of accepted orbit/column/margin bounds are assembled.
-/

noncomputable section
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- A fixed genuine action constant converts ambient jets through five into
actual original first/sortedsecond column orbit jets through three, uniformly
on ALL original points and ALL real orbit times. No column estimate is assumed.
Proof: compose the accepted full orbit composition estimate at order five with
the accepted actual column contraction, using n+2<=5. Source: prop:collar520–526. -/
theorem collarHopf_ambient_c5_column_jets {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] :
    ∃ B : ℝ, 0 < B ∧
      ∀ R : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N), ContDiff ℝ ∞ R →
      ∀ ε : ℝ, 0 ≤ ε →
        (∀ x : FreeHopfProduct C, ∀ i ≤ 5,
          ‖iteratedFDeriv ℝ i R (freeHopfAmbientInclusion C x)‖ ≤ ε) →
        ∀ x : FreeHopfProduct C, ∀ y : EuclideanSpace ℝ (Fin a), ∀ n ≤ 3,
          ∀ k : BalancedPairingIndex a,
          ‖iteratedFDeriv ℝ n (fun t : EuclideanSpace ℝ (Fin a) ↦
            freeFlowColumns (freeHopfProductFlow C) (R ∘ freeHopfAmbientInclusion C)
              (freeHopfOrbitLift C x t) k) y‖ ≤ B * ε := by
  obtain ⟨B, hB, hb⟩ := collarHopf_ambient_orbit_jet_bound (N := N) C 5
  refine ⟨B, hB, ?_⟩
  intro R hR ε hε hjet x y n hn k
  have hU := hR.contMDiff.comp (freeHopfAmbientInclusion_contMDiff C)
  exact collarHopf_column_orbit_jet_bound C _ hU x y n (B * ε)
    (fun i hi ↦ hb R hR ε hε hjet x y i (by omega)) k

/-- A FIXED smooth actual ambient extension with free native restriction determines
a positive actual ambient C5 threshold, a positive common synthesis lower margin,
and a common column orbit C3 bound, BEFORE any approximating F is chosen.

Proof: use accepted native compact persistence for the fixed restriction. The
accepted actual ambient-to-column constant converts the genuine C5 error into
its required native column error. Compactness bounds fixed f0 jets through five;
restrict the threshold to at most one, yielding common F jets and hence common
column fiber jets through three. All norms, flows and indices are the originals.
The fixed f0 is constructed by the accepted compact ambient extension theorem.
No rank or desired column/Holder/inverse bound on F is a premise.
Source: prop:collar sufficiently close analytic approximation, lines520–526. -/
theorem collarHopf_fixed_ambient_c5_neighborhood {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)]
    (f0 : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N)) (hf0 : ContDiff ℝ ∞ f0)
    (hfree : ∀ x, LinearIndependent ℝ
      (freeFlowColumns (freeHopfProductFlow C) (f0 ∘ freeHopfAmbientInclusion C) x)) :
    ∃ η μ L : ℝ, 0 < η ∧ 0 < μ ∧ 1 ≤ L ∧
      ∀ F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N), ContDiff ℝ ∞ F →
        (∀ x : FreeHopfProduct C, ∀ i ≤ 5,
          ‖iteratedFDeriv ℝ i (F - f0) (freeHopfAmbientInclusion C x)‖ ≤ η) →
        (∀ x, LinearIndependent ℝ
          (freeFlowColumns (freeHopfProductFlow C) (F ∘ freeHopfAmbientInclusion C) x) ∧
          ∀ u : EuclideanSpace ℝ (BalancedPairingIndex a),
            μ * ‖u‖ ≤ ‖freeColumnOperator
              (freeFlowColumns (freeHopfProductFlow C) (F ∘ freeHopfAmbientInclusion C) x) u‖) ∧
        (∀ x : FreeHopfProduct C, ∀ y : EuclideanSpace ℝ (Fin a), ∀ n ≤ 3,
          ∀ k : BalancedPairingIndex a,
          ‖iteratedFDeriv ℝ n (fun t : EuclideanSpace ℝ (Fin a) ↦
            freeFlowColumns (freeHopfProductFlow C) (F ∘ freeHopfAmbientInclusion C)
              (freeHopfOrbitLift C x t) k) y‖ ≤ L) ∧
        (∀ x : FreeHopfProduct C, ∀ y : Fin a → ℝ,
          (collarAmbientHopfPairingMatrix C F
              (collarAmbientHopfAction C y (freeHopfAmbientInclusion C x)) *
            (collarAmbientHopfPairingMatrix C F
              (collarAmbientHopfAction C y (freeHopfAmbientInclusion C x))).transpose).det ≠ 0) := by
  have hbase := hf0.contMDiff.comp (freeHopfAmbientInclusion_contMDiff C)
  obtain ⟨d, μ, hd, hμ, hpersist⟩ :=
    collarHopf_native_free_persistence C _ hbase hfree
  obtain ⟨B, hB, hb⟩ := collarHopf_ambient_c5_column_jets (N := N) C
  let S : FreeHopfProduct C → ℝ := fun x ↦
    ∑ i : Fin 6, ‖iteratedFDeriv ℝ i.val f0 (freeHopfAmbientInclusion C x)‖
  have hS : Continuous S := by
    apply continuous_finsetSum Finset.univ
    intro i _
    exact ((hf0.continuous_iteratedFDeriv (by simp)).comp
      (freeHopfAmbientInclusion_contMDiff C).continuous).norm
  obtain ⟨K0, hK0⟩ := (isCompact_univ : IsCompact (Set.univ : Set (FreeHopfProduct C)))
    |>.exists_bound_of_continuousOn hS.continuousOn
  let K := max 1 K0
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hf0jet (x : FreeHopfProduct C) (i : ℕ) (hi : i ≤ 5) :
      ‖iteratedFDeriv ℝ i f0 (freeHopfAmbientInclusion C x)‖ ≤ K := by
    have hs : ‖iteratedFDeriv ℝ i f0 (freeHopfAmbientInclusion C x)‖ ≤ S x :=
      Finset.single_le_sum
        (f := fun j : Fin 6 ↦ ‖iteratedFDeriv ℝ j.val f0 (freeHopfAmbientInclusion C x)‖)
        (fun j _ ↦ norm_nonneg _) (Finset.mem_univ (⟨i, by omega⟩ : Fin 6))
    exact hs.trans ((le_abs_self (S x)).trans ((hK0 x (Set.mem_univ x)).trans (le_max_right _ _)))
  let η := min 1 (d / B)
  have hη : 0 < η := lt_min zero_lt_one (div_pos hd hB)
  have hBη : B * η ≤ d := by
    have hh := mul_le_mul_of_nonneg_left (min_le_right (1 : ℝ) (d / B)) hB.le
    simpa only [mul_div_cancel₀ _ hB.ne'] using hh
  let L := 1 + B * (K + 1)
  have hL : 1 ≤ L := le_add_of_nonneg_right (by positivity)
  refine ⟨η, μ, L, hη, hμ, hL, ?_⟩
  intro F hF hclose
  let U := F ∘ freeHopfAmbientInclusion C
  let U0 := f0 ∘ freeHopfAmbientInclusion C
  have hU : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ U :=
    hF.contMDiff.comp (freeHopfAmbientInclusion_contMDiff C)
  have hdsub (P Q : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
      (hP : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ P)
      (hQ : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ Q)
      (i : Fin a) : freeHopfDeriv C i (P - Q) = freeHopfDeriv C i P - freeHopfDeriv C i Q := by
    funext z
    change freeHopfDeriv C i (fun x ↦ P x - Q x) z =
      freeHopfDeriv C i P z - freeHopfDeriv C i Q z
    rw [← freeHopfGenerator_mvfderiv C i _ (hP.sub hQ) z,
      ← freeHopfGenerator_mvfderiv C i P hP z, ← freeHopfGenerator_mvfderiv C i Q hQ z]
    rw [mvfderiv_fun_sub (hP.mdifferentiableAt (by simp)) (hQ.mdifferentiableAt (by simp))]
    rfl
  have hcolsub (z : FreeHopfProduct C) (k : BalancedPairingIndex a) :
      freeFlowColumns (freeHopfProductFlow C) (U - U0) z k =
        freeFlowColumns (freeHopfProductFlow C) U z k -
          freeFlowColumns (freeHopfProductFlow C) U0 z k := by
    cases k with
    | inl i => exact congrFun (hdsub U U0 hU hbase i) z
    | inr ij =>
      change freeHopfDeriv C ij.val.1 (freeHopfDeriv C ij.val.2 (U - U0)) z = _
      rw [hdsub U U0 hU hbase ij.val.2]
      exact congrFun (hdsub _ _ (freeHopfDeriv_contMDiff C U hU ij.val.2)
        (freeHopfDeriv_contMDiff C U0 hbase ij.val.2) ij.val.1) z
  have herr (z : FreeHopfProduct C) (k : BalancedPairingIndex a) :
      ‖freeFlowColumns (freeHopfProductFlow C) U z k -
        freeFlowColumns (freeHopfProductFlow C) U0 z k‖ ≤ d := by
    have hh := hb (F - f0) (hF.sub hf0) η hη.le hclose z 0 0 (by omega) k
    simp only [norm_iteratedFDeriv_zero, freeHopfOrbitLift_zero] at hh
    change ‖freeFlowColumns (freeHopfProductFlow C) (U - U0) z k‖ ≤ B * η at hh
    rw [hcolsub] at hh
    exact hh.trans hBη
  have hstable := hpersist U herr
  have hFjet (z : FreeHopfProduct C) (i : ℕ) (hi : i ≤ 5) :
      ‖iteratedFDeriv ℝ i F (freeHopfAmbientInclusion C z)‖ ≤ K + 1 := by
    have he := hclose z i hi
    rw [iteratedFDeriv_sub_apply (hF.contDiffAt.of_le (by simp))
      (hf0.contDiffAt.of_le (by simp))] at he
    have hh := norm_le_norm_sub_add
      (iteratedFDeriv ℝ i F (freeHopfAmbientInclusion C z))
      (iteratedFDeriv ℝ i f0 (freeHopfAmbientInclusion C z))
    have hη1 : η ≤ 1 := min_le_left _ _
    linarith [hf0jet z i hi]
  refine ⟨hstable, ?_, ?_⟩
  · intro x y n hn k
    exact (hb F hF (K + 1) (by positivity) hFjet x y n hn k).trans
      (le_add_of_nonneg_left zero_le_one)
  · exact collarAmbientHopfPairingMatrix_fiber_det_ne_zero C F (fun z ↦ (hstable z).1)

end GlobalEmbedding.Paper
