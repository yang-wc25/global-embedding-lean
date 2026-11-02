import AuxNormBridge.AllOrderCore
import Smoothing.TensorParameterNorms
import Smoothing.TensorTransferJets

/-!
# Transport the same tensor's jets from protected cores

The actual moving-frame formula has both Jacobian factors.  It transports
the tensor's own compact-core jets to the unchanged original norm domains;
it never identifies matrices in different tangent frames.  Only the fixed
fiber dimension contributes to the contraction, and no chart-count factor
is introduced.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold IsManifold Module Set Function Metric Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation.AuxNormBridge

section CompactFamily
variable {E F X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace X]

/-- The same manufactured cores also bound a finite family of local
coordinate functions, as needed for tensor coefficients in moving frames. -/
theorem protected_family_jet_prefix_bound
    (A : BufferedAtlas X E) (centers : Fin A.count → E) (radius : ℝ)
    (hBound : ∀ i, (A.chart i) '' A.inner i ⊆ closedBall (centers i) radius)
    (f : Fin A.count → E → F)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (A.chart i).target) (j : ℕ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ i k, k ≤ j → ∀ y ∈ protectedInnerClosure A i,
      ‖iteratedFDeriv ℝ k (f i) y‖ ≤ R := by
  classical
  have hEach : ∀ a : Fin A.count × Fin (j+1), ∃ R : ℝ,
      ∀ y ∈ protectedInnerClosure A a.1, ‖iteratedFDeriv ℝ (a.2 : ℕ) (f a.1) y‖ ≤ R := by
    intro a
    obtain ⟨R,hR⟩ := parameterRound2_coordinate_jets_bounded_of_compact
      (f a.1) (A.chart a.1).target (protectedInnerClosure A a.1) (protectedInnerClosure A a.1)
      (A.chart a.1).open_target (protectedInnerClosure_isCompact A centers radius hBound a.1)
      Subset.rfl (protectedInnerClosure_subset_target A a.1) (hf a.1) a.2
    exact ⟨R,fun y hy => hR ⟨⟨y,hy⟩,rfl⟩⟩
  choose R hR using hEach
  obtain ⟨B,hB⟩ := (Set.finite_range R).bddAbove
  refine ⟨max 0 B,le_max_left _ _,?_⟩
  intro i k hk y hy
  let a : Fin A.count × Fin (j+1) := (i,⟨k,by omega⟩)
  exact (hR a y hy).trans ((hB (mem_range_self a)).trans (le_max_right _ _))
end CompactFamily

section FiniteContraction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The two genuine tensor slots cost only n squared, never the number of
atlas labels.  This is an estimate for derivatives of the same finite sum. -/
theorem two_slot_sum_jet_le {n : ℕ} (f : Fin n → Fin n → E → ℝ)
    {x : E} (hf : ∀ r s, ContDiffAt ℝ ∞ (f r s) x) (k : ℕ) (C : ℝ)
    (hC : ∀ r s, ‖iteratedFDeriv ℝ k (f r s) x‖ ≤ C) :
    ‖iteratedFDeriv ℝ k (fun y => ∑ r, ∑ s, f r s y) x‖ ≤ (n : ℝ)^2*C := by
  classical
  have hsum : iteratedFDeriv ℝ k (fun y => ∑ r, ∑ s, f r s y) x =
      ∑ r, ∑ s, iteratedFDeriv ℝ k (f r s) x := by
    rw [iteratedFDeriv_fun_sum_apply (fun r _ =>
      (ContDiffAt.sum fun s _ => hf r s).of_le (by simp))]
    apply Finset.sum_congr rfl
    intro r _
    exact iteratedFDeriv_fun_sum_apply (fun s _ => (hf r s).of_le (by simp))
  rw [hsum]
  calc
    _ ≤ ∑ r, ‖∑ s, iteratedFDeriv ℝ k (f r s) x‖ := norm_sum_le _ _
    _ ≤ ∑ r : Fin n, ∑ _s : Fin n, C := by
      apply Finset.sum_le_sum
      intro r _
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun s _ => hC r s))
    _ = _ := by simp [nsmul_eq_mul,pow_two,mul_assoc]
end FiniteContraction

section TensorTransport
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℝ,E) ∞ X]
  {n : ℕ} {V : X → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]

/-- Internally manufactured all-order tensor profile.  The frame premises
are for the actual basis transition; the product source-tangent application
derives them from original coordinate transitions in the next module. -/
theorem original_tensor_native_profile_exists
    (A : BufferedAtlas X E) (hA : IsSmoothBufferedAtlas A)
    (centers : Fin A.count → E) (radius : ℝ)
    (hBound : ∀ i, (A.chart i) '' A.inner i ⊆ closedBall (centers i) radius)
    (Omega : Fin A.count → Set E) (hTarget : ∀ i, Omega i ⊆ (A.chart i).target)
    (T J : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hJ : ∀ k, 0 ≤ J k)
    (hTransition : ∀ (p i : Fin A.count) (k : ℕ), 1 ≤ k →
      ∀ y ∈ Omega p, y ∈ ((A.chart p).symm.trans (A.chart i)).source →
        ‖iteratedFDeriv ℝ k ((A.chart p).symm.trans (A.chart i)) y‖ ≤ T k)
    (b : Fin A.count → (x : X) → Basis (Fin n) ℝ (V x))
    (H : (x : X) → LinearMap.BilinForm ℝ (V x))
    (hH : ∀ i, ContDiffOn ℝ ∞ (tensorCoefficientField A b H i ∘ (A.chart i).symm)
      (A.chart i).target)
    (hFrame : ∀ p i a r, ContDiffOn ℝ ∞ (tensorFrameTransition A b p i a r)
      (bufferedChartOverlap A p i))
    (hFrameJets : ∀ p i a r k y, y ∈ Omega p → y ∈ bufferedChartOverlap A p i →
      ‖iteratedFDeriv ℝ k (tensorFrameTransition A b p i a r) y‖ ≤ J k) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧ ∀ i k y, y ∈ Omega i →
      ‖iteratedFDeriv ℝ k (tensorCoefficientField A b H i ∘ (A.chart i).symm) y‖ ≤ C k := by
  classical
  let f := fun i => tensorCoefficientField A b H i ∘ (A.chart i).symm
  have hOne : ∀ k (y : E), ‖iteratedFDeriv ℝ k (fun _ : E => (1 : ℝ)) y‖ ≤ 1 := by
    intro k y
    cases k with
    | zero => simp
    | succ k => simp only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero,zero_le_one]
  have hOrder : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ p y, y ∈ Omega p → ‖iteratedFDeriv ℝ k (f p) y‖ ≤ C := by
    intro k
    obtain ⟨R,hR,hCore⟩ := protected_family_jet_prefix_bound A centers radius hBound f hH k
    let K := tensorTransferCore (fun _ => 1) T J k*R
    have hK : 0 ≤ K := mul_nonneg
      (tensorTransferCore_nonneg (fun _ => zero_le_one) hT hJ k) hR
    refine ⟨(n:ℝ)^2*K,mul_nonneg (sq_nonneg _) hK,?_⟩
    intro p y hy
    let x := (A.chart p).symm y
    obtain ⟨i,hi⟩ := A.cover x
    let O := bufferedChartOverlap A p i
    let t := A.chart i ∘ (A.chart p).symm
    have hyO : y ∈ O := ⟨hTarget p hy,hi⟩
    have hO : IsOpen O := bufferedChartOverlap_open A p i
    have ht : ContDiffOn ℝ ∞ t O := bufferedTransition_contDiffOn A hA p i
    have hmap : MapsTo t O (A.chart i).target := fun z hz =>
      (A.chart i).map_source (A.inner_subset i hz.2)
    have htd : ∀ l, 1 ≤ l → ‖iteratedFDeriv ℝ l t y‖ ≤ T l := by
      intro l hl
      exact hTransition p i l hl y hy ⟨hTarget p hy,A.inner_subset i hi⟩
    apply tensor_jet_le_of_components ((hH p).contDiffAt ((A.chart p).open_target.mem_nhds (hTarget p hy)))
      k ((n:ℝ)^2*K) (mul_nonneg (sq_nonneg _) hK)
    intro a
    obtain ⟨⟨a,c⟩,rfl⟩ := finProdFinEquiv.surjective a
    let term := fun r s z => (tensorFrameTransition A b p i a r z * tensorFrameTransition A b p i c s z) *
      f i (t z) (finProdFinEquiv (r,s))
    have hterm : ∀ r s, ContDiffOn ℝ ∞ (term r s) O := by
      intro r s
      exact ((hFrame p i a r).mul (hFrame p i c s)).mul
        (((contDiffOn_pi.mp (hH i)) (finProdFinEquiv (r,s))).comp ht hmap)
    have htermBound : ∀ r s, ‖iteratedFDeriv ℝ k (term r s) y‖ ≤ K := by
      intro r s
      have hb := tensor_transferred_entry_jet_le (fun _ => 1) T J
        (fun _ => zero_le_one) hT hJ hO (A.chart i).open_target contDiffOn_const
        (hFrame p i a r) (hFrame p i c s)
        ((contDiffOn_pi.mp (hH i)) (finProdFinEquiv (r,s))) ht hmap hyO k R
        (fun l => hOne l y) (fun l => hFrameJets p i a r l y hy hyO)
        (fun l => hFrameJets p i c s l y hy hyO) htd (by
          intro l hl
          exact (tensor_component_jet_le ((hH i).contDiffAt
            ((A.chart i).open_target.mem_nhds (hmap hyO))) (finProdFinEquiv (r,s)) l).trans
              (hCore i l hl (t y) (mem_protectedInnerClosure A i x hi)))
      simpa only [one_pow,one_mul] using hb
    have hEq : (fun z => f p z (finProdFinEquiv (a,c))) =ᶠ[𝓝 y]
        (fun z => ∑ r, ∑ s, term r s z) := by
      filter_upwards [hO.mem_nhds hyO] with z hz
      have hx : (A.chart p).symm z ∈ (A.chart i).source := A.inner_subset i hz.2
      have hInv := (A.chart i).left_inv hx
      change tensorFrameComponents (b p ((A.chart p).symm z)) (H ((A.chart p).symm z))
        (finProdFinEquiv (a,c)) = _
      rw [tensorFrameComponents_change (b i ((A.chart p).symm z))]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      dsimp only [term,f,t,Function.comp_apply,tensorCoefficientField,tensorFrameTransition]
      rw [hInv]
      ring
    rw [(hEq.iteratedFDeriv ℝ k).eq_of_nhds]
    exact two_slot_sum_jet_le term (fun r s => (hterm r s).contDiffAt (hO.mem_nhds hyO)) k K htermBound
  choose C hC hBounds using hOrder
  exact ⟨C,hC,fun i k y hy => hBounds k i y hy⟩
end TensorTransport

end GlobalEmbedding.Continuation.AuxNormBridge

#print axioms GlobalEmbedding.Continuation.AuxNormBridge.protected_family_jet_prefix_bound
#print axioms GlobalEmbedding.Continuation.AuxNormBridge.two_slot_sum_jet_le
#print axioms GlobalEmbedding.Continuation.AuxNormBridge.original_tensor_native_profile_exists
