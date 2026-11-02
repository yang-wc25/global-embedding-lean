import OriginalCollars.ConditionedOriginalCutoffBudget

/-! Finite-prefix dependence of the exact original-observer cutoff formula.
The same actual packet and its low geometric constants are held fixed;
only raw-parent and original transition orders through j are read at j. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation.OriginalCollars
open OriginalIncrements

theorem cutoffTransferCost_prefix_congr
    (T T' : ℕ → ℝ) (j : ℕ) (h : ∀ k, k ≤ j → T k = T' k) :
    actualFastChartTransferCost T j = actualFastChartTransferCost T' j := by
  have hsum : (∑ k ∈ Finset.range (j+1), T k) = ∑ k ∈ Finset.range (j+1), T' k := by
    apply Finset.sum_congr rfl
    intro k hk
    exact h k (by simpa using hk)
  simp only [actualFastChartTransferCost,bufferedTransitionPrefix,hsum]

theorem originalParentGridHostCutoffProfile_prefix_congr
    (m d Ds Dp j : ℕ) (mu Mb buffer : ℝ)
    (BS BS' TS TS' BP BP' TP TP' : ℕ → ℝ)
    (hBS : ∀ k, k ≤ j → BS k = BS' k) (hTS : ∀ k, k ≤ j → TS k = TS' k)
    (hBP : ∀ k, k ≤ j → BP k = BP' k) (hTP : ∀ k, k ≤ j → TP k = TP' k) :
    originalParentGridHostCutoffProfile m d mu Mb buffer BS TS BP TP Ds Dp j =
      originalParentGridHostCutoffProfile m d mu Mb buffer BS' TS' BP' TP' Ds Dp j := by
  have hsum : (∑ k ∈ Finset.range (j+1), round4ParentProfile BS TS BP TP Ds Dp k) =
      ∑ k ∈ Finset.range (j+1), round4ParentProfile BS' TS' BP' TP' Ds Dp k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkj : k ≤ j := by simpa using hk
    exact round4ParentProfile_congr_prefix Ds Dp k
      (fun l hl => hBS l (hl.trans hkj)) (fun l hl => hTS l (hl.trans hkj))
      (fun l hl => hBP l (hl.trans hkj)) (fun l hl => hTP l (hl.trans hkj))
  simp only [originalParentGridHostCutoffProfile,hsum]

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

theorem originalObserverCutoffProfile_prefix_congr
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (supply : OriginalBudgetedPrimarySupply Data theta)
    (BS BS' TS TS' BP BP' TP TP' Parameter Parameter' Spatial Spatial' : ℕ → ℝ)
    (Ds Dp j : ℕ)
    (hBS : ∀ k, k ≤ j → BS k = BS' k) (hTS : ∀ k, k ≤ j → TS k = TS' k)
    (hBP : ∀ k, k ≤ j → BP k = BP' k) (hTP : ∀ k, k ≤ j → TP k = TP' k)
    (hParameter : ∀ k, k ≤ j → Parameter k = Parameter' k)
    (hSpatial : ∀ k, k ≤ j → Spatial k = Spatial' k) :
    originalObserverCutoffProfile Data theta supply BS TS BP TP Parameter Spatial Ds Dp j =
      originalObserverCutoffProfile Data theta supply BS' TS' BP' TP' Parameter' Spatial' Ds Dp j := by
  have hTransfer := cutoffTransferCost_prefix_congr
    (fun k => max (Parameter k) (Spatial k)) (fun k => max (Parameter' k) (Spatial' k)) j
    (fun k hk => by rw [hParameter k hk,hSpatial k hk])
  unfold originalObserverCutoffProfile
  congr 1
  funext a
  rw [hTransfer,originalParentGridHostCutoffProfile_prefix_congr m d Ds Dp j _ _ _
    BS BS' TS TS' BP BP' TP TP' hBS hTS hBP hTP]

end GlobalEmbedding.Continuation.OriginalCollars
#print axioms GlobalEmbedding.Continuation.OriginalCollars.originalObserverCutoffProfile_prefix_congr
