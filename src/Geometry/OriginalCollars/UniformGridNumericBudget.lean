import OriginalCollars.OriginalObserverCutoffFinitePrefix

/-!
# A numerical grid reserve bounds the same packet's observer cutoffs

The displayed upper profile depends only on dimensions, a single positive
grid reserve and the original raw/transition profiles.  It has no atlas,
index family, selected chart or constructed derivative as an argument.
The reserve is manufactured by a finite maximum of the same packet's
literal refinement-factor/buffer ratios.  This aggregation preserves the
packet and does not by itself assert a reserve uniform over arbitrary
uncontrolled input geometries.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation.OriginalCollars
open OriginalIncrements

variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

def uniformOriginalGridCutoffPrefix (H : ℝ) (j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (j+1), H^k * actualRefinementCutoffJetCost X k

theorem uniformOriginalGridCutoffPrefix_nonneg (H : ℝ) (hH : 0 ≤ H) (j : ℕ) :
    0 ≤ uniformOriginalGridCutoffPrefix X H j :=
  Finset.sum_nonneg (fun k _ =>
    mul_nonneg (pow_nonneg hH _) (actualRefinementCutoffJetCost_nonneg X k))

theorem originalGridCutoffPrefix_le_uniform
    (mu Mb buffer H : ℝ) (hmu : 0 < mu) (hMb : 0 ≤ Mb) (hbuffer : 0 < buffer)
    (hRatio : actualPhaseRefinementFactor mu Mb / buffer ≤ H) (j : ℕ) :
    originalGridCutoffPrefix X mu Mb buffer j ≤ uniformOriginalGridCutoffPrefix X H j := by
  apply Finset.sum_le_sum
  intro k hk
  have hquot : 0 ≤ actualPhaseRefinementFactor mu Mb / buffer :=
    div_nonneg (actualPhaseRefinementFactor_pos hmu hMb).le hbuffer.le
  calc
    originalGridCutoffBudget X mu Mb buffer k =
        (actualPhaseRefinementFactor mu Mb / buffer)^k * actualRefinementCutoffJetCost X k := by
      simp only [originalGridCutoffBudget, div_pow]
      ring
    _ ≤ H^k * actualRefinementCutoffJetCost X k :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hquot hRatio k)
        (actualRefinementCutoffJetCost_nonneg X k)

def uniformOriginalObserverCutoffProfile (m d : ℕ) (H : ℝ)
    (BS TS BP TP Parameter Spatial : ℕ → ℝ) (Ds Dp j : ℕ) : ℝ :=
  actualFastChartTransferCost (fun k => max (Parameter k) (Spatial k)) j *
    (2^j * (‖ContinuousLinearMap.mul ℝ ℝ‖ *
      (∑ k ∈ Finset.range (j+1), round4ParentProfile BS TS BP TP Ds Dp k)) *
      uniformOriginalGridCutoffPrefix
        (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin (m+1))) H j)

theorem uniformOriginalObserverCutoffProfile_nonneg
    (m d : ℕ) (H : ℝ) (hH : 0 ≤ H)
    (BS TS BP TP Parameter Spatial : ℕ → ℝ)
    (hBS : ∀ k, 0 ≤ BS k) (hTS : ∀ k, 0 ≤ TS k)
    (hBP : ∀ k, 0 ≤ BP k) (hTP : ∀ k, 0 ≤ TP k)
    (hParameter : ∀ k, 0 ≤ Parameter k) (hSpatial : ∀ k, 0 ≤ Spatial k)
    (Ds Dp j : ℕ) :
    0 ≤ uniformOriginalObserverCutoffProfile m d H BS TS BP TP Parameter Spatial Ds Dp j := by
  apply mul_nonneg
  · exact actualFastChartTransferCost_nonneg _
      (fun k => (hParameter k).trans (le_max_left _ _)) j
  · exact mul_nonneg (mul_nonneg (by positivity)
      (mul_nonneg (ContinuousLinearMap.mul ℝ ℝ).opNorm_nonneg
        (Finset.sum_nonneg (fun k _ => round4ParentProfile_nonneg hBS hTS hBP hTP Ds Dp k))))
      (uniformOriginalGridCutoffPrefix_nonneg _ H hH j)

theorem uniformOriginalObserverCutoffProfile_prefix_congr
    (m d : ℕ) (H : ℝ)
    (BS BS' TS TS' BP BP' TP TP' Parameter Parameter' Spatial Spatial' : ℕ → ℝ)
    (Ds Dp j : ℕ)
    (hBS : ∀ k, k ≤ j → BS k = BS' k) (hTS : ∀ k, k ≤ j → TS k = TS' k)
    (hBP : ∀ k, k ≤ j → BP k = BP' k) (hTP : ∀ k, k ≤ j → TP k = TP' k)
    (hParameter : ∀ k, k ≤ j → Parameter k = Parameter' k)
    (hSpatial : ∀ k, k ≤ j → Spatial k = Spatial' k) :
    uniformOriginalObserverCutoffProfile m d H BS TS BP TP Parameter Spatial Ds Dp j =
      uniformOriginalObserverCutoffProfile m d H BS' TS' BP' TP' Parameter' Spatial' Ds Dp j := by
  have hTransfer := cutoffTransferCost_prefix_congr
    (fun k => max (Parameter k) (Spatial k)) (fun k => max (Parameter' k) (Spatial' k)) j
    (fun k hk => by rw [hParameter k hk,hSpatial k hk])
  have hParent : (∑ k ∈ Finset.range (j+1), round4ParentProfile BS TS BP TP Ds Dp k) =
      ∑ k ∈ Finset.range (j+1), round4ParentProfile BS' TS' BP' TP' Ds Dp k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkj : k ≤ j := by simpa using hk
    exact round4ParentProfile_congr_prefix Ds Dp k
      (fun l hl => hBS l (hl.trans hkj)) (fun l hl => hTS l (hl.trans hkj))
      (fun l hl => hBP l (hl.trans hkj)) (fun l hl => hTP l (hl.trans hkj))
  simp only [uniformOriginalObserverCutoffProfile,hTransfer,hParent]

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

theorem originalObserverCutoffProfile_le_uniform
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (supply : OriginalBudgetedPrimarySupply Data theta)
    (H : ℝ) (hH : 0 ≤ H)
    (hRatio : ∀ nu i,
      actualPhaseRefinementFactor (supply.mu nu i) (supply.Mb nu i) / supply.buffer nu i ≤ H)
    (BS TS BP TP Parameter Spatial : ℕ → ℝ)
    (hBS : ∀ k, 0 ≤ BS k) (hTS : ∀ k, 0 ≤ TS k)
    (hBP : ∀ k, 0 ≤ BP k) (hTP : ∀ k, 0 ≤ TP k)
    (hParameter : ∀ k, 0 ≤ Parameter k) (hSpatial : ∀ k, 0 ≤ Spatial k)
    (Ds Dp j : ℕ) :
    originalObserverCutoffProfile Data theta supply BS TS BP TP Parameter Spatial Ds Dp j ≤
      uniformOriginalObserverCutoffProfile m d H BS TS BP TP Parameter Spatial Ds Dp j := by
  unfold originalObserverCutoffProfile round3PreparedFiniteMaximum
  apply Finset.max'_le
  intro y hy
  rcases Finset.mem_insert.mp hy with rfl | hy
  · exact uniformOriginalObserverCutoffProfile_nonneg m d H hH
      BS TS BP TP Parameter Spatial hBS hTS hBP hTP hParameter hSpatial Ds Dp j
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    apply mul_le_mul_of_nonneg_left
    · apply mul_le_mul_of_nonneg_left
      · exact originalGridCutoffPrefix_le_uniform _ _ _ _ H
          (supply.mu_pos a.1 a.2) (supply.Mb_nonneg a.1 a.2)
          (supply.buffer_pos a.1 a.2) (hRatio a.1 a.2) j
      · exact mul_nonneg (by positivity)
          (mul_nonneg (ContinuousLinearMap.mul ℝ ℝ).opNorm_nonneg
            (Finset.sum_nonneg (fun k _ => round4ParentProfile_nonneg hBS hTS hBP hTP Ds Dp k)))
    · exact actualFastChartTransferCost_nonneg _
        (fun k => (hParameter k).trans (le_max_left _ _)) j

/-- The scalar is chosen from the same actual packet before any observation
order or requested entrance budget.  No bound for it is an input. -/
def originalGridNumericReserve
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (supply : OriginalBudgetedPrimarySupply Data theta) : ℝ :=
  1 + round3PreparedFiniteMaximum
    (fun a : Fin Data.primaryCount × (Fin Data.atlas.count × Fin Data.parameterCount) =>
      actualPhaseRefinementFactor (supply.mu a.1 a.2) (supply.Mb a.1 a.2) / supply.buffer a.1 a.2)

theorem originalGridNumericReserve_pos
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (supply : OriginalBudgetedPrimarySupply Data theta) :
    0 < originalGridNumericReserve Data theta supply :=
  add_pos_of_pos_of_nonneg zero_lt_one (round3PreparedFiniteMaximum_nonneg _)

theorem originalGridNumericReserve_bound
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (supply : OriginalBudgetedPrimarySupply Data theta)
    (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount) :
    actualPhaseRefinementFactor (supply.mu nu i) (supply.Mb nu i) / supply.buffer nu i ≤
      originalGridNumericReserve Data theta supply := by
  have h := round3PreparedFiniteMaximum_bound
    (fun a : Fin Data.primaryCount × (Fin Data.atlas.count × Fin Data.parameterCount) =>
      actualPhaseRefinementFactor (supply.mu a.1 a.2) (supply.Mb a.1 a.2) / supply.buffer a.1 a.2)
    (nu,i)
  exact h.trans (le_add_of_nonneg_left zero_le_one)

theorem originalObserverCutoffProfile_le_numeric_reserve
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (supply : OriginalBudgetedPrimarySupply Data theta)
    (BS TS BP TP Parameter Spatial : ℕ → ℝ)
    (hBS : ∀ k, 0 ≤ BS k) (hTS : ∀ k, 0 ≤ TS k)
    (hBP : ∀ k, 0 ≤ BP k) (hTP : ∀ k, 0 ≤ TP k)
    (hParameter : ∀ k, 0 ≤ Parameter k) (hSpatial : ∀ k, 0 ≤ Spatial k)
    (Ds Dp j : ℕ) :
    originalObserverCutoffProfile Data theta supply BS TS BP TP Parameter Spatial Ds Dp j ≤
      uniformOriginalObserverCutoffProfile m d (originalGridNumericReserve Data theta supply)
        BS TS BP TP Parameter Spatial Ds Dp j :=
  originalObserverCutoffProfile_le_uniform Data theta supply _
    (originalGridNumericReserve_pos Data theta supply).le (originalGridNumericReserve_bound Data theta supply)
    BS TS BP TP Parameter Spatial hBS hTS hBP hTP hParameter hSpatial Ds Dp j

end GlobalEmbedding.Continuation.OriginalCollars

#print axioms GlobalEmbedding.Continuation.OriginalCollars.originalObserverCutoffProfile_le_numeric_reserve
