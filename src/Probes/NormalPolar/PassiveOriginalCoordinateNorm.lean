import GlobalEmbedding.Paper.PaperCoordinateNormBridge
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Passive extension in the original coordinate partial norm

The domain is the original Pi space `Fin (n+d) → ℝ`, not an equivalent
Euclidean norm.  Actual coordinate derivatives in added parameter directions
vanish; the other derivatives are the original source derivatives.  Thus
adding a passive parameter keeps every original coordinate Cj bound and its
weighted atlas budget, with constant one and without rechoosing the function
at different orders.
-/

noncomputable section
open Set Function
open scoped ContDiff Topology BigOperators ENNReal Classical
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.Paper

variable {n d q : ℕ}

/-- The literal original source coordinates inside the full Pi vector. -/
def passiveOriginalSourceProjection : (Fin (n+d) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (Fin.castAdd d i))

@[simp] theorem passiveOriginalSourceProjection_apply (y : Fin (n+d) → ℝ) (i : Fin n) :
    passiveOriginalSourceProjection (d := d) y i = y (Fin.castAdd d i) := rfl

theorem passiveOriginalSourceProjection_norm_le_one :
    ‖passiveOriginalSourceProjection (n := n) (d := d)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro y
  rw [one_mul]
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg y)).mpr
    (fun i => norm_le_pi_norm y (Fin.castAdd d i))

theorem passiveOriginalSourceProjection_single_source (i : Fin n) :
    passiveOriginalSourceProjection (d := d) (Pi.single (Fin.castAdd d i) 1) =
      Pi.single i 1 := by
  ext j
  simp only [passiveOriginalSourceProjection_apply,Pi.single_apply]
  simp

theorem passiveOriginalSourceProjection_single_parameter (i : Fin (n+d)) (hi : n ≤ i.val) :
    passiveOriginalSourceProjection (n := n) (d := d) (Pi.single i 1) = 0 := by
  ext j
  have hne : i ≠ Fin.castAdd d j := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castAdd] at this
    omega
  simp only [passiveOriginalSourceProjection_apply,Pi.single_apply,Pi.zero_apply]
  simp [hne,Ne.symm hne]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem passiveOriginalSourceProjection_iteratedFDeriv
    (f : (Fin n → ℝ) → V) (O : Set (Fin n → ℝ))
    (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
    (y : Fin (n+d) → ℝ) (hy : passiveOriginalSourceProjection y ∈ O) (k : ℕ) :
    iteratedFDeriv ℝ k (f ∘ passiveOriginalSourceProjection (d := d)) y =
      (iteratedFDeriv ℝ k f (passiveOriginalSourceProjection y)).compContinuousLinearMap
        (fun _ => passiveOriginalSourceProjection (d := d)) := by
  let L := passiveOriginalSourceProjection (n := n) (d := d)
  have hp : IsOpen (L ⁻¹' O) := hO.preimage L.continuous
  have h := L.iteratedFDerivWithin_comp_right (i := k) hf hO.uniqueDiffOn hp.uniqueDiffOn hy (by simp)
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hp.uniqueDiffOn
      (((hf.comp_continuousLinearMap L).contDiffAt (hp.mem_nhds hy)).of_le (by simp)) hy,
    iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn
      ((hf.contDiffAt (hO.mem_nhds hy)).of_le (by simp)) hy] at h
  exact h

/-- Every original partial in an added parameter direction is exactly zero;
all-source words are exactly the corresponding original derivative. -/
theorem passiveOriginalSourceProjection_jet_coefficient
    (f : (Fin n → ℝ) → V) (O : Set (Fin n → ℝ))
    (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
    (y : Fin (n+d) → ℝ) (hy : passiveOriginalSourceProjection y ∈ O)
    (k : ℕ) (σ : Fin k → Fin (n+d)) :
    (∃ σ₀ : Fin k → Fin n,
      iteratedFDeriv ℝ k (f ∘ passiveOriginalSourceProjection (d := d)) y
        (fun i => Pi.single (σ i) 1) =
      iteratedFDeriv ℝ k f (passiveOriginalSourceProjection y)
        (fun i => Pi.single (σ₀ i) 1)) ∨
    iteratedFDeriv ℝ k (f ∘ passiveOriginalSourceProjection (d := d)) y
      (fun i => Pi.single (σ i) 1) = 0 := by
  rw [passiveOriginalSourceProjection_iteratedFDeriv f O hO hf y hy k]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  by_cases hσ : ∀ i, (σ i).val < n
  · left
    let σ₀ : Fin k → Fin n := fun i => ⟨(σ i).val,hσ i⟩
    refine ⟨σ₀,?_⟩
    congr 1
    funext i
    have hs : σ i = Fin.castAdd d (σ₀ i) := Fin.ext rfl
    rw [hs,passiveOriginalSourceProjection_single_source]
  · right
    obtain ⟨i,hi⟩ := not_forall.mp hσ
    exact (iteratedFDeriv ℝ k f (passiveOriginalSourceProjection y)).map_coord_zero i
      (passiveOriginalSourceProjection_single_parameter (σ i) (Nat.le_of_not_gt hi))

/-- Original component partial norms do not grow.  The actual added
parameter sampling domain can be any subset of the full inverse image. -/
theorem passiveOriginal_paperCoordinateCj_le (j : ℕ)
    (f : (Fin n → ℝ) → Fin q → ℝ) (O S : Set (Fin n → ℝ))
    (hO : IsOpen O) (hSO : S ⊆ O) (hf : ContDiffOn ℝ ∞ f O)
    (Samples : Set (Fin (n+d) → ℝ))
    (hSamples : MapsTo (passiveOriginalSourceProjection (d := d)) Samples S) :
    paperCoordinateCj j (f ∘ passiveOriginalSourceProjection (d := d))
      ((passiveOriginalSourceProjection (d := d)) ⁻¹' O) Samples ≤
      paperCoordinateCj j f O S := by
  let L := passiveOriginalSourceProjection (n := n) (d := d)
  have hp : IsOpen (L ⁻¹' O) := hO.preimage L.continuous
  have hSP : Samples ⊆ L ⁻¹' O := fun _ hy => hSO (hSamples hy)
  rw [paperCoordinateCj_eq_coordinateJetGauge j _ _ _ hp hSP (hf.comp_continuousLinearMap L),
    paperCoordinateCj_eq_coordinateJetGauge j f O S hO hSO hf]
  refine iSup_le fun k => iSup_le fun y => iSup_le fun σ => iSup_le fun c => ?_
  rcases passiveOriginalSourceProjection_jet_coefficient f O hO hf y (hSP y.property) k.val σ with
    ⟨σ₀,heq⟩ | heq
  · rw [heq]
    exact coordinate_jet_coefficient_le_gauge f S (by omega) ⟨L y,hSamples y.property⟩ σ₀ c
  · rw [heq]
    simp only [Pi.zero_apply,norm_zero,ENNReal.ofReal_zero]
    exact bot_le

/-- The same unchanged constants control every component of the original
finite atlas maximum, including repeated parameter chart observations. -/
theorem passiveOriginal_paperAtlasCj_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (j : ℕ) (f : ι → (Fin n → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin n → ℝ)) (hO : ∀ i, IsOpen (O i))
    (hSO : ∀ i, S i ⊆ O i) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i))
    (source : κ → ι) (Samples : κ → Set (Fin (n+d) → ℝ))
    (hSamples : ∀ i, MapsTo (passiveOriginalSourceProjection (d := d)) (Samples i) (S (source i))) :
    paperAtlasCj j (fun i => f (source i) ∘ passiveOriginalSourceProjection (d := d))
      (fun i => (passiveOriginalSourceProjection (d := d)) ⁻¹' O (source i)) Samples ≤
      paperAtlasCj j f O S := by
  unfold paperAtlasCj
  refine iSup_le fun i => ?_
  exact (passiveOriginal_paperCoordinateCj_le j (f (source i)) (O (source i)) (S (source i))
    (hO _) (hSO _) (hf _) (Samples i) (hSamples i)).trans (le_iSup_of_le (source i) le_rfl)

/-- One function and one lifted domain satisfy every order.  The weighted
paper budget is retained with no extra dimension or chart-count factor. -/
theorem passiveOriginal_paperAtlasWeighted_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (base j : ℕ) (ell : ℝ) (f : ι → (Fin n → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin n → ℝ)) (hO : ∀ i, IsOpen (O i))
    (hSO : ∀ i, S i ⊆ O i) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i))
    (source : κ → ι) (Samples : κ → Set (Fin (n+d) → ℝ))
    (hSamples : ∀ i, MapsTo (passiveOriginalSourceProjection (d := d)) (Samples i) (S (source i))) :
    paperAtlasWeighted base j ell
      (fun i => f (source i) ∘ passiveOriginalSourceProjection (d := d))
      (fun i => (passiveOriginalSourceProjection (d := d)) ⁻¹' O (source i)) Samples ≤
      paperAtlasWeighted base j ell f O S := by
  apply Finset.sum_le_sum
  intro a ha
  simpa only [mul_comm] using
    mul_le_mul_left (passiveOriginal_paperAtlasCj_le (a+base) f O S hO hSO hf source Samples hSamples)
      (ENNReal.ofReal ell ^ a)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveOriginalSourceProjection_jet_coefficient
#print axioms GlobalEmbedding.Continuation.passiveOriginal_paperCoordinateCj_le
#print axioms GlobalEmbedding.Continuation.passiveOriginal_paperAtlasWeighted_le
