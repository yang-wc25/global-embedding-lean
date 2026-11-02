import NormalPolar.PassiveOriginalRawNorm

/-! The original finite-atlas maximum and cumulative weighted budget of
literal passive coordinate fields. Repeated observations in the new
parameter charts have no chart-count factor. No primitive smoothness or
desired output estimate is needed for these raw partial-norm comparisons. -/

noncomputable section
open Set Function
open scoped ContDiff Topology ENNReal Classical
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.Paper

variable {n d q : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem passiveOriginal_raw_paperAtlasCj_le (j : ℕ)
    (f : ι → (Fin n → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin n → ℝ)) (hO : ∀ i, IsOpen (O i))
    (source : κ → ι) (D T : κ → Set (Fin (n+d) → ℝ))
    (hD : ∀ i, IsOpen (D i))
    (hDO : ∀ i, MapsTo (passiveOriginalSourceProjection (d := d)) (D i) (O (source i)))
    (hTD : ∀ i, T i ⊆ D i)
    (hTS : ∀ i, MapsTo (passiveOriginalSourceProjection (d := d)) (T i) (S (source i))) :
    paperAtlasCj j (fun i => f (source i) ∘ passiveOriginalSourceProjection (d := d)) D T ≤
      paperAtlasCj j f O S := by
  unfold paperAtlasCj
  refine iSup_le fun i => ?_
  exact (passiveOriginal_raw_paperCoordinateCj_le j (f (source i)) (O (source i))
    (S (source i)) (hO _) (D i) (T i) (hD _) (hDO _) (hTD _) (hTS _)).trans
      (le_iSup_of_le (source i) le_rfl)

theorem passiveOriginal_raw_paperAtlasWeighted_le (base j : ℕ) (ell : ℝ)
    (f : ι → (Fin n → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin n → ℝ)) (hO : ∀ i, IsOpen (O i))
    (source : κ → ι) (D T : κ → Set (Fin (n+d) → ℝ))
    (hD : ∀ i, IsOpen (D i))
    (hDO : ∀ i, MapsTo (passiveOriginalSourceProjection (d := d)) (D i) (O (source i)))
    (hTD : ∀ i, T i ⊆ D i)
    (hTS : ∀ i, MapsTo (passiveOriginalSourceProjection (d := d)) (T i) (S (source i))) :
    paperAtlasWeighted base j ell
      (fun i => f (source i) ∘ passiveOriginalSourceProjection (d := d)) D T ≤
      paperAtlasWeighted base j ell f O S := by
  apply Finset.sum_le_sum
  intro a ha
  simpa only [mul_comm] using
    mul_le_mul_left (passiveOriginal_raw_paperAtlasCj_le (a+base) f O S hO source D T
      hD hDO hTD hTS) (ENNReal.ofReal ell ^ a)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveOriginal_raw_paperAtlasWeighted_le
