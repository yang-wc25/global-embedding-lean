import FaithfulIncrements.GivenFiniteEnvelope
import FaithfulIncrements.LocalPrimaryNeighborhoods
import Smoothing.ParameterRound2CompactNorms

/-!
# Original norm finiteness from an actual buffered smooth extension

An original norm domain can be open and need not have compact closure inside
its own chart target. A buffered parent chart may instead control the same
coordinate function on a larger open set. This file proves finiteness of the
literal original norm in exactly that situation; neither its sampling set nor
its differentiation domain is replaced.

The second part checks that the actual internal primary-domain localization
does not increase the given finite input profile. All native functions remain
the original functions.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation.FaithfulIncrements

/-- The compact control carrier is in the parent's smooth open region, not
necessarily inside the original differentiation domain. The original norm
is preserved by the already proved open-domain locality identity. -/
theorem weighted_finite_of_smooth_extension
    {ι : Type*} [Fintype ι] {a q : ℕ}
    (f : ι → (Fin a → ℝ) → Fin q → ℝ)
    (O S U K : ι → Set (Fin a → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hU : ∀ i, IsOpen (U i)) (hK : ∀ i, IsCompact (K i))
    (hSK : ∀ i, S i ⊆ K i) (hKU : ∀ i, K i ⊆ U i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (U i))
    (base j : ℕ) (ell : ℝ) :
    paperAtlasWeighted base j ell f O S ≠ ⊤ := by
  let V := fun i => O i ∩ U i
  have hV : ∀ i, IsOpen (V i) := fun i => (hO i).inter (hU i)
  have hSV : ∀ i, S i ⊆ V i := fun i y hy => ⟨hSO i hy, hKU i (hSK i hy)⟩
  rw [actual_paperAtlasWeighted_open_restrict base j ell f O V S hO hV
    (fun _ => inter_subset_left) hSV]
  exact paperAtlasWeighted_ne_top base j ell f V S hV hSV
    (fun i => (hf i).mono inter_subset_right)
    (fun i k _ => parameterRound2_coordinate_jets_bounded_of_compact
      (f i) (U i) (S i) (K i) (hU i) (hK i) (hSK i) (hKU i) (hf i) k)

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

/-- This exact comparison includes the provided free normal, not a new
choice of normal, and includes the full parameter-phase differential. -/
theorem localPrimaryData_given_profile_le
    (Data : IncrementsOriginalNativeData n d N M P)
    (V : Set P) (domain : Fin Data.primaryCount → Set (P × M))
    (hOld : ∀ nu, IsOpen (Data.primaryDomain nu)) (hNew : ∀ nu, IsOpen (domain nu))
    (hSub : ∀ nu, domain nu ⊆ Data.primaryDomain nu)
    (j : ℕ) (ell : ℝ) :
    actualOriginalGivenInputProfile (localPrimaryData Data V domain) j ell ≤
      actualOriginalGivenInputProfile Data j ell := by
  have hPrimary (nu : Fin Data.primaryCount) {a : ℕ}
      (f : (Fin Data.atlas.count × Fin Data.parameterCount) → (Fin (n+d) → ℝ) → Fin a → ℝ) :=
    localPrimaryData_primary_weighted_le Data V domain hOld hNew hSub nu f 0 j ell
  unfold actualOriginalGivenInputProfile incrementsOriginalInputProfileWithLinear
    incrementsOriginalCoreInputProfile
  apply max_le_max
  · apply max_le_max
    · apply max_le_max le_rfl
      apply max_le_max le_rfl
      apply iSup_mono
      intro nu
      exact max_le_max (hPrimary nu _)
        (max_le_max (hPrimary nu _) (hPrimary nu _))
    · exact iSup_mono (fun nu => hPrimary nu _)
  · exact max_le_max (iSup_mono (fun nu => hPrimary nu _)) le_rfl

/-- Every prescribed finite original input bound transfers to the actual
localized data. The transfer uses the same scale and does not introduce a
budget for any higher derivative. -/
theorem localPrimaryData_given_prefix
    (Data : IncrementsOriginalNativeData n d N M P)
    (V : Set P) (domain : Fin Data.primaryCount → Set (P × M))
    (hOld : ∀ nu, IsOpen (Data.primaryDomain nu)) (hNew : ∀ nu, IsOpen (domain nu))
    (hSub : ∀ nu, domain nu ⊆ Data.primaryDomain nu)
    (J : ℕ) (ell : ℝ) (allowed : ℕ → ℝ)
    (hFinite : ∀ j, j ≤ J → actualOriginalGivenInputProfile Data j ell ≠ ⊤)
    (hBudget : ∀ j, j ≤ J →
      (actualOriginalGivenInputProfile Data j ell).toReal ≤ allowed j) :
    ∀ j, j ≤ J →
      actualOriginalGivenInputProfile (localPrimaryData Data V domain) j ell ≠ ⊤ ∧
      (actualOriginalGivenInputProfile (localPrimaryData Data V domain) j ell).toReal ≤ allowed j := by
  intro j hj
  have h := localPrimaryData_given_profile_le Data V domain hOld hNew hSub j ell
  exact ⟨ne_top_of_le_ne_top (hFinite j hj) h,
    (ENNReal.toReal_mono (hFinite j hj) h).trans (hBudget j hj)⟩

end GlobalEmbedding.Continuation.FaithfulIncrements

#print axioms GlobalEmbedding.Continuation.FaithfulIncrements.weighted_finite_of_smooth_extension
#print axioms GlobalEmbedding.Continuation.FaithfulIncrements.localPrimaryData_given_prefix
