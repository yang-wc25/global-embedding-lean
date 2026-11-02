import NormalPolar.PassiveOriginalParameterAtlas
import Smoothing.ParameterRound2CompactNorms

/-! Genuine finite all-order costs for the actual parameter transitions
of the constructed compact atlas. Their forward maps are globally smooth,
so the entire compact Q_i controls the transition into every second chart,
including points approaching that chart's source boundary. The coordinate
norm is the original Pi-domain scalar-partial norm. One cost sequence is
fixed before the derivative scale is supplied. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold IsManifold GlobalEmbedding.Paper
open scoped ContDiff Topology ENNReal Classical
namespace GlobalEmbedding.Continuation

variable {d : ℕ} {P : Type*} [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

def passiveOriginalParameterTransition
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (ik : Fin B.count × Fin B.count) (y : Fin d → ℝ) : Fin d → ℝ :=
  EuclideanSpace.equiv (Fin d) ℝ
    (B.chart ik.2 ((B.chart ik.1).symm ((EuclideanSpace.equiv (Fin d) ℝ).symm y)))

def passiveOriginalParameterTransitionDomain
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (ik : Fin B.count × Fin B.count) : Set (Fin d → ℝ) :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm ⁻¹' (B.chart ik.1).target

def passiveOriginalParameterTransitionSample
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d)))
    (ik : Fin B.count × Fin B.count) : Set (Fin d → ℝ) :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm ⁻¹' Q ik.1

def passiveOriginalParameterTransitionDifferential
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (ik : Fin B.count × Fin B.count) (y : Fin d → ℝ) : Fin (d*d) → ℝ :=
  fun a => fderiv ℝ (passiveOriginalParameterTransition B ik) y
    (Pi.single (finProdFinEquiv.symm a).2 1) (finProdFinEquiv.symm a).1

theorem passiveOriginalParameterTransitionDomain_open
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (ik : Fin B.count × Fin B.count) :
    IsOpen (passiveOriginalParameterTransitionDomain B ik) :=
  (B.chart ik.1).open_target.preimage (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous

theorem passiveOriginalParameterTransition_smooth
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (hB : IsSmoothBufferedAtlas B)
    (hforward : ∀ i, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin d))
      𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ (B.chart i))
    (ik : Fin B.count × Fin B.count) :
    ContDiffOn ℝ ∞ (passiveOriginalParameterTransition B ik)
      (passiveOriginalParameterTransitionDomain B ik) := by
  have hi := contMDiffOn_symm_of_mem_maximalAtlas (hB.chart_mem ik.1)
  have ht := ((EuclideanSpace.equiv (Fin d) ℝ).contDiff.contMDiff.comp
    (hforward ik.2)).comp_contMDiffOn hi
  exact ht.contDiffOn.comp (EuclideanSpace.equiv (Fin d) ℝ).symm.contDiff.contDiffOn
    (fun _ hy => hy)

theorem passiveOriginalParameterTransitionDifferential_smooth
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (hB : IsSmoothBufferedAtlas B)
    (hforward : ∀ i, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin d))
      𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ (B.chart i))
    (ik : Fin B.count × Fin B.count) :
    ContDiffOn ℝ ∞ (passiveOriginalParameterTransitionDifferential B ik)
      (passiveOriginalParameterTransitionDomain B ik) := by
  apply contDiffOn_pi.mpr
  intro a
  exact (ContinuousLinearMap.proj (finProdFinEquiv.symm a).1).contDiff.comp_contDiffOn
    (((passiveOriginalParameterTransition_smooth B hB hforward ik).fderiv_of_isOpen
      (passiveOriginalParameterTransitionDomain_open B ik) (m := ∞) (by simp)).clm_apply
        contDiffOn_const)

def passiveOriginalParameterTransitionProfile
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d))) (j : ℕ) (ell : ℝ) : ℝ≥0∞ :=
  paperAtlasWeighted 0 j ell (passiveOriginalParameterTransitionDifferential B)
    (passiveOriginalParameterTransitionDomain B) (passiveOriginalParameterTransitionSample B Q)

theorem passiveOriginalParameterTransitionProfile_finite
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (hB : IsSmoothBufferedAtlas B)
    (hforward : ∀ i, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin d))
      𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ (B.chart i))
    (Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d)))
    (hQ : ∀ i, IsCompact (Q i)) (hQT : ∀ i, Q i ⊆ (B.chart i).target)
    (j : ℕ) (ell : ℝ) : passiveOriginalParameterTransitionProfile B Q j ell ≠ ⊤ := by
  apply parameterRound2_paperAtlasWeighted_finite_of_compact
    (passiveOriginalParameterTransitionDifferential B)
    (passiveOriginalParameterTransitionDomain B)
    (passiveOriginalParameterTransitionSample B Q)
    (passiveOriginalParameterTransitionSample B Q)
    (passiveOriginalParameterTransitionDomain_open B)
  · intro ik
    exact (EuclideanSpace.equiv (Fin d) ℝ).symm.toHomeomorph.isCompact_preimage.mpr (hQ ik.1)
  · exact fun _ => Subset.rfl
  · exact fun ik _ hy => hQT ik.1 hy
  · exact passiveOriginalParameterTransitionDifferential_smooth B hB hforward

theorem passiveOriginalParameterTransitionProfile_mono_scale
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d))) (j : ℕ)
    (ell : ℝ) (hell : ell ≤ 1) :
    passiveOriginalParameterTransitionProfile B Q j ell ≤
      passiveOriginalParameterTransitionProfile B Q j 1 := by
  unfold passiveOriginalParameterTransitionProfile paperAtlasWeighted
  apply Finset.sum_le_sum
  intro a ha
  exact mul_le_mul_left (pow_le_pow_left' (ENNReal.ofReal_le_ofReal hell) a) _

/-- A single actual finite cost sequence, chosen from the constructed
transition fields before any derivative scale or amplitude is chosen. -/
theorem passiveOriginalParameterTransitionProfile_uniform_cost
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (hB : IsSmoothBufferedAtlas B)
    (hforward : ∀ i, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin d))
      𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ (B.chart i))
    (Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d)))
    (hQ : ∀ i, IsCompact (Q i)) (hQT : ∀ i, Q i ⊆ (B.chart i).target) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∀ j ell, ell ≤ 1 →
      passiveOriginalParameterTransitionProfile B Q j ell ≠ ⊤ ∧
      (passiveOriginalParameterTransitionProfile B Q j ell).toReal ≤ C j := by
  refine ⟨fun j => (passiveOriginalParameterTransitionProfile B Q j 1).toReal,
    fun _ => ENNReal.toReal_nonneg,?_⟩
  intro j ell hell
  have hfinite := passiveOriginalParameterTransitionProfile_finite B hB hforward Q hQ hQT j 1
  have hle := passiveOriginalParameterTransitionProfile_mono_scale B Q j ell hell
  exact ⟨ne_top_of_le_ne_top hfinite hle,ENNReal.toReal_mono hfinite hle⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveOriginalParameterTransitionProfile_finite
#print axioms GlobalEmbedding.Continuation.passiveOriginalParameterTransitionProfile_uniform_cost
