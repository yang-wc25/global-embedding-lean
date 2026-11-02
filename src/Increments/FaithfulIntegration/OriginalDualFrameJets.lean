import FaithfulIntegration.OriginalLinearTransport

/-!
# Reverse coframe jets from the original forward and reverse overlaps

The host is selected inside its given source inner.  Thus the reverse
transition is evaluated at a point of the host's original Omega; the old
source-transition budget applies directly.  No extra inverse-frame
hypothesis and no compact norm-domain hypothesis are introduced.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Module Filter
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation.FaithfulIntegration
open FaithfulRepair

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

theorem originalTransition_maps_reverse
    (D : IncrementsOriginalNativeData n d N M P)
    (p i : Fin D.atlas.count × Fin D.parameterCount) :
    MapsTo (actualOriginalGivenTransition D p i)
      (actualOriginalGivenTransitionDomain D (p,i))
      (actualOriginalGivenTransitionDomain D (i,p)) := by
  intro y hy
  let chart := originalJointCoordinateChart D
  have hy' : y ∈ ((chart p).symm.trans (chart i)).source := by
    rwa [originalJointCoordinateChart_transition_source]
  have ht : actualOriginalGivenTransition D p i y ∈ (chart i).target :=
    (chart i).map_source hy'.2
  have hi : (chart i).symm (actualOriginalGivenTransition D p i y) =
      (chart p).symm y := (chart i).left_inv hy'.2
  rw [← originalJointCoordinateChart_transition_source]
  refine ⟨ht,?_⟩
  change (chart i).symm (actualOriginalGivenTransition D p i y) ∈ (chart p).source
  rw [hi]
  exact (chart p).map_target hy'.1

def originalDualFrameEntry
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D)
    (p i : Fin D.atlas.count × Fin D.parameterCount) (a r : Fin n) :
    (Fin (n+d) → ℝ) → ℝ :=
  originalTensorFrameEntry D hd i p a r ∘ actualOriginalGivenTransition D p i

def originalSourceFrameJetProfile (n d : ℕ) (TS : ℕ → ℝ) (k : ℕ) : ℝ :=
  TS (k+1) * ‖originalSourceProjection n d‖^k

def originalDualFrameJetProfile (n d : ℕ) (T TS : ℕ → ℝ) (k : ℕ) : ℝ :=
  (k.factorial : ℝ) * bufferedTransitionPrefix (originalSourceFrameJetProfile n d TS) k *
    bufferedTransitionPrefix T k ^ k

theorem originalSourceFrameJetProfile_nonneg
    (TS : ℕ → ℝ) (hTS : ∀ k, 0 ≤ TS k) (k : ℕ) :
    0 ≤ originalSourceFrameJetProfile n d TS k :=
  mul_nonneg (hTS _) (pow_nonneg (norm_nonneg _) _)

theorem originalDualFrameJetProfile_nonneg
    (T TS : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hTS : ∀ k, 0 ≤ TS k) (k : ℕ) :
    0 ≤ originalDualFrameJetProfile n d T TS k :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (zero_le_one.trans (one_le_bufferedTransitionPrefix (originalSourceFrameJetProfile_nonneg TS hTS) k)))
    (pow_nonneg (zero_le_one.trans (one_le_bufferedTransitionPrefix hT k)) k)

theorem originalDualFrameEntry_contDiffOn
    (D : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions D)
    (p i : Fin D.atlas.count × Fin D.parameterCount) (a r : Fin n) :
    ContDiffOn ℝ ∞ (originalDualFrameEntry D hd p i a r)
      (actualOriginalGivenTransitionDomain D (p,i)) :=
  (originalTensorFrameEntry_contDiffOn D hd i p a r).comp
    (actualOriginalGivenTransition_contDiffOn D hd (p,i))
    (originalTransition_maps_reverse D p i)

/-- Both transition directions are paid by original budgets on their own
original norm domains.  The host-inner fact is manufactured by the compact
core producer, not a new field of the original datum. -/
theorem originalDualFrameEntry_jet_le
    (D : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions D)
    (T TS : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hTS : ∀ k, 0 ≤ TS k)
    (hTransition : ∀ p i k, 1 ≤ k → ∀ y ∈ actualOriginalGivenTransitionSample D (p,i),
      ‖iteratedFDeriv ℝ k (actualOriginalGivenTransition D p i) y‖ ≤ T k)
    (hSource : ∀ p i k, 1 ≤ k → ∀ y ∈ D.sourceNormDomain p,
      y ∈ ((D.atlas.chart p).symm.trans (D.atlas.chart i)).source →
      ‖iteratedFDeriv ℝ k ((D.atlas.chart p).symm.trans (D.atlas.chart i)) y‖ ≤ TS k)
    (p i : Fin D.atlas.count × Fin D.parameterCount) (a r : Fin n)
    (y : Fin (n+d) → ℝ) (hy : y ∈ actualOriginalGivenTransitionSample D (p,i))
    (hInner : (incrementsOriginalJointPoint D.atlas D.parameterChart p y).2 ∈ D.atlas.inner i.1)
    (k : ℕ) :
    ‖iteratedFDeriv ℝ k (originalDualFrameEntry D hd p i a r) y‖ ≤
      originalDualFrameJetProfile n d T TS k := by
  let e := actualOriginalGivenTransition D p i
  have hrev := originalTransition_maps_reverse D p i hy.2
  have hHostOmega : incrementsOriginalSourcePoint (e y) ∈ D.sourceNormDomain i.1 := by
    have h := hd.source_inner_norm i.1 _ hInner
    have he := congrArg Prod.snd ((parameterTensorModelEquiv n d).symm_apply_apply
      (D.parameterChart i.2 (incrementsOriginalJointPoint D.atlas D.parameterChart p y).1,
       D.atlas.chart i.1 (incrementsOriginalJointPoint D.atlas D.parameterChart p y).2))
    rw [parameterTensorModelEquiv_symm_apply] at he
    change incrementsOriginalSourcePoint (e y) = _ at he
    rw [he]
    exact h
  have hFrame : ∀ l, ‖iteratedFDeriv ℝ l (originalTensorFrameEntry D hd i p a r) (e y)‖ ≤
      originalSourceFrameJetProfile n d TS l := by
    intro l
    exact (originalTensorFrameEntry_jet_le D hd i p a r (e y) hrev l).trans
      (mul_le_mul_of_nonneg_right
        (hSource i.1 p.1 (l+1) (by omega) _ hHostOmega ⟨hrev.1.1,hrev.2.2⟩)
        (pow_nonneg (norm_nonneg _) _))
  apply buffered_composition_jet_le T hT
    (actualOriginalGivenTransitionDomain_open D (p,i))
    (actualOriginalGivenTransitionDomain_open D (i,p))
    (actualOriginalGivenTransition_contDiffOn D hd (p,i))
    (originalTensorFrameEntry_contDiffOn D hd i p a r)
    (originalTransition_maps_reverse D p i) hy.2 k
    (bufferedTransitionPrefix (originalSourceFrameJetProfile n d TS) k)
  · intro l hl
    apply (hFrame l).trans
    have hb : originalSourceFrameJetProfile n d TS l ≤
        ∑ j ∈ Finset.range (k+1), originalSourceFrameJetProfile n d TS j :=
      Finset.single_le_sum
        (fun j _ => originalSourceFrameJetProfile_nonneg TS hTS j) (by simpa using hl)
    exact hb.trans (le_add_of_nonneg_left zero_le_one)
  · intro l hl _
    exact hTransition p i l hl y hy

end GlobalEmbedding.Continuation.FaithfulIntegration

#print axioms GlobalEmbedding.Continuation.FaithfulIntegration.originalDualFrameEntry_jet_le

