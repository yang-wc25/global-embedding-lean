import Probes.ActualProbeNormalSource
import Probes.ActualRealHomogeneousProbe
import GlobalEmbedding.Paper.IncrementsModeComplexLinearity

/-!
# The prescribed u₁-i u₂ normal amplitude gives the actual finite source

The source is literally the original h=0 `incrementsModeSource` in the real
and imaginary normal channels. Its finite dictionary is proved, including the
minus-i sine column. Thus the previously established full first-block jet
theorems apply to this prescribed source, rather than to arbitrary placeholders.
-/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Continuation Manifold Set Filter
open scoped ContDiff BigOperators Topology
namespace GlobalEmbedding.Offline

section Dictionary
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedSpace ℂ Y]
  [IsScalarTower ℝ ℂ Y] {p r : ℕ}

/-- Sparse actual source dictionary for one original paired label. -/
def pairedProbeSourceDictionary (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (s : X → Y) (q : Fin p) (x : X) : Y :=
  (if q = label (l, false) then s x else 0) +
    (if q = label (l, true) then (-Complex.I) • s x else 0)

theorem finiteProbeSource_paired_dictionary
    (label : (Fin r × Bool) ↪ Fin p) (l : Fin r) (s : X → Y)
    (u : Fin p → ℝ) (x : X) :
    finiteProbeSource (pairedProbeSourceDictionary label l s) u x =
      u (label (l, false)) • s x + u (label (l, true)) • ((-Complex.I) • s x) := by
  classical
  simp [finiteProbeSource, pairedProbeSourceDictionary, smul_add, Finset.sum_add_distrib]

theorem pairedProbeSourceDictionary_cos_column
    (label : (Fin r × Bool) ↪ Fin p) (l : Fin r) (s : X → Y) :
    pairedProbeSourceDictionary label l s (label (l, false)) = s := by
  funext x
  simp [pairedProbeSourceDictionary, label.injective.eq_iff]

theorem pairedProbeSourceDictionary_sin_column
    (label : (Fin r × Bool) ↪ Fin p) (l : Fin r) (s : X → Y) :
    pairedProbeSourceDictionary label l s (label (l, true)) = fun x ↦ (-Complex.I) • s x := by
  funext x
  simp [pairedProbeSourceDictionary, label.injective.eq_iff]

theorem pairedProbeSourceDictionary_contDiffOn
    (label : (Fin r × Bool) ↪ Fin p) (l : Fin r) (s : X → Y) (O : Set X)
    (hs : ContDiffOn ℝ ∞ s O) (q : Fin p) :
    ContDiffOn ℝ ∞ (pairedProbeSourceDictionary label l s q) O := by
  classical
  unfold pairedProbeSourceDictionary
  split_ifs <;> fun_prop

/-- The sparse actual columns retain the source's original slow budget,
because multiplication by -i is an isometry in the native complex norm. -/
theorem pairedProbeSourceDictionary_weighted_jet_bound
    (label : (Fin r × Bool) ↪ Fin p) (l : Fin r) (s : X → Y)
    (n : ℕ) (x : X) (hs : ContDiffAt ℝ n s x)
    (ell K : ℝ) (hK : 0 ≤ K) (hb : ell ^ n * ‖iteratedFDeriv ℝ n s x‖ ≤ K)
    (q : Fin p) :
    ell ^ n * ‖iteratedFDeriv ℝ n (pairedProbeSourceDictionary label l s q) x‖ ≤ K := by
  classical
  by_cases hc : q = label (l, false)
  · subst q
    rw [pairedProbeSourceDictionary_cos_column]
    exact hb
  · by_cases hi : q = label (l, true)
    · subst q
      rw [pairedProbeSourceDictionary_sin_column, iteratedFDeriv_const_smul_apply' hs,
        norm_smul, norm_neg, Complex.norm_I, one_mul]
      exact hb
    · have he : pairedProbeSourceDictionary label l s q = fun _ ↦ 0 := by
        funext y
        simp [pairedProbeSourceDictionary, hc, hi]
      rw [he]
      simpa using hK
end Dictionary

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Cdata" => Fin (m + 1) → ℂ

/-- Original real/imaginary source of the prescribed complex amplitude
v_f (u₁-i u₂), with v_f a genuine original normal-bundle section. -/
def actualPairedNormalSource (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (vf : (x : D) → normalSpace (I := I) F (c x)) (u : Fin p → ℝ) (x : D) : Cdata :=
  incrementsModeComplexInclude (incrementsModeSource F hF c (fun _ _ _ ↦ 0)
    (fun y ↦ u (label (l, false)) • vf y) x) +
  Complex.I • incrementsModeComplexInclude (incrementsModeSource F hF c (fun _ _ _ ↦ 0)
    (fun y ↦ (-u (label (l, true))) • vf y) x)

/-- Exact binding of the actual original homogeneous source to the finite
source family used in all native reconstruction and mixed-jet theorems. -/
theorem actualPairedNormalSource_eq_finite_source
    (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (vf : (x : D) → normalSpace (I := I) F (c x)) (u : Fin p → ℝ) :
    actualPairedNormalSource label l F hF c vf u =
      finiteProbeSource (pairedProbeSourceDictionary label l
        (fun x ↦ incrementsModeComplexInclude (incrementsModeSource F hF c (fun _ _ _ ↦ 0) vf x))) u := by
  funext x
  rw [finiteProbeSource_paired_dictionary]
  simp only [actualPairedNormalSource, incrementsModeSource_zero_smul, map_smul]
  congr 1
  rw [smul_comm Complex.I (-u (label (l, true)))]
  simp only [neg_smul, smul_neg]

/-- Native parameter differentiation of the literal original source.
The cosine and sine source columns are precisely s and -i*s. -/
theorem hasFDerivAt_actualPairedNormalSource
    (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M)
    (vf : (x : D) → normalSpace (I := I) F (c x)) (u : Fin p → ℝ) (x : D) :
    HasFDerivAt (fun z ↦ actualPairedNormalSource label l F hF c vf z x)
      (probeColumnMap (fun q ↦ pairedProbeSourceDictionary label l
        (fun y ↦ incrementsModeComplexInclude (incrementsModeSource F hF c (fun _ _ _ ↦ 0) vf y)) q x)) u := by
  have he : (fun z ↦ actualPairedNormalSource label l F hF c vf z x) =
      probeColumnMap (fun q ↦ pairedProbeSourceDictionary label l
        (fun y ↦ incrementsModeComplexInclude (incrementsModeSource F hF c (fun _ _ _ ↦ 0) vf y)) q x) := by
    funext z
    rw [actualPairedNormalSource_eq_finite_source, probeColumnMap_apply]
    rfl
  rw [he]
  exact ContinuousLinearMap.hasFDerivAt _

#print axioms actualPairedNormalSource_eq_finite_source
#print axioms hasFDerivAt_actualPairedNormalSource
#print axioms pairedProbeSourceDictionary_weighted_jet_bound
end GlobalEmbedding.Offline
