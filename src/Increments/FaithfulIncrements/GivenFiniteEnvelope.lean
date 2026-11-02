import Smoothing.ParameterRound2OriginalFixedPacket
import Repair.EntranceFiniteReferenceEnvelope
import CollarCompletion.FiniteMeanNumerics

/-!
# Manufacture the original Given budget beyond its prescribed finite prefix

The given datum, every coordinate field, differentiation domain, observation
set, and scale are unchanged.  The allowed finite prefix is completed by the
actual higher norms of that same datum.  The exact mean threshold is proved
independent of every completed tail value.

This is the numerical part of the original entrance, not a replacement
original theorem: the original finite-norm producer must supply the displayed
finiteness proof.  In particular `toReal` is never used to hide an infinite
norm and no all-order numerical upper budget is an entrance hypothesis.

Source: main.tex, notation:averages, setup:uniform, lem:increments (the finite
backward list of derivative orders preceding (6.3)).
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation.FaithfulIncrements

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- Scale monotonicity for the actual complete given-input profile, including
the original total parameter-phase differential and original transitions. -/
theorem given_profile_mono_scale
    (Data : IncrementsOriginalNativeData n d N M P) (j : ℕ)
    (ell t : ℝ) (hle : ell ≤ t) :
    actualOriginalGivenInputProfile Data j ell ≤ actualOriginalGivenInputProfile Data j t := by
  rw [parameterRound2_originalGivenProfile_eq_map_tensor_packet,
    parameterRound2_originalGivenProfile_eq_map_tensor_packet]
  exact max_le_max
    (parameterRound2_paperAtlasWeighted_mono_scale 2 j ell t hle _ _ _)
    (max_le_max (parameterRound2_paperAtlasWeighted_mono_scale 0 j ell t hle _ _ _)
      (parameterRound2_originalFixedPacketProfile_mono_scale Data j ell t hle))

/-- The literal prescribed prefix and the actual high-order tail. -/
def actualGivenEnvelope
    (Data : IncrementsOriginalNativeData n d N M P) (J : ℕ)
    (allowed : ℕ → ℝ) : ℕ → ℝ :=
  repairEntranceFiniteProfile J allowed
    (fun j => (actualOriginalGivenInputProfile Data j 1).toReal)

theorem actualGivenEnvelope_prefix
    (Data : IncrementsOriginalNativeData n d N M P) (J : ℕ)
    (allowed : ℕ → ℝ) (j : ℕ) (hj : j ≤ J) :
    actualGivenEnvelope Data J allowed j = allowed j :=
  repairEntranceFiniteProfile_prefix J allowed _ j hj

theorem actualGivenEnvelope_nonneg
    (Data : IncrementsOriginalNativeData n d N M P) (J : ℕ)
    (allowed : ℕ → ℝ) (hAllowed : ∀ j, j ≤ J → 0 ≤ allowed j) (j : ℕ) :
    0 ≤ actualGivenEnvelope Data J allowed j :=
  repairEntranceFiniteProfile_nonneg J allowed _ hAllowed
    (fun _ => ENNReal.toReal_nonneg) j

/-- The same actual completed profile supplies every allowed scale. Only
the original finite prefix has a prescribed numerical upper bound. -/
theorem actualGivenEnvelope_all_scales
    (Data : IncrementsOriginalNativeData n d N M P) (J : ℕ)
    (allowed : ℕ → ℝ)
    (hFinite : ∀ j, actualOriginalGivenInputProfile Data j 1 ≠ ⊤)
    (hPrefix : ∀ j, j ≤ J →
      (actualOriginalGivenInputProfile Data j 1).toReal ≤ allowed j)
    (ell : ℝ) (hell : ell ≤ 1) (j : ℕ) :
    actualOriginalGivenInputProfile Data j ell ≠ ⊤ ∧
      (actualOriginalGivenInputProfile Data j ell).toReal ≤
        actualGivenEnvelope Data J allowed j := by
  have hle := given_profile_mono_scale Data j ell 1 hell
  refine ⟨ne_top_of_le_ne_top (hFinite j) hle, ?_⟩
  exact (ENNReal.toReal_mono (hFinite j) hle).trans
    (repairEntranceFiniteProfile_dominates J allowed _ hPrefix j)

/-- Finiteness is retained as a separate proved fact; the entire envelope
is constructed from the given datum and the permitted finite upper bounds. -/
theorem actualGivenEnvelope_nonneg_and_all_scales
    (Data : IncrementsOriginalNativeData n d N M P) (J : ℕ)
    (allowed : ℕ → ℝ)
    (hFinite : ∀ j, actualOriginalGivenInputProfile Data j 1 ≠ ⊤)
    (hPrefix : ∀ j, j ≤ J →
      (actualOriginalGivenInputProfile Data j 1).toReal ≤ allowed j) :
    (∀ j, 0 ≤ actualGivenEnvelope Data J allowed j) ∧
    ∀ ell : ℝ, ell ≤ 1 → ∀ j,
      actualOriginalGivenInputProfile Data j ell ≠ ⊤ ∧
      (actualOriginalGivenInputProfile Data j ell).toReal ≤
        actualGivenEnvelope Data J allowed j := by
  exact ⟨actualGivenEnvelope_nonneg Data J allowed
    (fun j hj => ENNReal.toReal_nonneg.trans (hPrefix j hj)),
    fun ell hell j => actualGivenEnvelope_all_scales Data J allowed hFinite hPrefix ell hell j⟩

/-- The original entrance only bounds the finite prefix at the CURRENT
weighted scale. It does not need a bound for that prefix at scale one.
Scale one is used solely to manufacture the actual high-order tail of the
same smooth datum, with no prescribed numerical upper bound on that tail. -/
theorem actualGivenEnvelope_current_scale
    (Data : IncrementsOriginalNativeData n d N M P) (J : ℕ)
    (allowed : ℕ → ℝ)
    (hFinite : ∀ j, actualOriginalGivenInputProfile Data j 1 ≠ ⊤)
    (ell : ℝ) (hell : ell ≤ 1)
    (hPrefix : ∀ j, j ≤ J →
      (actualOriginalGivenInputProfile Data j ell).toReal ≤ allowed j)
    (j : ℕ) :
    actualOriginalGivenInputProfile Data j ell ≠ ⊤ ∧
      (actualOriginalGivenInputProfile Data j ell).toReal ≤
        actualGivenEnvelope Data J allowed j := by
  have hle := given_profile_mono_scale Data j ell 1 hell
  refine ⟨ne_top_of_le_ne_top (hFinite j) hle, ?_⟩
  by_cases hj : j ≤ J
  · rw [actualGivenEnvelope_prefix Data J allowed j hj]
    exact hPrefix j hj
  · change _ ≤ repairEntranceFiniteProfile J allowed
      (fun k => (actualOriginalGivenInputProfile Data k 1).toReal) j
    rw [repairEntranceFiniteProfile, if_neg hj]
    exact ENNReal.toReal_mono (hFinite j) hle

/-- One completed profile, fixed before all scales, consumes just the
current-scale finite input budget at each scale. This is the scale order
required by the original increment entrance. -/
theorem actualGivenEnvelope_current_scale_family
    (Data : IncrementsOriginalNativeData n d N M P) (J : ℕ)
    (allowed : ℕ → ℝ) (hAllowed : ∀ j, j ≤ J → 0 ≤ allowed j)
    (hFinite : ∀ j, actualOriginalGivenInputProfile Data j 1 ≠ ⊤) :
    (∀ j, 0 ≤ actualGivenEnvelope Data J allowed j) ∧
    ∀ ell : ℝ, ell ≤ 1 →
      (∀ j, j ≤ J → (actualOriginalGivenInputProfile Data j ell).toReal ≤ allowed j) →
      ∀ j, actualOriginalGivenInputProfile Data j ell ≠ ⊤ ∧
        (actualOriginalGivenInputProfile Data j ell).toReal ≤
          actualGivenEnvelope Data J allowed j := by
  exact ⟨actualGivenEnvelope_nonneg Data J allowed hAllowed,
    fun ell hell hPrefix j => actualGivenEnvelope_current_scale Data J allowed hFinite ell hell hPrefix j⟩

section ExactThreshold
universe uM uB
variable {m : ℕ} {X : Type uM} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) X]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ X]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) X]

/-- Reusing the literal finite-prefix completion for all four primitive
profiles leaves the existing exact threshold unchanged. The tails are actual
data, never numerical entrance assumptions. -/
theorem completed_threshold_eq
    (q Rsub Lprimary : ℕ) (rho c cT : ℝ) (hrho : 0 < rho)
    (Packet Forward Meta Tinv actualPacket actualForward actualMeta actualTinv : ℕ → ℝ)
    (hPacket : ∀ j, 0 ≤ Packet j) (hForward : ∀ j, 0 ≤ Forward j)
    (hActualPacket : ∀ j, 0 ≤ actualPacket j)
    (hActualForward : ∀ j, 0 ≤ actualForward j) :
    let J := (q+1)*(q+4)+2
    let CP := repairEntranceFiniteProfile J Packet actualPacket
    let CF := repairEntranceFiniteProfile J Forward actualForward
    let CM := repairEntranceFiniteProfile J Meta actualMeta
    let CI := repairEntranceFiniteProfile J Tinv actualTinv
    let hCP := repairEntranceFiniteProfile_nonneg J Packet actualPacket
      (fun j _ => hPacket j) hActualPacket
    let hCF := repairEntranceFiniteProfile_nonneg J Forward actualForward
      (fun j _ => hForward j) hActualForward
    CollarCompletion.finiteOriginalMeanThreshold.{uM,uB}
      (m := m) (d := d) (N := N) (M := X)
      q Rsub Lprimary rho c cT hrho CP CF CM CI hCP hCF =
    CollarCompletion.finiteOriginalMeanThreshold.{uM,uB}
      (m := m) (d := d) (N := N) (M := X)
      q Rsub Lprimary rho c cT hrho Packet Forward Meta Tinv hPacket hForward := by
  intro J CP CF CM CI hCP hCF
  apply CollarCompletion.finiteOriginalMeanThreshold_prefix_congr
  · exact repairEntranceFiniteProfile_prefix J Packet actualPacket
  · exact repairEntranceFiniteProfile_prefix J Forward actualForward
  · exact repairEntranceFiniteProfile_prefix J Meta actualMeta
  · exact repairEntranceFiniteProfile_prefix J Tinv actualTinv

end ExactThreshold
end GlobalEmbedding.Continuation.FaithfulIncrements

#print axioms GlobalEmbedding.Continuation.FaithfulIncrements.actualGivenEnvelope_all_scales
#print axioms GlobalEmbedding.Continuation.FaithfulIncrements.completed_threshold_eq
