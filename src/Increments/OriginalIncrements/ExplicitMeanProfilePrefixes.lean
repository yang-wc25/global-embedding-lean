import OriginalIncrements.ExplicitPrimaryObserverProfiles
import OriginalCollars.OriginalObserverCutoffFinitePrefix
import FaithfulIncrements.PreparedFiniteBudgetOutput

/-!
# Exact finite prefixes of the profiles used by the actual mean threshold

The actual packet, its selected low geometric margins, and its transverse
reserve are held fixed. At mean order r, Forward reads Given only through
r and transitions through r+1; Meta reads raw and transition slots through
r. These equalities contain no cardinal multiplier and do not assert
uniform low geometry for an arbitrary class of atlases.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation.OriginalIncrements
open CollarCompletion OriginalCollars FaithfulIncrements

/-- The ordinary finite chain-rule majorant only reads the displayed jets. -/
theorem originalCompositionProfile_prefix_congr
    (Outer Outer' Inner Inner' : ℕ → ℝ) (j : ℕ)
    (hOuter : ∀ k, k ≤ j → Outer k = Outer' k)
    (hInner : ∀ k, k ≤ j → Inner k = Inner' k) :
    repairEntranceCompositionProfile Outer Inner j =
      repairEntranceCompositionProfile Outer' Inner' j := by
  have hsum : (∑ k ∈ Finset.range (j+1), Outer k) =
      ∑ k ∈ Finset.range (j+1), Outer' k := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hOuter k (by simpa using hk)
  simp only [repairEntranceCompositionProfile,
    cutoffTransferCost_prefix_congr Inner Inner' j hInner,bufferedTransitionPrefix,hsum]

universe uM uP
variable {m d N : ℕ} {M : Type uM} {P : Type uP}
  [TopologicalSpace M] [TopologicalSpace P] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)

theorem originalBudgetedObserverProfiles_prefix_congr
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (budgeted : OriginalBudgetedPrimarySupply Data theta)
    (Packet Packet' Parameter Parameter' Spatial Spatial' : ℕ → ℝ) (j : ℕ)
    (hPacket : ∀ k, k ≤ j-1 → Packet k = Packet' k)
    (hParameter : ∀ k, 1 ≤ k → k ≤ j → Parameter k = Parameter' k)
    (hSpatial : ∀ k, 1 ≤ k → k ≤ j → Spatial k = Spatial' k) :
    originalBudgetedObserverForward Data theta budgeted Packet Parameter Spatial j =
      originalBudgetedObserverForward Data theta budgeted Packet' Parameter' Spatial' j ∧
    originalBudgetedObserverInverse Data theta budgeted Packet Parameter Spatial j =
      originalBudgetedObserverInverse Data theta budgeted Packet' Parameter' Spatial' j := by
  constructor
  · unfold originalBudgetedObserverForward
    congr 1
    funext a
    exact (original_observer_profiles_prefix_congr m d j
      (budgeted.mu a.1 a.2) (budgeted.Mb a.1 a.2)
      Packet Packet' Parameter Parameter' Spatial Spatial' hPacket hParameter hSpatial).1
  · unfold originalBudgetedObserverInverse
    congr 1
    funext a
    exact (original_observer_profiles_prefix_congr m d j
      (budgeted.mu a.1 a.2) (budgeted.Mb a.1 a.2)
      Packet Packet' Parameter Parameter' Spatial Spatial' hPacket hParameter hSpatial).2

/-- The positive chart profile actually used by the mean preparation. -/
def originalBudgetedMeanForward
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (budgeted : OriginalBudgetedPrimarySupply Data theta)
    (Packet Parameter Spatial : ℕ → ℝ) (r : ℕ) : ℝ :=
  round3PreparedFiniteMaximum (fun k : Fin (r+2) =>
    originalBudgetedObserverForward Data theta budgeted Packet Parameter Spatial k)

/-- The actual adapted cutoff profile, after the finite mean's order prefix. -/
def originalBudgetedMeanMeta
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (budgeted : OriginalBudgetedPrimarySupply Data theta)
    (BS TS BP TP Packet Parameter Spatial : ℕ → ℝ) (Ds Dp : ℕ) (r : ℕ) : ℝ :=
  round3PreparedFiniteMaximum (fun k : Fin (r+1) =>
    repairEntranceCompositionProfile
      (originalObserverCutoffProfile Data theta budgeted BS TS BP TP Parameter Spatial Ds Dp)
      (originalBudgetedObserverInverse Data theta budgeted Packet Parameter Spatial) k)

theorem originalBudgetedMeanForward_nonneg
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (budgeted : OriginalBudgetedPrimarySupply Data theta)
    (Packet Parameter Spatial : ℕ → ℝ) (r : ℕ) :
    0 ≤ originalBudgetedMeanForward Data theta budgeted Packet Parameter Spatial r :=
  round3PreparedFiniteMaximum_nonneg _

theorem originalBudgetedMeanMeta_nonneg
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (budgeted : OriginalBudgetedPrimarySupply Data theta)
    (BS TS BP TP Packet Parameter Spatial : ℕ → ℝ) (Ds Dp r : ℕ) :
    0 ≤ originalBudgetedMeanMeta Data theta budgeted BS TS BP TP Packet Parameter Spatial Ds Dp r :=
  round3PreparedFiniteMaximum_nonneg _

theorem originalBudgetedMeanProfiles_prefix_congr
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (budgeted : OriginalBudgetedPrimarySupply Data theta)
    (BS BS' TS TS' BP BP' TP TP' Packet Packet' Parameter Parameter' Spatial Spatial' : ℕ → ℝ)
    (Ds Dp r : ℕ)
    (hBS : ∀ k, k ≤ r → BS k = BS' k) (hTS : ∀ k, k ≤ r → TS k = TS' k)
    (hBP : ∀ k, k ≤ r → BP k = BP' k) (hTP : ∀ k, k ≤ r → TP k = TP' k)
    (hPacket : ∀ k, k ≤ r → Packet k = Packet' k)
    (hParameter : ∀ k, k ≤ r+1 → Parameter k = Parameter' k)
    (hSpatial : ∀ k, k ≤ r+1 → Spatial k = Spatial' k) :
    originalBudgetedMeanForward Data theta budgeted Packet Parameter Spatial r =
      originalBudgetedMeanForward Data theta budgeted Packet' Parameter' Spatial' r ∧
    originalBudgetedMeanMeta Data theta budgeted BS TS BP TP Packet Parameter Spatial Ds Dp r =
      originalBudgetedMeanMeta Data theta budgeted BS' TS' BP' TP' Packet' Parameter' Spatial' Ds Dp r ∧
    originalBudgetedObserverInverse Data theta budgeted Packet Parameter Spatial r =
      originalBudgetedObserverInverse Data theta budgeted Packet' Parameter' Spatial' r := by
  refine ⟨?_,?_,?_⟩
  · unfold originalBudgetedMeanForward
    apply congrArg (round3PreparedFiniteMaximum (I := Fin (r+2)))
    funext k
    exact (originalBudgetedObserverProfiles_prefix_congr Data theta budgeted
      Packet Packet' Parameter Parameter' Spatial Spatial' k
      (fun l hl => hPacket l (by omega))
      (fun l _ hl => hParameter l (by omega)) (fun l _ hl => hSpatial l (by omega))).1
  · unfold originalBudgetedMeanMeta
    apply congrArg (round3PreparedFiniteMaximum (I := Fin (r+1)))
    funext k
    apply originalCompositionProfile_prefix_congr
    · intro l hl
      apply originalObserverCutoffProfile_prefix_congr
      · exact fun t ht => hBS t (by omega)
      · exact fun t ht => hTS t (by omega)
      · exact fun t ht => hBP t (by omega)
      · exact fun t ht => hTP t (by omega)
      · exact fun t ht => hParameter t (by omega)
      · exact fun t ht => hSpatial t (by omega)
    · intro l hl
      exact (originalBudgetedObserverProfiles_prefix_congr Data theta budgeted
        Packet Packet' Parameter Parameter' Spatial Spatial' l
        (fun t ht => hPacket t (by omega))
        (fun t _ ht => hParameter t (by omega)) (fun t _ ht => hSpatial t (by omega))).2
  · exact (originalBudgetedObserverProfiles_prefix_congr Data theta budgeted
      Packet Packet' Parameter Parameter' Spatial Spatial' r
      (fun k hk => hPacket k (by omega))
      (fun k _ hk => hParameter k (by omega)) (fun k _ hk => hSpatial k (by omega))).2

/-- The exact entrance number for the actual budgeted packet. Only the
admitted current Given prefix is used; its all-order envelope supplies C. -/
def originalBudgetedCurrentThreshold
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (budgeted : OriginalBudgetedPrimarySupply Data theta)
    (q Rsub Lactive : ℕ) (rho c cT : ℝ) (hrho : 0 < rho)
    (BS TS BP TP Parameter Spatial allowed : ℕ → ℝ) (Ds Dp : ℕ)
    (hAllowed : ∀ k, k ≤ (q+1)*(q+4)+2 → 0 ≤ allowed k) : ℝ :=
  let J := (q+1)*(q+4)+2
  let Packet := actualGivenEnvelope Data J allowed
  let F := originalBudgetedMeanForward Data theta budgeted Packet Parameter Spatial
  let Meta := originalBudgetedMeanMeta Data theta budgeted BS TS BP TP Packet Parameter Spatial Ds Dp
  let Inverse := originalBudgetedObserverInverse Data theta budgeted Packet Parameter Spatial
  finiteOriginalMeanThreshold.{uM,0} (m := m) (d := d) (N := N) (M := M)
    q Rsub Lactive rho c cT hrho
    (finitePrefixProfile J allowed) (finitePrefixProfile J F)
    (finitePrefixProfile J Meta) (finitePrefixProfile J Inverse)
    (finitePrefixProfile_nonneg J allowed hAllowed)
    (finitePrefixProfile_nonneg J F (fun k _ => originalBudgetedMeanForward_nonneg
      Data theta budgeted Packet Parameter Spatial k))

/-- Arbitrary tails of every input may be changed without changing the
actual threshold. The selected packet and its low margins stay identical. -/
theorem originalBudgetedCurrentThreshold_prefix_congr
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (budgeted : OriginalBudgetedPrimarySupply Data theta)
    (q Rsub Lactive : ℕ) (rho c cT : ℝ) (hrho : 0 < rho)
    (BS BS' TS TS' BP BP' TP TP' Parameter Parameter' Spatial Spatial' allowed allowed' : ℕ → ℝ)
    (Ds Dp : ℕ)
    (hAllowed : ∀ k, k ≤ (q+1)*(q+4)+2 → 0 ≤ allowed k)
    (hAllowed' : ∀ k, k ≤ (q+1)*(q+4)+2 → 0 ≤ allowed' k)
    (hBS : ∀ k, k ≤ (q+1)*(q+4)+2 → BS k = BS' k)
    (hTS : ∀ k, k ≤ (q+1)*(q+4)+2 → TS k = TS' k)
    (hBP : ∀ k, k ≤ (q+1)*(q+4)+2 → BP k = BP' k)
    (hTP : ∀ k, k ≤ (q+1)*(q+4)+2 → TP k = TP' k)
    (hParameter : ∀ k, k ≤ (q+1)*(q+4)+3 → Parameter k = Parameter' k)
    (hSpatial : ∀ k, k ≤ (q+1)*(q+4)+3 → Spatial k = Spatial' k)
    (hGiven : ∀ k, k ≤ (q+1)*(q+4)+2 → allowed k = allowed' k) :
    originalBudgetedCurrentThreshold Data theta budgeted q Rsub Lactive rho c cT hrho
      BS TS BP TP Parameter Spatial allowed Ds Dp hAllowed =
    originalBudgetedCurrentThreshold Data theta budgeted q Rsub Lactive rho c cT hrho
      BS' TS' BP' TP' Parameter' Spatial' allowed' Ds Dp hAllowed' := by
  let J := (q+1)*(q+4)+2
  have hEnvelope (k : ℕ) (hk : k ≤ J) :
      actualGivenEnvelope Data J allowed k = actualGivenEnvelope Data J allowed' k := by
    rw [actualGivenEnvelope_prefix Data J allowed k hk,
      actualGivenEnvelope_prefix Data J allowed' k hk]
    exact hGiven k hk
  have hProfiles (r : ℕ) (hr : r ≤ J) :=
    originalBudgetedMeanProfiles_prefix_congr Data theta budgeted
      BS BS' TS TS' BP BP' TP TP'
      (actualGivenEnvelope Data J allowed) (actualGivenEnvelope Data J allowed')
      Parameter Parameter' Spatial Spatial' Ds Dp r
      (fun k hk => hBS k (hk.trans hr)) (fun k hk => hTS k (hk.trans hr))
      (fun k hk => hBP k (hk.trans hr)) (fun k hk => hTP k (hk.trans hr))
      (fun k hk => hEnvelope k (hk.trans hr))
      (fun k hk => hParameter k (by dsimp only [J] at hr; omega))
      (fun k hk => hSpatial k (by dsimp only [J] at hr; omega))
  unfold originalBudgetedCurrentThreshold
  apply finiteOriginalMeanThreshold_prefix_congr
  · intro k hk
    rw [finitePrefixProfile_eq _ _ k hk,finitePrefixProfile_eq _ _ k hk]
    exact hGiven k hk
  · intro k hk
    rw [finitePrefixProfile_eq _ _ k hk,finitePrefixProfile_eq _ _ k hk]
    exact (hProfiles k hk).1
  · intro k hk
    rw [finitePrefixProfile_eq _ _ k hk,finitePrefixProfile_eq _ _ k hk]
    exact (hProfiles k hk).2.1
  · intro k hk
    rw [finitePrefixProfile_eq _ _ k hk,finitePrefixProfile_eq _ _ k hk]
    exact (hProfiles k hk).2.2

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.originalBudgetedCurrentThreshold_prefix_congr
