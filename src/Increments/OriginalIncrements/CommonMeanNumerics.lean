import OriginalIncrements.CommonObserverNumerics
import OriginalCollars.UniformGridNumericBudget

/-!
# Common mean costs with no atlas or original datum in their formulas

The actual packet supplies three low numbers: a two-jet upper bound, a
first inverse upper bound, and a grid reciprocal-radius upper bound. All
later numerical profiles depend only on these numbers, dimensions, and
original finite input profiles. The full threshold retains the existing
fixed source-manifold parameter of finiteOriginalMeanThreshold; no stronger
cross-manifold uniformity is claimed by these cost identities.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation.OriginalIncrements
open CollarCompletion OriginalCollars FaithfulIncrements

theorem originalCompositionProfile_mono_prefix
    (Outer Inner Outer' Inner' : ℕ → ℝ) (j : ℕ)
    (hOuter : ∀ k, 0 ≤ Outer k) (hInner : ∀ k, 0 ≤ Inner k)
    (hO : ∀ k, k ≤ j → Outer k ≤ Outer' k)
    (hI : ∀ k, k ≤ j → Inner k ≤ Inner' k) :
    repairEntranceCompositionProfile Outer Inner j ≤
      repairEntranceCompositionProfile Outer' Inner' j := by
  have hOp : bufferedTransitionPrefix Outer j ≤ bufferedTransitionPrefix Outer' j := by
    unfold bufferedTransitionPrefix
    exact add_le_add le_rfl (Finset.sum_le_sum (fun k hk => hO k (by simpa using hk)))
  have hIp : bufferedTransitionPrefix Inner j ≤ bufferedTransitionPrefix Inner' j := by
    unfold bufferedTransitionPrefix
    exact add_le_add le_rfl (Finset.sum_le_sum (fun k hk => hI k (by simpa using hk)))
  have hO0 := zero_le_one.trans (one_le_bufferedTransitionPrefix hOuter j)
  have hI0 := zero_le_one.trans (one_le_bufferedTransitionPrefix hInner j)
  unfold repairEntranceCompositionProfile actualFastChartTransferCost
  apply mul_le_mul _ hOp hO0
  · exact mul_nonneg (by positivity) (pow_nonneg (hI0.trans hIp) j)
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hI0 hIp j) (by positivity)

def commonMeanForward (m d : ℕ) (Mb : ℝ)
    (Packet Parameter Spatial : ℕ → ℝ) (r : ℕ) : ℝ :=
  round3PreparedFiniteMaximum (fun k : Fin (r+2) =>
    commonObserverForward m d Mb Packet Parameter Spatial k)

def commonAdaptedMeta (m d : ℕ) (B H : ℝ)
    (BS TS BP TP Packet Parameter Spatial : ℕ → ℝ) (Ds Dp j : ℕ) : ℝ :=
  repairEntranceCompositionProfile
    (uniformOriginalObserverCutoffProfile m d H BS TS BP TP Parameter Spatial Ds Dp)
    (commonObserverInverse m d B Packet Parameter Spatial) j

def commonMeanMeta (m d : ℕ) (B H : ℝ)
    (BS TS BP TP Packet Parameter Spatial : ℕ → ℝ) (Ds Dp r : ℕ) : ℝ :=
  round3PreparedFiniteMaximum (fun k : Fin (r+1) =>
    commonAdaptedMeta m d B H BS TS BP TP Packet Parameter Spatial Ds Dp k)

theorem commonMeanForward_nonneg (m d : ℕ) (Mb : ℝ)
    (Packet Parameter Spatial : ℕ → ℝ) (r : ℕ) :
    0 ≤ commonMeanForward m d Mb Packet Parameter Spatial r :=
  round3PreparedFiniteMaximum_nonneg _

theorem commonMeanMeta_nonneg (m d : ℕ) (B H : ℝ)
    (BS TS BP TP Packet Parameter Spatial : ℕ → ℝ) (Ds Dp r : ℕ) :
    0 ≤ commonMeanMeta m d B H BS TS BP TP Packet Parameter Spatial Ds Dp r :=
  round3PreparedFiniteMaximum_nonneg _

theorem commonMeanProfiles_given_prefix_congr
    (m d : ℕ) (Mb B H : ℝ) (BS TS BP TP Packet Packet' Parameter Spatial : ℕ → ℝ)
    (Ds Dp r : ℕ) (hPacket : ∀ k, k ≤ r → Packet k = Packet' k) :
    commonMeanForward m d Mb Packet Parameter Spatial r =
      commonMeanForward m d Mb Packet' Parameter Spatial r ∧
    commonMeanMeta m d B H BS TS BP TP Packet Parameter Spatial Ds Dp r =
      commonMeanMeta m d B H BS TS BP TP Packet' Parameter Spatial Ds Dp r ∧
    commonObserverInverse m d B Packet Parameter Spatial r =
      commonObserverInverse m d B Packet' Parameter Spatial r := by
  refine ⟨?_,?_,?_⟩
  · unfold commonMeanForward
    apply congrArg (round3PreparedFiniteMaximum (I := Fin (r+2)))
    funext k
    exact (commonObserverProfiles_prefix_congr m d Mb B Packet Packet' Parameter Parameter Spatial Spatial k
      (fun l hl => hPacket l (by omega)) (fun _ _ _ => rfl) (fun _ _ _ => rfl)).1
  · unfold commonMeanMeta commonAdaptedMeta
    apply congrArg (round3PreparedFiniteMaximum (I := Fin (r+1)))
    funext k
    apply originalCompositionProfile_prefix_congr
    · exact fun _ _ => rfl
    · intro l hl
      exact (commonObserverProfiles_prefix_congr m d Mb B Packet Packet' Parameter Parameter Spatial Spatial l
        (fun t ht => hPacket t (by omega)) (fun _ _ _ => rfl) (fun _ _ _ => rfl)).2
  · exact (commonObserverProfiles_prefix_congr m d Mb B Packet Packet' Parameter Parameter Spatial Spatial r
      (fun k hk => hPacket k (by omega)) (fun _ _ _ => rfl) (fun _ _ _ => rfl)).2

universe uM
variable {m d N : ℕ} {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

/-- The exact mean threshold using common numerical profiles. Packet can
carry actual high-order norms, but the theorem below removes its tail. -/
def commonPreparedThreshold
    (q Rsub Lactive : ℕ) (rho c cT Mb B H : ℝ) (hrho : 0 < rho)
    (BS TS BP TP Parameter Spatial Packet allowed : ℕ → ℝ) (Ds Dp : ℕ)
    (hAllowed : ∀ k, k ≤ (q+1)*(q+4)+2 → 0 ≤ allowed k) : ℝ :=
  let J := (q+1)*(q+4)+2
  let Forward := commonMeanForward m d Mb Packet Parameter Spatial
  let Meta := commonMeanMeta m d B H BS TS BP TP Packet Parameter Spatial Ds Dp
  let Inverse := commonObserverInverse m d B Packet Parameter Spatial
  finiteOriginalMeanThreshold.{uM,0} (m := m) (d := d) (N := N) (M := M)
    q Rsub Lactive rho c cT hrho
    (finitePrefixProfile J allowed) (finitePrefixProfile J Forward)
    (finitePrefixProfile J Meta) (finitePrefixProfile J Inverse)
    (finitePrefixProfile_nonneg J allowed hAllowed)
    (finitePrefixProfile_nonneg J Forward (fun k _ => commonMeanForward_nonneg m d Mb Packet Parameter Spatial k))

/-- This threshold has no Data, atlas, charts, cutoffs, or sample domains
among its arguments. All three low numbers are genuine geometric inputs. -/
def commonFiniteThreshold
    (q Rsub Lactive : ℕ) (rho c cT Mb B H : ℝ) (hrho : 0 < rho)
    (BS TS BP TP Parameter Spatial allowed : ℕ → ℝ) (Ds Dp : ℕ)
    (hAllowed : ∀ k, k ≤ (q+1)*(q+4)+2 → 0 ≤ allowed k) : ℝ :=
  commonPreparedThreshold (m := m) (d := d) (N := N) (M := M)
    q Rsub Lactive rho c cT Mb B H hrho BS TS BP TP Parameter Spatial
    (finitePrefixProfile ((q+1)*(q+4)+2) allowed) allowed Ds Dp hAllowed

theorem commonPreparedThreshold_eq_finite
    (q Rsub Lactive : ℕ) (rho c cT Mb B H : ℝ) (hrho : 0 < rho)
    (BS TS BP TP Parameter Spatial Packet allowed : ℕ → ℝ) (Ds Dp : ℕ)
    (hAllowed : ∀ k, k ≤ (q+1)*(q+4)+2 → 0 ≤ allowed k)
    (hPacket : ∀ k, k ≤ (q+1)*(q+4)+2 → Packet k = allowed k) :
    commonPreparedThreshold (m := m) (d := d) (N := N) (M := M)
      q Rsub Lactive rho c cT Mb B H hrho BS TS BP TP Parameter Spatial Packet allowed Ds Dp hAllowed =
    commonFiniteThreshold (m := m) (d := d) (N := N) (M := M)
      q Rsub Lactive rho c cT Mb B H hrho BS TS BP TP Parameter Spatial allowed Ds Dp hAllowed := by
  let J := (q+1)*(q+4)+2
  have hProfiles (r : ℕ) (hr : r ≤ J) :=
    commonMeanProfiles_given_prefix_congr m d Mb B H BS TS BP TP Packet
      (finitePrefixProfile J allowed) Parameter Spatial Ds Dp r (fun k hk =>
        (hPacket k (hk.trans hr)).trans (finitePrefixProfile_eq J allowed k (hk.trans hr)).symm)
  unfold commonFiniteThreshold commonPreparedThreshold
  apply finiteOriginalMeanThreshold_prefix_congr
  · exact fun _ _ => rfl
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
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.commonPreparedThreshold_eq_finite
