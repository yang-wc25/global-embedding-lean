import OriginalIncrements.CommonMeanNumerics

/-! The common numerical entrance is unchanged by all input tails above
its actual finite reads. These formulas contain no original data or atlas;
the low geometric numbers are explicitly held fixed. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation.OriginalIncrements
open CollarCompletion OriginalCollars FaithfulIncrements

theorem commonMeanProfiles_prefix_congr
    (m d : ℕ) (Mb B H : ℝ)
    (BS BS' TS TS' BP BP' TP TP' Packet Packet' Parameter Parameter' Spatial Spatial' : ℕ → ℝ)
    (Ds Dp r : ℕ)
    (hBS : ∀ k, k ≤ r → BS k = BS' k) (hTS : ∀ k, k ≤ r → TS k = TS' k)
    (hBP : ∀ k, k ≤ r → BP k = BP' k) (hTP : ∀ k, k ≤ r → TP k = TP' k)
    (hPacket : ∀ k, k ≤ r → Packet k = Packet' k)
    (hParameter : ∀ k, k ≤ r+1 → Parameter k = Parameter' k)
    (hSpatial : ∀ k, k ≤ r+1 → Spatial k = Spatial' k) :
    commonMeanForward m d Mb Packet Parameter Spatial r =
      commonMeanForward m d Mb Packet' Parameter' Spatial' r ∧
    commonMeanMeta m d B H BS TS BP TP Packet Parameter Spatial Ds Dp r =
      commonMeanMeta m d B H BS' TS' BP' TP' Packet' Parameter' Spatial' Ds Dp r ∧
    commonObserverInverse m d B Packet Parameter Spatial r =
      commonObserverInverse m d B Packet' Parameter' Spatial' r := by
  refine ⟨?_,?_,?_⟩
  · unfold commonMeanForward
    apply congrArg (round3PreparedFiniteMaximum (I := Fin (r+2)))
    funext k
    exact (commonObserverProfiles_prefix_congr m d Mb B Packet Packet' Parameter Parameter' Spatial Spatial' k
      (fun l hl => hPacket l (by omega)) (fun l _ hl => hParameter l (by omega))
      (fun l _ hl => hSpatial l (by omega))).1
  · unfold commonMeanMeta commonAdaptedMeta
    apply congrArg (round3PreparedFiniteMaximum (I := Fin (r+1)))
    funext k
    apply originalCompositionProfile_prefix_congr
    · intro l hl
      exact uniformOriginalObserverCutoffProfile_prefix_congr m d H
        BS BS' TS TS' BP BP' TP TP' Parameter Parameter' Spatial Spatial' Ds Dp l
        (fun t ht => hBS t (by omega)) (fun t ht => hTS t (by omega))
        (fun t ht => hBP t (by omega)) (fun t ht => hTP t (by omega))
        (fun t ht => hParameter t (by omega)) (fun t ht => hSpatial t (by omega))
    · intro l hl
      exact (commonObserverProfiles_prefix_congr m d Mb B Packet Packet' Parameter Parameter' Spatial Spatial' l
        (fun t ht => hPacket t (by omega)) (fun t _ ht => hParameter t (by omega))
        (fun t _ ht => hSpatial t (by omega))).2
  · exact (commonObserverProfiles_prefix_congr m d Mb B Packet Packet' Parameter Parameter' Spatial Spatial' r
      (fun k hk => hPacket k (by omega)) (fun k _ hk => hParameter k (by omega))
      (fun k _ hk => hSpatial k (by omega))).2

universe uM
variable {m d N : ℕ} {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

/-- The displayed common finite entrance reads Given/raw through J and
transitions through J+1. Later observation order never appears. -/
theorem commonFiniteThreshold_prefix_congr
    (q Rsub Lactive : ℕ) (rho c cT Mb B H : ℝ) (hrho : 0 < rho)
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
    commonFiniteThreshold (m := m) (d := d) (N := N) (M := M)
      q Rsub Lactive rho c cT Mb B H hrho BS TS BP TP Parameter Spatial allowed Ds Dp hAllowed =
    commonFiniteThreshold (m := m) (d := d) (N := N) (M := M)
      q Rsub Lactive rho c cT Mb B H hrho BS' TS' BP' TP' Parameter' Spatial' allowed' Ds Dp hAllowed' := by
  let J := (q+1)*(q+4)+2
  have hProfiles (r : ℕ) (hr : r ≤ J) :=
    commonMeanProfiles_prefix_congr m d Mb B H BS BS' TS TS' BP BP' TP TP'
      (finitePrefixProfile J allowed) (finitePrefixProfile J allowed') Parameter Parameter' Spatial Spatial' Ds Dp r
      (fun k hk => hBS k (hk.trans hr)) (fun k hk => hTS k (hk.trans hr))
      (fun k hk => hBP k (hk.trans hr)) (fun k hk => hTP k (hk.trans hr))
      (fun k hk => by
        rw [finitePrefixProfile_eq J allowed k (hk.trans hr),
          finitePrefixProfile_eq J allowed' k (hk.trans hr)]
        exact hGiven k (hk.trans hr))
      (fun k hk => hParameter k (by dsimp only [J] at hr; omega))
      (fun k hk => hSpatial k (by dsimp only [J] at hr; omega))
  unfold commonFiniteThreshold commonPreparedThreshold
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
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.commonFiniteThreshold_prefix_congr
