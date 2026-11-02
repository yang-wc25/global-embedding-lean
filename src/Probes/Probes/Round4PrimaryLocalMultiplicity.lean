import Smoothing.TensorSetupProviders
import Probes.Round3ParameterNativeRefinementSamples

/-!
The primary-label count used by the actual mean construction is a local
support count.  This module derives it from the same subordinate cutoffs and
a bounded number of basis labels per host.  Neither the number of hosts nor
the total number of primary modes occurs in the resulting bound.

The hypotheses on the host and basis label describe the original geometric
preparation.  They do not assert a bound on a computed mean or on an increment.
The resulting count is transported to the actual parameter observer charts.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

theorem round4_primary_count_of_subordinate_labels
    {X Host Label : Type*} [TopologicalSpace X] [Fintype Host] [Fintype Label]
    (rho : Host → X → ℝ) (chi : Label → X → ℝ)
    (K R : ℕ) (host : Label → Host) (slot : Label → Fin K)
    (hlabel : Function.Injective (fun nu => (host nu, slot nu)))
    (hsub : ∀ nu, tsupport (chi nu) ⊆ tsupport (rho (host nu)))
    (hcount : ∀ z, (activeCutoffIndices rho z).card ≤ R) (z : X) :
    (Finset.univ.filter (fun nu => z ∈ tsupport (chi nu))).card ≤ R * K := by
  classical
  let s := Finset.univ.filter (fun nu => z ∈ tsupport (chi nu))
  let t := (activeCutoffIndices rho z).product (Finset.univ : Finset (Fin K))
  have hinj : s.card ≤ t.card := Finset.card_le_card_of_injOn
    (fun nu => (host nu, slot nu)) (by
      intro nu hnu
      exact Finset.mem_product.mpr ⟨
        (mem_activeCutoffIndices rho z (host nu)).mpr (hsub nu (Finset.mem_filter.mp hnu).2),
        Finset.mem_univ _⟩) (fun _ _ _ _ h => hlabel h)
  calc
    s.card ≤ t.card := hinj
    _ = (activeCutoffIndices rho z).card * K := by simp [t]
    _ ≤ R * K := Nat.mul_le_mul_right K (hcount z)

theorem round4_primary_count_of_normalized_hosts
    {X Host Label : Type*} [TopologicalSpace X] [Fintype Host] [Fintype Label]
    (raw : Host → X → ℝ) (W : Host → Set X)
    (hraw : ∀ a, tsupport (raw a) ⊆ W a)
    (D K : ℕ) (hdegree : ∀ a, tensorEnlargedSupportDegree W a ≤ D)
    (chi : Label → X → ℝ) (host : Label → Host) (slot : Label → Fin K)
    (hlabel : Function.Injective (fun nu => (host nu, slot nu)))
    (hsub : ∀ nu, tsupport (chi nu) ⊆ tsupport (squareNormalizedCutoff raw (host nu)))
    (z : X) :
    (Finset.univ.filter (fun nu => z ∈ tsupport (chi nu))).card ≤ (D + 1) * K :=
  round4_primary_count_of_subordinate_labels (squareNormalizedCutoff raw) chi K (D+1)
    host slot hlabel hsub
    (squareNormalizedCutoff_card_le_enlarged_degree W raw hraw D hdegree) z

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem round4Parameter_native_primary_count
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    {Sub : Type*} [Fintype Sub]
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m)
      (Λ := Fin Data.primaryCount) (Β := Sub) (fun p x => Data.F (p,x)))
    (hcut : g.cutoff = Data.cutoff)
    (B : OpenPartialHomeomorph P Ep)
    (W : Set (Ep × M)) (hW : IsOpen W)
    (hWB : W ⊆ B.target ×ˢ (univ : Set M))
    (L : ℕ)
    (hcount : ∀ z, (Finset.univ.filter (fun nu => z ∈ tsupport (Data.cutoff nu))).card ≤ L) :
    let gN := round3ParameterNativePrimary (fun p x => Data.F (p,x)) g B
    ∀ z ∈ W, (Finset.univ.filter (fun nu =>
      z ∈ incrementsGlobalRelativeSupport W (gN.cutoff nu))).card ≤ L := by
  intro gN z hz
  apply (Finset.card_le_card ?_).trans (hcount (B.symm z.1,z.2))
  intro nu hnu
  have hn := (Finset.mem_filter.mp hnu).2
  rw [parameterRound2_global_relativeSupport_eq W hW] at hn
  have hp := round3Parameter_plain_pullback_tsupport
    (round3ParameterProductChart (M := M) B) (g.cutoff nu) z (hWB hz) hn.2
  rw [hcut] at hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩

theorem round4Parameter_native_original_refinement_samples_local
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    {Sub : Type*} [Fintype Sub]
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m)
      (Λ := Fin Data.primaryCount) (Β := Sub) (fun p x => Data.F (p,x)))
    (R L : ℕ) (hg : Round3ParameterOriginalPrimaryGeometry Data g R)
    (hcount : ∀ z, (Finset.univ.filter (fun nu => z ∈ tsupport (Data.cutoff nu))).card ≤ L)
    (ip : Fin Data.parameterCount)
    (host : Fin Data.primaryCount → Sub → Fin Data.atlas.count)
    (b : Fin Data.primaryCount → Sub → OpenPartialHomeomorph X X)
    (hChart : ∀ nu a, actualHostAdaptedChart (Data.atlas.chart (host nu a)) (b nu a) =
      (round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart ip)).chart nu a)
    (hSource : ∀ nu a, (b nu a).source ⊆
      (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart (host nu a))).target)
    (hInner : ∀ nu a y, y ∈ ((round3ParameterNativePrimary (fun p x => Data.F (p,x)) g
      (Data.parameterChart ip)).chart nu a).source → y.2 ∈ Data.atlas.inner (host nu a))
    (Forward Inverse Meta : ℕ → ℝ)
    (hProfiles : Round3ParameterOriginalChartProfiles Data g Forward Inverse Meta)
    (ell : ℝ) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (W : Set (Ep × M)) (hW : IsOpen W)
    (hWB : W ⊆ (Data.parameterChart ip).target ×ˢ (univ : Set M)) :
    let gN := round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart ip)
    Round3ParameterRefinementSamples Data ip (fun p x => Data.F ((Data.parameterChart ip).symm p,x))
      gN host b W ell Inverse
      (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+2) => Forward k))
      (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+1) => Meta k)) R L := by
  intro gN
  have old := round3Parameter_native_original_refinement_samples Data hd g R hg ip host b
    hChart hSource hInner Forward Inverse Meta hProfiles ell hell hell1 W hW hWB
  exact { old with
    primary_count := round4Parameter_native_primary_count Data g hg.cutoff
      (Data.parameterChart ip) W hW hWB L hcount }

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_primary_count_of_normalized_hosts
#print axioms GlobalEmbedding.Continuation.round4Parameter_native_original_refinement_samples_local
