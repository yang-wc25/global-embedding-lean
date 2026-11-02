import Probes.ActualIncrementOriginalNativeRawProfiles
import Probes.ActualIncrementOriginalRawFixedTransition
import Smoothing.ParameterRound2GlobalCorrectionSupport

/-! The original refinement sample ABI for an arbitrary physical parameter
manifold. The native family has Euclidean observer parameters; the ORIGINAL
Data, evaluation domains and original parameter charts remain on P.

Genuine fixed refinement data over a prepared neighborhood of the compact
parameter set. Only the original evaluation samples enter the numerical
bounds. Restricting to an input-dependent positive germ preserves these
same charts, cutoff values, derivative bounds and local multiplicities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff Topology ENNReal Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
variable {Β : Type*} [Fintype Β]

def round3ParameterRefinementActive
    (Data : IncrementsOriginalNativeData (m+1) d N M P) (ip : Fin Data.parameterCount)
    (F : Ep → M → V)
    (g0 : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := Β) F)
    (W : Set (Ep × M)) (observer : Fin Data.atlas.count) (nu : Fin Data.primaryCount) (beta : Β) : Set X :=
    ((parameterTensorModelEquiv (m+1) d) ⁻¹' incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet (observer,ip) ∩
      (fun z : X => (z.1,(Data.atlas.chart observer).symm z.2)) ⁻¹'
        incrementsGlobalRelativeSupport W (g0.cutoff nu)) ∩
    (fun z : X => (z.1,(Data.atlas.chart observer).symm z.2)) ⁻¹'
      incrementsGlobalRelativeSupport W (fun z => g0.eta nu beta z*g0.cutoff nu z)

def round3ParameterRefinementSample
    (Data : IncrementsOriginalNativeData (m+1) d N M P) (ip : Fin Data.parameterCount)
    (F : Ep → M → V)
    (g0 : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := Β) F)
    (W : Set (Ep × M)) (observer : Fin Data.atlas.count) (nu : Fin Data.primaryCount) (beta : Β) : Set X :=
  (fun z : X => g0.chart nu beta (z.1,(Data.atlas.chart observer).symm z.2)) ''
    round3ParameterRefinementActive Data ip F g0 W observer nu beta

structure Round3ParameterRefinementSamples
    (Data : IncrementsOriginalNativeData (m+1) d N M P) (ip : Fin Data.parameterCount)
    (F : Ep → M → V)
    (g0 : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := Β) F)
    (host : Fin Data.primaryCount → Β → Fin Data.atlas.count)
    (b : Fin Data.primaryCount → Β → OpenPartialHomeomorph X X)
    (W : Set (Ep × M)) (ell : ℝ) (Tinv Forward Meta : ℕ → ℝ) (Rsub Lprimary : ℕ) : Prop where
  eta_smooth : ∀ nu beta, ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (g0.eta nu beta) W
  eta_support : ∀ nu beta, incrementsGlobalRelativeSupport W (g0.eta nu beta) ⊆ (g0.chart nu beta).source
  partition : ∀ nu z, z ∈ incrementsGlobalRelativeSupport W (g0.cutoff nu) →
    ∀ᶠ w in 𝓝 z, ∑ beta, g0.eta nu beta w = 1
  sample_inverse : ∀ observer nu beta,
    MapsTo (b nu beta).symm (round3ParameterRefinementSample Data ip F g0 W observer nu beta)
      ((parameterTensorModelEquiv (m+1) d) ⁻¹' incrementsOriginalEvaluation Data.atlas Data.parameterChart
        Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet (host nu beta,ip))
  inverse_jets : ∀ observer nu beta k, 1 ≤ k → ∀ z ∈ round3ParameterRefinementSample Data ip F g0 W observer nu beta,
    ell^(k-1)*‖iteratedFDeriv ℝ k (b nu beta).symm z‖ ≤ Tinv k
  forward_jets : ∀ r observer nu beta k, 1 ≤ k → k ≤ r+1 →
    ∀ z ∈ round3ParameterRefinementActive Data ip F g0 W observer nu beta,
    ell^(k-1)*‖iteratedFDeriv ℝ k (b nu beta)
      (actualOriginalObserverHostTransition Data (observer,ip) (host nu beta) z)‖ ≤ Forward r
  eta_jets : ∀ r observer nu beta k, k ≤ r →
    ∀ z ∈ round3ParameterRefinementSample Data ip F g0 W observer nu beta,
    ell^k*‖iteratedFDeriv ℝ k (g0.eta nu beta ∘ (g0.chart nu beta).symm) z‖ ≤ Meta r
  eta_count : ∀ nu w, w ∈ W →
    (Finset.univ.filter (fun beta => w ∈ incrementsGlobalRelativeSupport W (g0.eta nu beta))).card ≤ Rsub
  primary_count : ∀ w ∈ W,
    (Finset.univ.filter (fun nu => w ∈ incrementsGlobalRelativeSupport W (g0.cutoff nu))).card ≤ Lprimary

private theorem round3Parameter_refinement_relativeSupport_mono_open
    (W G : Set (Ep × M)) (hW : IsOpen W) (hG : IsOpen G) (hGW : G ⊆ W)
    (f : Ep × M → ℝ) : incrementsGlobalRelativeSupport G f ⊆ incrementsGlobalRelativeSupport W f := by
  rw [parameterRound2_global_relativeSupport_eq G hG,parameterRound2_global_relativeSupport_eq W hW]
  exact fun z hz => ⟨hGW hz.1,hz.2⟩

theorem round3Parameter_refinement_samples_restrict
    (Data : IncrementsOriginalNativeData (m+1) d N M P) (ip : Fin Data.parameterCount)
    (F : Ep → M → V)
    (g0 : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := Β) F)
    (host : Fin Data.primaryCount → Β → Fin Data.atlas.count)
    (b : Fin Data.primaryCount → Β → OpenPartialHomeomorph X X)
    (W G : Set (Ep × M)) (hW : IsOpen W) (hG : IsOpen G) (hGW : G ⊆ W)
    (ell : ℝ) (Tinv Forward Meta : ℕ → ℝ) (Rsub Lprimary : ℕ)
    (h : Round3ParameterRefinementSamples Data ip F g0 host b W ell Tinv Forward Meta Rsub Lprimary) :
    Round3ParameterRefinementSamples Data ip F g0 host b G ell Tinv Forward Meta Rsub Lprimary := by
  have hrel (f : Ep × M → ℝ) := round3Parameter_refinement_relativeSupport_mono_open W G hW hG hGW f
  have hactive (observer nu beta) : round3ParameterRefinementActive Data ip F g0 G observer nu beta ⊆
      round3ParameterRefinementActive Data ip F g0 W observer nu beta :=
    fun z hz => ⟨⟨hz.1.1,hrel (g0.cutoff nu) hz.1.2⟩,
      hrel (fun w : Ep × M => g0.eta nu beta w*g0.cutoff nu w) hz.2⟩
  have hsample (observer nu beta) : round3ParameterRefinementSample Data ip F g0 G observer nu beta ⊆
      round3ParameterRefinementSample Data ip F g0 W observer nu beta :=
    image_mono (hactive observer nu beta)
  refine {
    eta_smooth := fun nu beta => (h.eta_smooth nu beta).mono hGW
    eta_support := fun nu beta z hz => h.eta_support nu beta (hrel _ hz)
    partition := fun nu z hz => h.partition nu z (hrel _ hz)
    sample_inverse := fun observer nu beta z hz => h.sample_inverse observer nu beta (hsample observer nu beta hz)
    inverse_jets := fun observer nu beta k hk z hz => h.inverse_jets observer nu beta k hk z (hsample observer nu beta hz)
    forward_jets := fun r observer nu beta k hk hkr z hz => h.forward_jets r observer nu beta k hk hkr z (hactive observer nu beta hz)
    eta_jets := fun r observer nu beta k hkr z hz => h.eta_jets r observer nu beta k hkr z (hsample observer nu beta hz)
    eta_count := ?_
    primary_count := ?_ }
  · intro nu w hw
    apply (Finset.card_le_card ?_).trans (h.eta_count nu w (hGW hw))
    intro beta hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hrel _ (Finset.mem_filter.mp hb).2⟩
  · intro w hw
    apply (Finset.card_le_card ?_).trans (h.primary_count w (hGW hw))
    intro nu hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hrel _ (Finset.mem_filter.mp hn).2⟩

#print axioms round3Parameter_refinement_samples_restrict
end GlobalEmbedding.Continuation
