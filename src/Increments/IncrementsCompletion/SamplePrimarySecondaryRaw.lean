import IncrementsCompletion.OriginalFinitePrimaryAtlas
import IncrementsCompletion.SampleNativeRawCount
import Probes.Round3ParameterSecondaryCommonRawAtlas
import Probes.ActualRawProfileBudgets

/-!
# Actual secondary assembly for the already constructed K and G

The primary package is produced by the actual finite trajectory.  A coherent
secondary factory supplies one physical choice and its native families.
This theorem constructs every complete raw atlas internally from those two
actual objects.  It retains their same native input K, final domain G,
canonical observer domains, and original samples.  Only numerical upper
budgets are enlarged; no geometric field or correction is replaced.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
universe uM uP uPrimary uSecondary
variable {m d N : ℕ} {M : Type uM} {P : Type uP}
  {Β : Type uPrimary} {SubSecondary : Type uSecondary}
  [TopologicalSpace M] [TopologicalSpace P] [Fintype Β] [Fintype SubSecondary]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

theorem incrementsCompletion_sample_secondary_raw_from_actual_primary
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Β)
      (fun p x => Data.F (p,x)))
    (hTarget : ∀ nu beta z, z ∈ (g.chart nu beta).target → z.1 ∈ Data.parameterOpen)
    (V0 : Set P)
    (K : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (Lactive : ℕ) (hCutoff : g.cutoff = Data.cutoff)
    (hCount : ∀ z ∈ Data.parameterSet ×ˢ (univ : Set M),
      (Finset.univ.filter (fun nu => z ∈ incrementsOriginalRelativeCutoffSupport Data nu)).card ≤ Lactive)
    (q Rsub : ℕ) (rho ell tau : ℝ) (Bnd Mg T : ℕ → ℝ)
    (primary : IncrementsCompletionOriginalPrimaryAtlas Data hd hs g hTarget V0 K
      q Rsub rho ell tau Bnd Mg T) :
    let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet
    let F := fullIncrementNovOriginalSourceSlice Data
    let hF := fullIncrementNov_original_source_slice_smooth Data hd hs
    let G := primary.domain
    let gG := round3Parameter_restrictPrimaryFamily F
      (fullIncrementNovOriginalOpenFamily Data g hTarget) G primary.domain_open
    ∀ (Msec Cut Tinv Tobs : ℕ → ℝ), (∀ j, Mg (j+q+4) ≤ Msec j) → ∀ Rsecondary,
    ∀ (choice : ActualSecondarySignedRecord (Fin Data.primaryCount) → SubSecondary →
      Round3ParameterSecondaryChoice P M m)
    (family : ∀ ip : Fin Data.parameterCount,
      Round3ParameterPreparedSecondaryFamily (SubSecondary := SubSecondary) Data
        (fun p => F ((Data.parameterChart ip).symm p)) (fun p => hF ((Data.parameterChart ip).symm p))
        (round3ParameterNativePrimary F gG (Data.parameterChart ip)) q ell
        (round3ParameterNativeDomain (Data.parameterChart ip) G)
        (round3ParameterNativeDomain (Data.parameterChart ip) G)
        Msec Cut Tinv Tobs Rsecondary
        (fun i => (parameterTensorModelEquiv (m+1) d) ⁻¹' S (i.1,ip))),
    (∀ ip, (family ip).choice = round3ParameterNativeChoices choice (Data.parameterChart ip)) →
    ∀ delta j, Nonempty (Round3ParameterRawAtlasData (Tr := ℝ) Data.atlas Data.parameterChart F hF gG K K
      (j+2*q+8) (j+q+4) j q Rsub Lactive Rsecondary (rho/4)
      (Bnd (j+q+4)) (Msec j) (Cut j) T Tinv Tobs G Data.primaryDomain S ell delta tau 0 choice) := by
  intro S F hF G gG Msec Cut Tinv Tobs hMg Rsecondary choice family hChoice delta j
  let s := j+q+4
  obtain ⟨raw,hO⟩ := primary.raw s
  have hEnlarged (i : Fin Data.atlas.count × Fin Data.parameterCount) :=
    actual_raw_profiles_enlarge_budgets (s+(q+4)) (q+2) s Rsub Data.primaryCount
      (rho/4) (Bnd s) (Mg s) (Bnd s) (Msec j) T le_rfl (hMg j)
      _ _ _ _ _ _ _ _ _ _ _ _ _ (raw.raw i)
  have hCutoffG : gG.cutoff = Data.cutoff := hCutoff
  have hInputOrder : s+(q+4) = j+2*q+8 := by dsimp [s]; omega
  have hSolve : actualSecondarySolveOrder q j = s := rfl
  have result := round3Parameter_secondary_common_raw_atlas Data hd F hF gG q ell G
    Msec Cut Tinv Tobs Rsecondary S choice family hChoice K K (s+(q+4)) j Rsub Lactive
    (rho/4) (Bnd s) T Data.primaryDomain delta tau 0 (by
      intro i
      have hi := hEnlarged i
      rw [congrFun hO i] at hi
      have rawActive := incrementsCompletion_native_raw_sample_count Data hd F hF gG i
        K K (s+(q+4)) (q+2) s Rsub Data.primaryCount Lactive (rho/4) (Bnd s) (Msec j) T
        G Data.primaryDomain
        (actualRawObserverOpen (Data.atlas.chart i.1) (round3ParameterNativeDomain (Data.parameterChart i.2) G))
        tau ell 0 hCutoffG hCount hi
      simpa only [hSolve] using rawActive)
  simpa only [hInputOrder,hSolve] using result

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_sample_secondary_raw_from_actual_primary
