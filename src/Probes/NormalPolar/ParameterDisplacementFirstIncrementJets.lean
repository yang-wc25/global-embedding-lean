import NormalPolar.ParameterDisplacementPrimaryJets
import Probes.ActualSecondaryCompleteMetricJets

/-!
# Jets of the same complete first increment

The primary is the common actual background/prescribed array. Every signed
ordered mixed-secondary piece belongs to the very same supplied physical
data array. Its local solver and support-sum theorems produce the secondary
budget internally. The complete U0 is never supplied with its own jet bound.
-/

noncomputable section
open Set Function Manifold GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m N p r : ℕ} {Ep M Λ Β SubSecondary : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype SubSecondary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)

/-- The same global secondary sum is smooth after any genuine smooth
observation, including a fixed-parameter source chart. -/
theorem actual_secondary_sum_arbitrary_observation_smooth
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    {n j : ℕ} {ell Mg CH delta : ℝ} {W : Set (Ep × M)}
    (data : ActualSecondarySignedRecord (Λ ⊕ Fin r) → SubSecondary →
      ActualSecondaryPhysicalPieceData F hF n j ell Mg CH delta W)
    (tau : ℝ) (length : ℕ) (hW : IsOpen W)
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (kappa : Y → Ep × M) (Omega : Set Y)
    (hkappa : ContMDiffOn 𝓘(ℝ,Y) ((𝓘(ℝ,Ep)).prod IM) ∞ kappa Omega)
    (hmap : MapsTo kappa Omega W) :
    ContDiffOn ℝ ∞ (actualConstructedSecondarySum F hF
      (fun rec b => (data rec b).base) tau length ∘ kappa) Omega := by
  change ContDiffOn ℝ ∞ (fun z => actualSecondaryRefinedNonzeroSum
    (actualConstructedSecondaryFamily F hF (fun rec b => (data rec b).base) tau length) (kappa z)) Omega
  rw [actual_secondary_refined_sum_eq_records]
  apply ContDiffOn.sum
  intro rec hr
  apply ContDiffOn.sum
  intro b _
  have hq := (Finset.mem_filter.mp hr).2
  have hm := (((data ⟨rec,hq⟩ b).base.wave_regular tau length hW).1.comp hkappa hmap).contDiffOn
  simpa only [actualConstructedSecondaryFamily, dif_pos hq, Function.comp_def] using hm

/-- The full map is literally the complete common primary plus all actual
secondary pieces of that same common array. -/
def actualProbeCompleteFirstIncrement
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := IM) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (label : (Fin r × Bool) ↪ Fin p)
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := IM) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (backgroundLength probeLength : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (input : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
    (u : Fin p → ℝ)
    {n j : ℕ} {ell Mg CH delta : ℝ} {W : Set (Ep × M)}
    (data : ActualSecondarySignedRecord (Λ ⊕ Fin r) → SubSecondary →
      ActualSecondaryPhysicalPieceData F hF n j ell Mg CH delta W)
    (tau : ℝ) (length : ℕ) (z : Ep × M) : V :=
  round4ParameterProbeCombinedPrimary F hF g label c vf phase tau delta
    backgroundLength probeLength a input u z +
  actualConstructedSecondarySum F hF (fun rec b => (data rec b).base) tau length z

/-- Fast jets of the entire U0, with its primary jet budget proved from the
actual two channel profiles and its secondary budget proved from actual
physical piece data. All mixed records are retained. -/
theorem actual_complete_first_increment_weighted_jets
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := IM) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (label : (Fin r × Bool) ↪ Fin p)
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := IM) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (backgroundLength probeLength : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (input : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
    (u : Fin p → ℝ)
    (n j length : ℕ) (ell Mg CH delta tau : ℝ) (W : Set (Ep × M))
    (data : ActualSecondarySignedRecord (Λ ⊕ Fin r) → SubSecondary →
      ActualSecondaryPhysicalPieceData F hF n (j+1) ell Mg CH delta W)
    (hbudget : j+2+length ≤ n)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (htau : 0 < tau) (htaul : tau ≤ ell)
    (hdelta : 0 ≤ delta) (hdeltatau : delta ≤ tau) (hMg : 0 ≤ Mg) (hCH : 0 ≤ CH) (hW : IsOpen W)
    (K : (Λ ⊕ Fin r) → Set (Ep × M))
    (hprimary : ∀ rec b, (data rec b).base.support ⊆ K rec.val.1.1 ∩ K rec.val.1.2)
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (kappa : Y → Ep × M) (Omega S : Set Y) (hOmega : IsOpen Omega) (hSOmega : S ⊆ Omega)
    (hkappa : ContMDiffOn 𝓘(ℝ,Y) ((𝓘(ℝ,Ep)).prod IM) ∞ kappa Omega)
    (hmap : MapsTo kappa Omega W)
    (O : ActualSecondarySignedRecord (Λ ⊕ Fin r) → SubSecondary → Set Y)
    (hO : ∀ rec b, IsOpen (O rec b))
    (hactiveO : ∀ rec b, S ∩ kappa ⁻¹' (data rec b).base.support ⊆ O rec b)
    (hsource : ∀ rec b, MapsTo kappa (O rec b) (data rec b).base.chart.source)
    (htransition : ∀ rec b, ContDiffOn ℝ ∞ ((data rec b).base.chart ∘ kappa) (O rec b))
    (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i)
    (hsample : ∀ rec b y, y ∈ S ∩ kappa ⁻¹' (data rec b).base.support →
      (data rec b).base.chart (kappa y) ∈ (data rec b).base.sample)
    (htransitionb : ∀ rec b y, y ∈ S ∩ kappa ⁻¹' (data rec b).base.support →
      ∀ i, 1 ≤ i → i ≤ j+1 →
        ell ^ (i-1) * ‖iteratedFDeriv ℝ i ((data rec b).base.chart ∘ kappa) y‖ ≤ T i)
    (L R : ℕ)
    (hL : ∀ y ∈ S, (Finset.univ.filter (fun l => kappa y ∈ K l)).card ≤ L)
    (hR : ∀ rec : ActualSecondarySignedRecord (Λ ⊕ Fin r), ∀ y ∈ S,
      (Finset.univ.filter (fun b => kappa y ∈ (data rec b).base.support)).card ≤ R)
    (Mphase KR KI : ℝ) (hKR : 0 ≤ KR) (hKI : 0 ≤ KI) :
    let phi := fun l => Sum.elim g.phase phase l ∘ kappa
    let ZR := fun l => round4ParameterProbeCombinedAmplitude F hF g label c vf tau delta
      backgroundLength probeLength a input u false l ∘ kappa
    let ZI := fun l => round4ParameterProbeCombinedAmplitude F hF g label c vf tau delta
      backgroundLength probeLength a input u true l ∘ kappa
    (∀ l, ContDiffOn ℝ ∞ (phi l) Omega) →
    (∀ l, ContDiffOn ℝ ∞ (ZR l) Omega) → (∀ l, ContDiffOn ℝ ∞ (ZI l) Omega) →
    (∀ l k, k < j+1 → ∀ y ∈ S, ell ^ k * ‖iteratedFDeriv ℝ (k+1) (phi l) y‖ ≤ Mphase) →
    (∀ l k, k ≤ j+1 → ∀ y ∈ S, ell ^ k * ‖iteratedFDeriv ℝ k (ZR l) y‖ ≤ KR * delta * tau) →
    (∀ l k, k ≤ j+1 → ∀ y ∈ S, ell ^ k * ‖iteratedFDeriv ℝ k (ZI l) y‖ ≤ KI * delta * tau) →
    let Cprimary := actualFinitePrimaryJetConstant (Fintype.card (Λ ⊕ Fin r)) N (j+1) Mphase KR KI
    let Csecondary := actualConstructedSecondaryWaveBudget m N n (j+1) length L R Mg CH T
    let U := actualProbeCompleteFirstIncrement F hF g label c vf phase backgroundLength probeLength
      a input u data tau length ∘ kappa
    ContDiffOn ℝ ∞ U Omega ∧ ∀ k ≤ j+1, ∀ y ∈ S,
      tau ^ k * ‖iteratedFDeriv ℝ k U y‖ ≤ (Cprimary + Csecondary) * delta * tau := by
  intro phi ZR ZI hphase hZR hZI hpb hRb hIb Cprimary Csecondary U
  have hfirst := actual_combined_primary_weighted_jets F hF g label c vf phase
    backgroundLength probeLength a input u kappa Omega S hOmega hSOmega
    (j+1) tau ell delta Mphase KR KI htau htaul hell1 hdelta hKR hKI
    hphase hZR hZI hpb hRb hIb
  have hsecondSmooth := actual_secondary_sum_arbitrary_observation_smooth
    F hF data tau length hW kappa Omega hkappa hmap
  have hsecond := actual_constructed_secondary_sum_weighted_jets F hF
    (fun rec b => (data rec b).base) tau length (by omega)
    hell hell1 htau htaul hMg hCH hW K hprimary kappa Omega S hOmega hSOmega
    hkappa.continuousOn hmap O hO hactiveO hsource htransition T hT hsample
    htransitionb L R hL hR
  have hCsecondary : 0 ≤ Csecondary := by
    have hcost := actualSecondaryForcedWaveCost_nonneg m N n length (j+1) Mg CH hMg hCH
    have hprefix := actualFastChartTransferPrefix_nonneg T hT (j+1)
    dsimp only [Csecondary,actualConstructedSecondaryWaveBudget]
    positivity
  refine ⟨hfirst.1.add hsecondSmooth, ?_⟩
  intro k hk y hy
  have hsum := actual_joint_slow_add_jet_bound
    (round4ParameterProbeCombinedPrimary F hF g label c vf phase tau delta
      backgroundLength probeLength a input u ∘ kappa)
    (actualConstructedSecondarySum F hF (fun rec b => (data rec b).base) tau length ∘ kappa)
    k tau (Cprimary * delta * tau) (Csecondary * delta ^ 2) htau.le y
    ((hfirst.1.contDiffAt (hOmega.mem_nhds (hSOmega hy))).of_le (by simp))
    ((hsecondSmooth.contDiffAt (hOmega.mem_nhds (hSOmega hy))).of_le (by simp))
    (hfirst.2 k hk y hy) (hsecond.2 k hk y hy)
  apply hsum.trans
  have hmul := mul_le_mul_of_nonneg_left hdeltatau hdelta
  have habs := mul_le_mul_of_nonneg_left hmul hCsecondary
  nlinarith

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_secondary_sum_arbitrary_observation_smooth
#print axioms GlobalEmbedding.Continuation.actual_complete_first_increment_weighted_jets
