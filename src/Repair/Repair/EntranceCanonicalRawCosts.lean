import Repair.EntranceCanonicalRawMapNorms
import Repair.EntranceCanonicalRawMetricNorms
import Probes.Round4ParameterFiniteProfiles
import Probes.Round3ParameterActualIncrementNorms
import Probes.Round3ParameterActualMetricRemainder

/-!
# Named finite-order constants for the actual general-parameter increment

The two constants are selected after truncating all transition profiles to
orders actually consumed by the finite solver. Their bounds concern the
same literal physical U, the same native mean, and the unchanged original
full-joint norms. Equality of finite prefixes gives equality of the selected
constants, not merely the existence of alternative upper bounds.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal Topology
namespace GlobalEmbedding.Continuation
universe uM uTr uP uLabel uPrimary uSecondary
variable {m d N : ℕ} {M : Type uM} {Tr : Type uTr}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

def repairEntranceCanonicalRawMapCost
    (nInput nSolve j q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (hSolve : j+2+(q+2) ≤ nSolve) (hInput : nSolve+2+(q+2) ≤ nInput)
    (reserve Bnd Mg Kcut : ℝ) (hreserve : 0 < reserve)
    (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (T Tinv Tobs : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) : ℝ :=
  Classical.choose (repairEntranceCanonical_increment_original_norms.{uM,uTr,uP,uLabel,uPrimary,uSecondary}
    (m := m) (d := d) (N := N) (Tr := Tr)
    nInput nSolve j q Rsub Lprimary Rsecondary hq hSolve hInput
    reserve Bnd Mg Kcut hreserve hBnd hMg hKcut
    (parameterRound2_numericProfilePrefix (nSolve+1) T)
    (parameterRound2_numericProfilePrefix (nSolve+1) Tinv)
    (parameterRound2_numericProfilePrefix (j+2) Tobs)
    (parameterRound2_numericProfilePrefix_nonneg (nSolve+1) T hT)
    (parameterRound2_numericProfilePrefix_nonneg (nSolve+1) Tinv hTinv)
    (parameterRound2_numericProfilePrefix_nonneg (j+2) Tobs hTobs))

theorem repairEntranceCanonicalRawMapCost_nonneg
    (nInput nSolve j q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (hSolve : j+2+(q+2) ≤ nSolve) (hInput : nSolve+2+(q+2) ≤ nInput)
    (reserve Bnd Mg Kcut : ℝ) (hreserve : 0 < reserve)
    (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (T Tinv Tobs : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) :
    0 ≤ repairEntranceCanonicalRawMapCost.{uM,uTr,uP,uLabel,uPrimary,uSecondary}
      (m := m) (d := d) (N := N) (Tr := Tr)
    nInput nSolve j q Rsub Lprimary Rsecondary hq hSolve hInput
    reserve Bnd Mg Kcut hreserve hBnd hMg hKcut T Tinv Tobs hT hTinv hTobs :=
  (Classical.choose_spec (repairEntranceCanonical_increment_original_norms.{uM,uTr,uP,uLabel,uPrimary,uSecondary}
    (m := m) (d := d) (N := N) (Tr := Tr)
    nInput nSolve j q Rsub Lprimary Rsecondary hq hSolve hInput
    reserve Bnd Mg Kcut hreserve hBnd hMg hKcut
    (parameterRound2_numericProfilePrefix (nSolve+1) T)
    (parameterRound2_numericProfilePrefix (nSolve+1) Tinv)
    (parameterRound2_numericProfilePrefix (j+2) Tobs)
    (parameterRound2_numericProfilePrefix_nonneg (nSolve+1) T hT)
    (parameterRound2_numericProfilePrefix_nonneg (nSolve+1) Tinv hTinv)
    (parameterRound2_numericProfilePrefix_nonneg (j+2) Tobs hTobs))).1

theorem repairEntranceCanonicalRawMapCost_bound
    (nInput nSolve j q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (hSolve : j+2+(q+2) ≤ nSolve) (hInput : nSolve+2+(q+2) ≤ nInput)
    (reserve Bnd Mg Kcut : ℝ) (hreserve : 0 < reserve)
    (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (T Tinv Tobs : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) :
    let C := repairEntranceCanonicalRawMapCost.{uM,uTr,uP,uLabel,uPrimary,uSecondary}
      (m := m) (d := d) (N := N) (Tr := Tr)
      nInput nSolve j q Rsub Lprimary Rsecondary hq hSolve hInput
      reserve Bnd Mg Kcut hreserve hBnd hMg hKcut T Tinv Tobs hT hTinv hTobs
    ∀ (M : Type uM) [TopologicalSpace M] [ChartedSpace D M]
      [IsManifold 𝓙 ∞ M] [BoundarylessManifold 𝓙 M],
    ∀ (P : Type uP) (Label : Type uLabel) (SubPrimary : Type uPrimary) (SubSecondary : Type uSecondary)
      [TopologicalSpace P] [Fintype Label] [DecidableEq Label]
      [Fintype SubPrimary] [Fintype SubSecondary], ∀ (c : ℕ)
      (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
      (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
      (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Label) (Β := SubPrimary) F)
      (hg : ∀ ν β, Round3ParameterChartPreserves (g.chart ν β))
      (input inputbar : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (W : Set (P × M)) (primary : Label → Set (P × M))
      (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ))
      (ell delta tau Delta : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
      (hdelta : 0 ≤ delta) (hdeltatau : delta ≤ tau)
      (choice : ActualSecondarySignedRecord Label → SubSecondary → Round3ParameterSecondaryChoice P M m)
      (hc : ∀ r a, Round3ParameterChartPreserves (choice r a).chart)
      (data : Round3ParameterRawAtlasData (Tr := Tr) A B F hF g input inputbar
        nInput nSolve j q Rsub Lprimary Rsecondary reserve Bnd Mg Kcut T Tinv Tobs
        W primary S ell delta tau Delta choice),
    let U := round3ParameterIncrementMap F hF g input (q+2) tau delta choice
    let coordinates := incrementsOriginalMapCoordinates A B U
    (∀ i, ∃ G : Set (Fin (m+1+d) → ℝ), IsOpen G ∧ S i ⊆ G ∧
      G ⊆ incrementsOriginalDifferentiation A B i ∧ ContDiffOn ℝ ∞ (coordinates i) G) ∧
    (paperAtlasWeighted 0 (j+1) tau coordinates (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
      (paperAtlasWeighted 0 (j+1) tau coordinates (incrementsOriginalDifferentiation A B) S).toReal ≤ C*delta*tau) ∧
    (paperAtlasWeighted 1 j tau coordinates (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
      (paperAtlasWeighted 1 j tau coordinates (incrementsOriginalDifferentiation A B) S).toReal ≤ C*delta) := by
  intro C M _ _ _ _ P Label SubPrimary SubSecondary _ _ _ _ _ c A B F hF g hg input inputbar W primary S
    ell delta tau Delta htau htaul hell1 hdelta hdeltatau choice hc data U coordinates
  let data' := round4ParameterRawAtlasDataPrefix A B F hF g input inputbar
    nInput nSolve j q Rsub Lprimary Rsecondary (by omega)
    reserve Bnd Mg Kcut T Tinv Tobs W primary S ell delta tau Delta choice data
  exact (Classical.choose_spec (repairEntranceCanonical_increment_original_norms.{uM,uTr,uP,uLabel,uPrimary,uSecondary}
    (m := m) (d := d) (N := N) (Tr := Tr)
    nInput nSolve j q Rsub Lprimary Rsecondary hq hSolve hInput
    reserve Bnd Mg Kcut hreserve hBnd hMg hKcut
    (parameterRound2_numericProfilePrefix (nSolve+1) T)
    (parameterRound2_numericProfilePrefix (nSolve+1) Tinv)
    (parameterRound2_numericProfilePrefix (j+2) Tobs)
    (parameterRound2_numericProfilePrefix_nonneg (nSolve+1) T hT)
    (parameterRound2_numericProfilePrefix_nonneg (nSolve+1) Tinv hTinv)
    (parameterRound2_numericProfilePrefix_nonneg (j+2) Tobs hTobs))).2
    M P Label SubPrimary SubSecondary c A B F hF g hg input inputbar W primary S
    ell delta tau Delta htau htaul hell1 hdelta hdeltatau choice hc data'

theorem repairEntranceCanonicalRawMapCost_prefix_congr
    (nInput nSolve j q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (hSolve : j+2+(q+2) ≤ nSolve) (hInput : nSolve+2+(q+2) ≤ nInput)
    (reserve Bnd Mg Kcut : ℝ) (hreserve : 0 < reserve)
    (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (T Tinv Tobs : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k)
    (T' Tinv' Tobs' : ℕ → ℝ)
    (hT' : ∀ k, 0 ≤ T' k) (hTinv' : ∀ k, 0 ≤ Tinv' k) (hTobs' : ∀ k, 0 ≤ Tobs' k)
    (hTeq : ∀ k, k ≤ nSolve+1 → T k = T' k)
    (hTinveq : ∀ k, k ≤ nSolve+1 → Tinv k = Tinv' k)
    (hTobseq : ∀ k, k ≤ j+2 → Tobs k = Tobs' k) :
    repairEntranceCanonicalRawMapCost.{uM,uTr,uP,uLabel,uPrimary,uSecondary}
      (m := m) (d := d) (N := N) (Tr := Tr)
    nInput nSolve j q Rsub Lprimary Rsecondary hq hSolve hInput
    reserve Bnd Mg Kcut hreserve hBnd hMg hKcut T Tinv Tobs hT hTinv hTobs =
    repairEntranceCanonicalRawMapCost.{uM,uTr,uP,uLabel,uPrimary,uSecondary}
      (m := m) (d := d) (N := N) (Tr := Tr)
    nInput nSolve j q Rsub Lprimary Rsecondary hq hSolve hInput
    reserve Bnd Mg Kcut hreserve hBnd hMg hKcut T' Tinv' Tobs' hT' hTinv' hTobs' := by
  have ht := parameterRound2_numericProfilePrefix_congr (nSolve+1) T T' hTeq
  have hi := parameterRound2_numericProfilePrefix_congr (nSolve+1) Tinv Tinv' hTinveq
  have ho := parameterRound2_numericProfilePrefix_congr (j+2) Tobs Tobs' hTobseq
  unfold repairEntranceCanonicalRawMapCost
  congr 1
  rw [ht,hi,ho]

def repairEntranceCanonicalRawMetricCost
    (nInput nSolve j q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (hSolve : j+2+(q+2) ≤ nSolve) (hInput : nSolve+2+(q+2) ≤ nInput)
    (reserve Bnd Mg Kcut : ℝ) (hreserve : 0 < reserve)
    (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (T Tinv Tobs : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) : ℝ :=
  Classical.choose (repairEntranceCanonical_metric_remainder_original_norms.{uM,uTr,uP,uLabel,uPrimary,uSecondary}
    (m := m) (d := d) (N := N) (Tr := Tr)
    nInput nSolve j q Rsub Lprimary Rsecondary hq hSolve hInput
    reserve Bnd Mg Kcut hreserve hBnd hMg hKcut
    (parameterRound2_numericProfilePrefix (nSolve+1) T)
    (parameterRound2_numericProfilePrefix (nSolve+1) Tinv)
    (parameterRound2_numericProfilePrefix (j+2) Tobs)
    (parameterRound2_numericProfilePrefix_nonneg (nSolve+1) T hT)
    (parameterRound2_numericProfilePrefix_nonneg (nSolve+1) Tinv hTinv)
    (parameterRound2_numericProfilePrefix_nonneg (j+2) Tobs hTobs))

theorem repairEntranceCanonicalRawMetricCost_nonneg
    (nInput nSolve j q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (hSolve : j+2+(q+2) ≤ nSolve) (hInput : nSolve+2+(q+2) ≤ nInput)
    (reserve Bnd Mg Kcut : ℝ) (hreserve : 0 < reserve)
    (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (T Tinv Tobs : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) :
    0 ≤ repairEntranceCanonicalRawMetricCost.{uM,uTr,uP,uLabel,uPrimary,uSecondary}
      (m := m) (d := d) (N := N) (Tr := Tr)
    nInput nSolve j q Rsub Lprimary Rsecondary hq hSolve hInput
    reserve Bnd Mg Kcut hreserve hBnd hMg hKcut T Tinv Tobs hT hTinv hTobs :=
  (Classical.choose_spec (repairEntranceCanonical_metric_remainder_original_norms.{uM,uTr,uP,uLabel,uPrimary,uSecondary}
    (m := m) (d := d) (N := N) (Tr := Tr)
    nInput nSolve j q Rsub Lprimary Rsecondary hq hSolve hInput
    reserve Bnd Mg Kcut hreserve hBnd hMg hKcut
    (parameterRound2_numericProfilePrefix (nSolve+1) T)
    (parameterRound2_numericProfilePrefix (nSolve+1) Tinv)
    (parameterRound2_numericProfilePrefix (j+2) Tobs)
    (parameterRound2_numericProfilePrefix_nonneg (nSolve+1) T hT)
    (parameterRound2_numericProfilePrefix_nonneg (nSolve+1) Tinv hTinv)
    (parameterRound2_numericProfilePrefix_nonneg (j+2) Tobs hTobs))).1

theorem repairEntranceCanonicalRawMetricCost_bound
    (nInput nSolve j q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (hSolve : j+2+(q+2) ≤ nSolve) (hInput : nSolve+2+(q+2) ≤ nInput)
    (reserve Bnd Mg Kcut : ℝ) (hreserve : 0 < reserve)
    (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (T Tinv Tobs : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) :
    let C := repairEntranceCanonicalRawMetricCost.{uM,uTr,uP,uLabel,uPrimary,uSecondary}
      (m := m) (d := d) (N := N) (Tr := Tr)
      nInput nSolve j q Rsub Lprimary Rsecondary hq hSolve hInput
      reserve Bnd Mg Kcut hreserve hBnd hMg hKcut T Tinv Tobs hT hTinv hTobs
    ∀ (M : Type uM) [TopologicalSpace M] [ChartedSpace D M]
      [IsManifold 𝓙 ∞ M] [BoundarylessManifold 𝓙 M],
    ∀ (P : Type uP) (Label : Type uLabel) (SubPrimary : Type uPrimary) (SubSecondary : Type uSecondary)
      [TopologicalSpace P] [Fintype Label] [DecidableEq Label]
      [Fintype SubPrimary] [Fintype SubSecondary], ∀ (c : ℕ)
      (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep) (hA : IsSmoothBufferedAtlas A)
      (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
      (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Label) (Β := SubPrimary) F)
      (hg : ∀ ν β, Round3ParameterChartPreserves (g.chart ν β))
      (input inputbar : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (W : Set (P × M)) (primary : Label → Set (P × M))
      (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ))
      (ell delta tau Delta : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
      (hdelta : 0 ≤ delta) (hdeltatau : delta ≤ tau)
      (choice : ActualSecondarySignedRecord Label → SubSecondary → Round3ParameterSecondaryChoice P M m)
      (hc : ∀ r a, Round3ParameterChartPreserves (choice r a).chart)
      (data : Round3ParameterRawAtlasData (Tr := Tr) A B F hF g input inputbar
        nInput nSolve j q Rsub Lprimary Rsecondary reserve Bnd Mg Kcut T Tinv Tobs
        W primary S ell delta tau Delta choice),
    let U := round3ParameterIncrementMap F hF g input (q+2) tau delta choice
    let Mean := round3ParameterPrimaryMean F hF g input (q+2) tau
    let Rest := incrementsOriginalMetricError (fun y : P × M => F y.1 y.2) U Mean delta
    Rest ∈ parameterRound2_originalTensorGermSpace A B S W ∧
    paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates A B Rest)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
    (paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates A B Rest)
      (incrementsOriginalDifferentiation A B) S).toReal ≤ C*(delta*(tau/ell)^q+delta^3/tau) := by
  intro C M _ _ _ _ P Label SubPrimary SubSecondary _ _ _ _ _ c A B hA F hF g hg input inputbar W primary S
    ell delta tau Delta htau htaul hell1 hdelta hdeltatau choice hc data U Mean Rest
  let data' := round4ParameterRawAtlasDataPrefix A B F hF g input inputbar
    nInput nSolve j q Rsub Lprimary Rsecondary (by omega)
    reserve Bnd Mg Kcut T Tinv Tobs W primary S ell delta tau Delta choice data
  exact (Classical.choose_spec (repairEntranceCanonical_metric_remainder_original_norms.{uM,uTr,uP,uLabel,uPrimary,uSecondary}
    (m := m) (d := d) (N := N) (Tr := Tr)
    nInput nSolve j q Rsub Lprimary Rsecondary hq hSolve hInput
    reserve Bnd Mg Kcut hreserve hBnd hMg hKcut
    (parameterRound2_numericProfilePrefix (nSolve+1) T)
    (parameterRound2_numericProfilePrefix (nSolve+1) Tinv)
    (parameterRound2_numericProfilePrefix (j+2) Tobs)
    (parameterRound2_numericProfilePrefix_nonneg (nSolve+1) T hT)
    (parameterRound2_numericProfilePrefix_nonneg (nSolve+1) Tinv hTinv)
    (parameterRound2_numericProfilePrefix_nonneg (j+2) Tobs hTobs))).2
    M P Label SubPrimary SubSecondary c A B hA F hF g hg input inputbar W primary S
    ell delta tau Delta htau htaul hell1 hdelta hdeltatau choice hc data'

theorem repairEntranceCanonicalRawMetricCost_prefix_congr
    (nInput nSolve j q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (hSolve : j+2+(q+2) ≤ nSolve) (hInput : nSolve+2+(q+2) ≤ nInput)
    (reserve Bnd Mg Kcut : ℝ) (hreserve : 0 < reserve)
    (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (T Tinv Tobs : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k)
    (T' Tinv' Tobs' : ℕ → ℝ)
    (hT' : ∀ k, 0 ≤ T' k) (hTinv' : ∀ k, 0 ≤ Tinv' k) (hTobs' : ∀ k, 0 ≤ Tobs' k)
    (hTeq : ∀ k, k ≤ nSolve+1 → T k = T' k)
    (hTinveq : ∀ k, k ≤ nSolve+1 → Tinv k = Tinv' k)
    (hTobseq : ∀ k, k ≤ j+2 → Tobs k = Tobs' k) :
    repairEntranceCanonicalRawMetricCost.{uM,uTr,uP,uLabel,uPrimary,uSecondary}
      (m := m) (d := d) (N := N) (Tr := Tr)
    nInput nSolve j q Rsub Lprimary Rsecondary hq hSolve hInput
    reserve Bnd Mg Kcut hreserve hBnd hMg hKcut T Tinv Tobs hT hTinv hTobs =
    repairEntranceCanonicalRawMetricCost.{uM,uTr,uP,uLabel,uPrimary,uSecondary}
      (m := m) (d := d) (N := N) (Tr := Tr)
    nInput nSolve j q Rsub Lprimary Rsecondary hq hSolve hInput
    reserve Bnd Mg Kcut hreserve hBnd hMg hKcut T' Tinv' Tobs' hT' hTinv' hTobs' := by
  have ht := parameterRound2_numericProfilePrefix_congr (nSolve+1) T T' hTeq
  have hi := parameterRound2_numericProfilePrefix_congr (nSolve+1) Tinv Tinv' hTinveq
  have ho := parameterRound2_numericProfilePrefix_congr (j+2) Tobs Tobs' hTobseq
  unfold repairEntranceCanonicalRawMetricCost
  congr 1
  rw [ht,hi,ho]

#print axioms repairEntranceCanonicalRawMapCost_bound
#print axioms repairEntranceCanonicalRawMapCost_prefix_congr
#print axioms repairEntranceCanonicalRawMetricCost_bound
#print axioms repairEntranceCanonicalRawMetricCost_prefix_congr
end GlobalEmbedding.Continuation
