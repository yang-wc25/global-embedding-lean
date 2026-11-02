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

def round4ParameterRawMapCost
    (nInput nSolve j q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (hSolve : j+2+(q+2) ≤ nSolve) (hInput : nSolve+2+(q+2) ≤ nInput)
    (reserve Bnd Mg Kcut : ℝ) (hreserve : 0 < reserve)
    (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (T Tinv Tobs : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) : ℝ :=
  Classical.choose (round3Parameter_actual_increment_original_norms_uniform.{uM,uTr,uP,uLabel,uPrimary,uSecondary}
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    nInput nSolve j q Rsub Lprimary Rsecondary hq hSolve hInput
    reserve Bnd Mg Kcut hreserve hBnd hMg hKcut
    (parameterRound2_numericProfilePrefix (nSolve+1) T)
    (parameterRound2_numericProfilePrefix (nSolve+1) Tinv)
    (parameterRound2_numericProfilePrefix (j+2) Tobs)
    (parameterRound2_numericProfilePrefix_nonneg (nSolve+1) T hT)
    (parameterRound2_numericProfilePrefix_nonneg (nSolve+1) Tinv hTinv)
    (parameterRound2_numericProfilePrefix_nonneg (j+2) Tobs hTobs))

theorem round4ParameterRawMapCost_nonneg
    (nInput nSolve j q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (hSolve : j+2+(q+2) ≤ nSolve) (hInput : nSolve+2+(q+2) ≤ nInput)
    (reserve Bnd Mg Kcut : ℝ) (hreserve : 0 < reserve)
    (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (T Tinv Tobs : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) :
    0 ≤ round4ParameterRawMapCost.{uM,uTr,uP,uLabel,uPrimary,uSecondary}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    nInput nSolve j q Rsub Lprimary Rsecondary hq hSolve hInput
    reserve Bnd Mg Kcut hreserve hBnd hMg hKcut T Tinv Tobs hT hTinv hTobs :=
  (Classical.choose_spec (round3Parameter_actual_increment_original_norms_uniform.{uM,uTr,uP,uLabel,uPrimary,uSecondary}
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    nInput nSolve j q Rsub Lprimary Rsecondary hq hSolve hInput
    reserve Bnd Mg Kcut hreserve hBnd hMg hKcut
    (parameterRound2_numericProfilePrefix (nSolve+1) T)
    (parameterRound2_numericProfilePrefix (nSolve+1) Tinv)
    (parameterRound2_numericProfilePrefix (j+2) Tobs)
    (parameterRound2_numericProfilePrefix_nonneg (nSolve+1) T hT)
    (parameterRound2_numericProfilePrefix_nonneg (nSolve+1) Tinv hTinv)
    (parameterRound2_numericProfilePrefix_nonneg (j+2) Tobs hTobs))).1

theorem round4ParameterRawMapCost_bound
    (nInput nSolve j q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (hSolve : j+2+(q+2) ≤ nSolve) (hInput : nSolve+2+(q+2) ≤ nInput)
    (reserve Bnd Mg Kcut : ℝ) (hreserve : 0 < reserve)
    (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (T Tinv Tobs : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) :
    let C := round4ParameterRawMapCost.{uM,uTr,uP,uLabel,uPrimary,uSecondary}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      nInput nSolve j q Rsub Lprimary Rsecondary hq hSolve hInput
      reserve Bnd Mg Kcut hreserve hBnd hMg hKcut T Tinv Tobs hT hTinv hTobs
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
  intro C P Label SubPrimary SubSecondary _ _ _ _ _ c A B F hF g hg input inputbar W primary S
    ell delta tau Delta htau htaul hell1 hdelta hdeltatau choice hc data U coordinates
  let data' := round4ParameterRawAtlasDataPrefix A B F hF g input inputbar
    nInput nSolve j q Rsub Lprimary Rsecondary (by omega)
    reserve Bnd Mg Kcut T Tinv Tobs W primary S ell delta tau Delta choice data
  exact (Classical.choose_spec (round3Parameter_actual_increment_original_norms_uniform.{uM,uTr,uP,uLabel,uPrimary,uSecondary}
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    nInput nSolve j q Rsub Lprimary Rsecondary hq hSolve hInput
    reserve Bnd Mg Kcut hreserve hBnd hMg hKcut
    (parameterRound2_numericProfilePrefix (nSolve+1) T)
    (parameterRound2_numericProfilePrefix (nSolve+1) Tinv)
    (parameterRound2_numericProfilePrefix (j+2) Tobs)
    (parameterRound2_numericProfilePrefix_nonneg (nSolve+1) T hT)
    (parameterRound2_numericProfilePrefix_nonneg (nSolve+1) Tinv hTinv)
    (parameterRound2_numericProfilePrefix_nonneg (j+2) Tobs hTobs))).2
    P Label SubPrimary SubSecondary c A B F hF g hg input inputbar W primary S
    ell delta tau Delta htau htaul hell1 hdelta hdeltatau choice hc data'

theorem round4ParameterRawMapCost_prefix_congr
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
    round4ParameterRawMapCost.{uM,uTr,uP,uLabel,uPrimary,uSecondary}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    nInput nSolve j q Rsub Lprimary Rsecondary hq hSolve hInput
    reserve Bnd Mg Kcut hreserve hBnd hMg hKcut T Tinv Tobs hT hTinv hTobs =
    round4ParameterRawMapCost.{uM,uTr,uP,uLabel,uPrimary,uSecondary}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    nInput nSolve j q Rsub Lprimary Rsecondary hq hSolve hInput
    reserve Bnd Mg Kcut hreserve hBnd hMg hKcut T' Tinv' Tobs' hT' hTinv' hTobs' := by
  have ht := parameterRound2_numericProfilePrefix_congr (nSolve+1) T T' hTeq
  have hi := parameterRound2_numericProfilePrefix_congr (nSolve+1) Tinv Tinv' hTinveq
  have ho := parameterRound2_numericProfilePrefix_congr (j+2) Tobs Tobs' hTobseq
  unfold round4ParameterRawMapCost
  congr 1
  rw [ht,hi,ho]

def round4ParameterRawMetricCost
    (nInput nSolve j q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (hSolve : j+2+(q+2) ≤ nSolve) (hInput : nSolve+2+(q+2) ≤ nInput)
    (reserve Bnd Mg Kcut : ℝ) (hreserve : 0 < reserve)
    (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (T Tinv Tobs : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) : ℝ :=
  Classical.choose (round3Parameter_actual_metric_remainder_original_norm_uniform.{uM,uTr,uP,uLabel,uPrimary,uSecondary}
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    nInput nSolve j q Rsub Lprimary Rsecondary hq hSolve hInput
    reserve Bnd Mg Kcut hreserve hBnd hMg hKcut
    (parameterRound2_numericProfilePrefix (nSolve+1) T)
    (parameterRound2_numericProfilePrefix (nSolve+1) Tinv)
    (parameterRound2_numericProfilePrefix (j+2) Tobs)
    (parameterRound2_numericProfilePrefix_nonneg (nSolve+1) T hT)
    (parameterRound2_numericProfilePrefix_nonneg (nSolve+1) Tinv hTinv)
    (parameterRound2_numericProfilePrefix_nonneg (j+2) Tobs hTobs))

theorem round4ParameterRawMetricCost_nonneg
    (nInput nSolve j q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (hSolve : j+2+(q+2) ≤ nSolve) (hInput : nSolve+2+(q+2) ≤ nInput)
    (reserve Bnd Mg Kcut : ℝ) (hreserve : 0 < reserve)
    (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (T Tinv Tobs : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) :
    0 ≤ round4ParameterRawMetricCost.{uM,uTr,uP,uLabel,uPrimary,uSecondary}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    nInput nSolve j q Rsub Lprimary Rsecondary hq hSolve hInput
    reserve Bnd Mg Kcut hreserve hBnd hMg hKcut T Tinv Tobs hT hTinv hTobs :=
  (Classical.choose_spec (round3Parameter_actual_metric_remainder_original_norm_uniform.{uM,uTr,uP,uLabel,uPrimary,uSecondary}
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    nInput nSolve j q Rsub Lprimary Rsecondary hq hSolve hInput
    reserve Bnd Mg Kcut hreserve hBnd hMg hKcut
    (parameterRound2_numericProfilePrefix (nSolve+1) T)
    (parameterRound2_numericProfilePrefix (nSolve+1) Tinv)
    (parameterRound2_numericProfilePrefix (j+2) Tobs)
    (parameterRound2_numericProfilePrefix_nonneg (nSolve+1) T hT)
    (parameterRound2_numericProfilePrefix_nonneg (nSolve+1) Tinv hTinv)
    (parameterRound2_numericProfilePrefix_nonneg (j+2) Tobs hTobs))).1

theorem round4ParameterRawMetricCost_bound
    (nInput nSolve j q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (hSolve : j+2+(q+2) ≤ nSolve) (hInput : nSolve+2+(q+2) ≤ nInput)
    (reserve Bnd Mg Kcut : ℝ) (hreserve : 0 < reserve)
    (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (T Tinv Tobs : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) :
    let C := round4ParameterRawMetricCost.{uM,uTr,uP,uLabel,uPrimary,uSecondary}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      nInput nSolve j q Rsub Lprimary Rsecondary hq hSolve hInput
      reserve Bnd Mg Kcut hreserve hBnd hMg hKcut T Tinv Tobs hT hTinv hTobs
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
  intro C P Label SubPrimary SubSecondary _ _ _ _ _ c A B hA F hF g hg input inputbar W primary S
    ell delta tau Delta htau htaul hell1 hdelta hdeltatau choice hc data U Mean Rest
  let data' := round4ParameterRawAtlasDataPrefix A B F hF g input inputbar
    nInput nSolve j q Rsub Lprimary Rsecondary (by omega)
    reserve Bnd Mg Kcut T Tinv Tobs W primary S ell delta tau Delta choice data
  exact (Classical.choose_spec (round3Parameter_actual_metric_remainder_original_norm_uniform.{uM,uTr,uP,uLabel,uPrimary,uSecondary}
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    nInput nSolve j q Rsub Lprimary Rsecondary hq hSolve hInput
    reserve Bnd Mg Kcut hreserve hBnd hMg hKcut
    (parameterRound2_numericProfilePrefix (nSolve+1) T)
    (parameterRound2_numericProfilePrefix (nSolve+1) Tinv)
    (parameterRound2_numericProfilePrefix (j+2) Tobs)
    (parameterRound2_numericProfilePrefix_nonneg (nSolve+1) T hT)
    (parameterRound2_numericProfilePrefix_nonneg (nSolve+1) Tinv hTinv)
    (parameterRound2_numericProfilePrefix_nonneg (j+2) Tobs hTobs))).2
    P Label SubPrimary SubSecondary c A B hA F hF g hg input inputbar W primary S
    ell delta tau Delta htau htaul hell1 hdelta hdeltatau choice hc data'

theorem round4ParameterRawMetricCost_prefix_congr
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
    round4ParameterRawMetricCost.{uM,uTr,uP,uLabel,uPrimary,uSecondary}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    nInput nSolve j q Rsub Lprimary Rsecondary hq hSolve hInput
    reserve Bnd Mg Kcut hreserve hBnd hMg hKcut T Tinv Tobs hT hTinv hTobs =
    round4ParameterRawMetricCost.{uM,uTr,uP,uLabel,uPrimary,uSecondary}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    nInput nSolve j q Rsub Lprimary Rsecondary hq hSolve hInput
    reserve Bnd Mg Kcut hreserve hBnd hMg hKcut T' Tinv' Tobs' hT' hTinv' hTobs' := by
  have ht := parameterRound2_numericProfilePrefix_congr (nSolve+1) T T' hTeq
  have hi := parameterRound2_numericProfilePrefix_congr (nSolve+1) Tinv Tinv' hTinveq
  have ho := parameterRound2_numericProfilePrefix_congr (j+2) Tobs Tobs' hTobseq
  unfold round4ParameterRawMetricCost
  congr 1
  rw [ht,hi,ho]

#print axioms round4ParameterRawMapCost_bound
#print axioms round4ParameterRawMapCost_prefix_congr
#print axioms round4ParameterRawMetricCost_bound
#print axioms round4ParameterRawMetricCost_prefix_congr
end GlobalEmbedding.Continuation
