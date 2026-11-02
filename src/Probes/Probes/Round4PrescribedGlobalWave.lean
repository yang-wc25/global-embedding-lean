import Probes.Round4PrescribedGlobalParameterSmooth
import Probes.ActualEuclideanProbeHigherBounds

/-!
# The actual globally supported complete sine/cosine first block

Every mode is the original chart extension of its complete free-plus-homogeneous
reconstruction. The finite parameter response is proved for this literal global
field, even at chart boundaries. All parameter derivatives are genuine native
Fréchet derivatives; no leading-only surrogate is introduced.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff BigOperators
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Pspace" => Fin p → ℝ

def round4PrescribedGlobalWave
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (tau : ℝ) (length : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X) (u : Pspace) (z : Ep × M) : V :=
  ∑ l, (Real.cos (phase l z/tau) •
      round4PrescribedGlobalAmplitude false label l F hF (c l) (vf l) tau length (a l) u z-
    Real.sin (phase l z/tau) •
      round4PrescribedGlobalAmplitude true label l F hF (c l) (vf l) tau length (a l) u z)


theorem round4PrescribedGlobalWave_columns
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (tau : ℝ) (length : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (hA : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hB : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hBR : ∀ l, ContDiffOn ℝ ∞ (fun z : X => fun k : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c l z.1) z.2 0 k : V)) (a l).target)
    (hvf : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (vf l z.1 z.2 : V)) (a l).target)
    (u : Pspace) (z : Ep × M) :
    round4PrescribedGlobalWave label F hF c vf phase tau length a u z =
      ∑ q, u q • round4PrescribedGlobalWave label F hF c vf phase tau length a (Pi.single q 1) z := by
  classical
  let R := fun l u => round4PrescribedGlobalAmplitude false label l F hF (c l) (vf l) tau length (a l) u z
  let Q := fun l u => round4PrescribedGlobalAmplitude true label l F hF (c l) (vf l) tau length (a l) u z
  have hR l : R l u = ∑ q, u q • R l (Pi.single q 1) :=
    congrFun (round4PrescribedGlobalAmplitude_columns false label l F hF (c l) (vf l) tau length (a l)
      (hA l) (hB l) (hBR l) (hvf l) u) z
  have hQ l : Q l u = ∑ q, u q • Q l (Pi.single q 1) :=
    congrFun (round4PrescribedGlobalAmplitude_columns true label l F hF (c l) (vf l) tau length (a l)
      (hA l) (hB l) (hBR l) (hvf l) u) z
  change (∑ l, (Real.cos (phase l z/tau) • R l u-Real.sin (phase l z/tau) • Q l u)) =
    ∑ q, u q • ∑ l, (Real.cos (phase l z/tau) • R l (Pi.single q 1)-
      Real.sin (phase l z/tau) • Q l (Pi.single q 1))
  calc
    _ = ∑ l, ∑ q, u q • (Real.cos (phase l z/tau) • R l (Pi.single q 1)-
        Real.sin (phase l z/tau) • Q l (Pi.single q 1)) := by
      apply Finset.sum_congr rfl
      intro l _
      rw [hR,hQ,Finset.smul_sum,Finset.smul_sum,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro q _
      module
    _ = _ := by rw [Finset.sum_comm]; simp only [Finset.smul_sum]

/-- Actual global value response; exact at every point, including chart edges. -/
theorem round4PrescribedGlobalWave_hasFDerivAt
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (tau : ℝ) (length : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (hA : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hB : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hBR : ∀ l, ContDiffOn ℝ ∞ (fun z : X => fun k : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c l z.1) z.2 0 k : V)) (a l).target)
    (hvf : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (vf l z.1 z.2 : V)) (a l).target)
    (u : Pspace) (z : Ep × M) :
    HasFDerivAt (fun v => round4PrescribedGlobalWave label F hF c vf phase tau length a v z)
      (probeColumnMap (fun q =>
        round4PrescribedGlobalWave label F hF c vf phase tau length a (Pi.single q 1) z)) u := by
  have heq : (fun v => round4PrescribedGlobalWave label F hF c vf phase tau length a v z) =
      probeColumnMap (fun q => round4PrescribedGlobalWave label F hF c vf phase tau length a (Pi.single q 1) z) := by
    funext v
    rw [probeColumnMap_apply]
    exact round4PrescribedGlobalWave_columns label F hF c vf phase tau length a hA hB hBR hvf v z
  rw [heq]
  exact (probeColumnMap _).hasFDerivAt

/-- Every actual global parameter column is returned by the native derivative. -/
theorem round4PrescribedGlobalWave_response_column
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (tau : ℝ) (length : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (hA : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hB : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hBR : ∀ l, ContDiffOn ℝ ∞ (fun z : X => fun k : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c l z.1) z.2 0 k : V)) (a l).target)
    (hvf : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (vf l z.1 z.2 : V)) (a l).target)
    (u : Pspace) (z : Ep × M) (q : Fin p) :
    fderiv ℝ (fun v => round4PrescribedGlobalWave label F hF c vf phase tau length a v z) u (Pi.single q 1) =
      round4PrescribedGlobalWave label F hF c vf phase tau length a (Pi.single q 1) z := by
  rw [(round4PrescribedGlobalWave_hasFDerivAt label F hF c vf phase tau length a hA hB hBR hvf u z).fderiv,
    probeColumnMap_apply]
  simp [Pi.single_apply]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4PrescribedGlobalWave_columns
#print axioms GlobalEmbedding.Continuation.round4PrescribedGlobalWave_hasFDerivAt
#print axioms GlobalEmbedding.Continuation.round4PrescribedGlobalWave_response_column
