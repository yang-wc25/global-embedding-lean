import Probes.Round3ParameterPrimaryGlobalNaturality
import Probes.Round4PrescribedNativeMeanParity
import Probes.Round4PrescribedGlobalWave

/-!
# The same complete prescribed wave on the original parameter space

The physical parameter space is only topological. The finite source solver
and reconstruction differentiate the spatial variable alone. A genuine
parameter chart therefore conjugates the original extension exactly on its
target, without extending that target or choosing a new output wave.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Manifold
open scoped ContDiff BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {E H M P Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [TopologicalSpace P] [TopologicalSpace Q]
  {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The original chart extension of both reconstructed channels, with no
linear or normed-space structure imposed on the physical parameter. -/
def actualParameterPrescribedGlobalAmplitude
    (imag : Bool) (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : P → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : P → D → M) (vf : (b : P) → (x : D) → normalSpace (I := I) (F b) (c b x))
    (tau : ℝ) (length : ℕ) (a : OpenPartialHomeomorph (P × M) (P × D))
    (u : Fin p → ℝ) (z : P × M) : V :=
  if z ∈ a.source then
    round4PrescribedAmplitude imag label l (F (a z).1) (hF (a z).1)
      (c (a z).1) (vf (a z).1) tau length u (a z).2 else 0

def actualParameterPrescribedGlobalWave
    (label : (Fin r × Bool) ↪ Fin p)
    (F : P → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → P → D → M)
    (vf : (l : Fin r) → (b : P) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (phase : Fin r → P × M → ℝ) (tau : ℝ) (length : ℕ)
    (a : Fin r → OpenPartialHomeomorph (P × M) (P × D))
    (u : Fin p → ℝ) (z : P × M) : V :=
  ∑ l, (Real.cos (phase l z/tau) •
    actualParameterPrescribedGlobalAmplitude false label l F hF (c l) (vf l) tau length (a l) u z -
    Real.sin (phase l z/tau) •
    actualParameterPrescribedGlobalAmplitude true label l F hF (c l) (vf l) tau length (a l) u z)

theorem actualParameterPrescribedGlobalAmplitude_pullback
    (imag : Bool) (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : P → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : P → D → M) (vf : (b : P) → (x : D) → normalSpace (I := I) (F b) (c b x))
    (tau : ℝ) (length : ℕ) (a : OpenPartialHomeomorph (P × M) (P × D))
    (ha : Round3ParameterChartPreserves a) (B : OpenPartialHomeomorph P Q)
    (u : Fin p → ℝ) (b : Q) (hb : b ∈ B.target) (x : M) :
    actualParameterPrescribedGlobalAmplitude imag label l
      (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      (fun t => c (B.symm t)) (fun t => vf (B.symm t)) tau length
      (round3ParameterChartPullback B a) u (b,x) =
    actualParameterPrescribedGlobalAmplitude imag label l F hF c vf tau length a u (B.symm b,x) := by
  have hi := round3ParameterChartPullback_source_iff B a ha (b,x) hb
  by_cases hx : (B.symm b,x) ∈ a.source
  · have hnew := hi.mpr hx
    have hparam : B.symm (B (a (B.symm b,x)).1) = (a (B.symm b,x)).1 :=
      B.left_inv (by rw [ha _ hx]; exact B.map_target hb)
    simp only [actualParameterPrescribedGlobalAmplitude,hnew,hx,ite_true,
      round3ParameterChartPullback_apply]
    exact congrArg (fun t => round4PrescribedAmplitude imag label l (F t) (hF t)
      (c t) (vf t) tau length u (a (B.symm b,x)).2) hparam
  · have hnew := mt hi.mp hx
    simp only [actualParameterPrescribedGlobalAmplitude,hnew,hx,ite_false]

theorem actualParameterPrescribedGlobalWave_pullback
    (label : (Fin r × Bool) ↪ Fin p)
    (F : P → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → P → D → M)
    (vf : (l : Fin r) → (b : P) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (phase : Fin r → P × M → ℝ) (tau : ℝ) (length : ℕ)
    (a : Fin r → OpenPartialHomeomorph (P × M) (P × D))
    (ha : ∀ l, Round3ParameterChartPreserves (a l)) (B : OpenPartialHomeomorph P Q)
    (u : Fin p → ℝ) (b : Q) (hb : b ∈ B.target) (x : M) :
    actualParameterPrescribedGlobalWave label
      (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      (fun l t => c l (B.symm t)) (fun l t => vf l (B.symm t))
      (fun l z => phase l (B.symm z.1,z.2)) tau length
      (fun l => round3ParameterChartPullback B (a l)) u (b,x) =
    actualParameterPrescribedGlobalWave label F hF c vf phase tau length a u (B.symm b,x) := by
  unfold actualParameterPrescribedGlobalWave
  apply Finset.sum_congr rfl
  intro l _
  rw [actualParameterPrescribedGlobalAmplitude_pullback false label l F hF (c l) (vf l)
    tau length (a l) (ha l) B u b hb,
    actualParameterPrescribedGlobalAmplitude_pullback true label l F hF (c l) (vf l)
    tau length (a l) (ha l) B u b hb]

section Native
variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]

/-- The physical formula specializes definitionally to the existing actual
native amplitude, including its finite reconstruction and original extension. -/
theorem actualParameterPrescribedGlobalAmplitude_native
    (imag : Bool) (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Ep → D → M) (vf : (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c b x))
    (tau : ℝ) (length : ℕ) (a : OpenPartialHomeomorph (Ep × M) (Ep × D)) :
    actualParameterPrescribedGlobalAmplitude imag label l F hF c vf tau length a =
      round4PrescribedGlobalAmplitude imag label l F hF c vf tau length a := rfl

theorem actualParameterPrescribedGlobalWave_native
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (tau : ℝ) (length : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) (Ep × D)) :
    actualParameterPrescribedGlobalWave label F hF c vf phase tau length a =
      round4PrescribedGlobalWave label F hF c vf phase tau length a := rfl

/-- Each admitted parameter chart sees the same physical prescribed wave. -/
theorem actualParameterPrescribedGlobalWave_native_pullback
    (label : (Fin r × Bool) ↪ Fin p)
    (F : P → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → P → D → M)
    (vf : (l : Fin r) → (b : P) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (phase : Fin r → P × M → ℝ) (tau : ℝ) (length : ℕ)
    (a : Fin r → OpenPartialHomeomorph (P × M) (P × D))
    (ha : ∀ l, Round3ParameterChartPreserves (a l)) (B : OpenPartialHomeomorph P Ep)
    (u : Fin p → ℝ) (b : Ep) (hb : b ∈ B.target) (x : M) :
    round4PrescribedGlobalWave label
      (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      (fun l t => c l (B.symm t)) (fun l t => vf l (B.symm t))
      (fun l z => phase l (B.symm z.1,z.2)) tau length
      (fun l => round3ParameterChartPullback B (a l)) u (b,x) =
    actualParameterPrescribedGlobalWave label F hF c vf phase tau length a u (B.symm b,x) :=
  actualParameterPrescribedGlobalWave_pullback label F hF c vf phase tau length a ha B u b hb x

end Native
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualParameterPrescribedGlobalAmplitude_pullback
#print axioms GlobalEmbedding.Continuation.actualParameterPrescribedGlobalWave_native_pullback
