import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Actual real Gram source coefficients on a uniform original base neighborhood

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 522–534. The source formula uses ordinary transpose, not complex conjugation.
-/

open Set Filter Matrix
open scoped Topology

namespace GlobalEmbedding.Paper

/-- Actual periodic real analytic T and Gram nondegeneracy only over one base fiber construct
one open original base neighborhood on which the actual Gram right-inverse source coefficient
is analytic, integer-periodic and a genuine right inverse.

Source: Proposition `prop:collar`, proof lines 522–534. At each point over the base point,
continuity of the actual Gram determinant gives an open nonzero neighborhood. The fundamental
cube is compact, hence one common base neighborhood works for every fractional orbit point.
Actual integer periodicity reduces every real orbit point to that cube. Shrink inside the given
source open set. For a point over this neighborhood, actual analytic entries make the bilinear
Gram entries, determinant and adjugate entries analytic finite polynomials. Reciprocal nonzero
determinant gives the actual inverse and its ordinary-transpose product. Finite coordinate
flattening gives the precise real matrix coefficient, and associativity with the genuine
nonsingular inverse gives T C=1. No complex extension, C analyticity, nearby nondegeneracy or
uniform base neighborhood is an input. Empty row/column and base/orbit dimensions are included. -/
theorem collar_real_gram_source_coefficients {b a M N : ℕ}
    (T : (Fin (b + a) → ℝ) → Matrix (Fin M) (Fin N) ℝ)
    (V : Set (Fin b → ℝ)) (hV : IsOpen V) (p₀ : Fin b → ℝ) (hp₀ : p₀ ∈ V)
    (hT : ∀ x : Fin (b + a) → ℝ, (fun i : Fin b ↦ x (Fin.castAdd a i)) ∈ V →
      ∀ i j, AnalyticAt ℝ (fun z ↦ T z i j) x)
    (hperiodT : ∀ x : Fin (b + a) → ℝ, (fun i : Fin b ↦ x (Fin.castAdd a i)) ∈ V →
      ∀ t : Fin a → ℤ,
        T (x + Fin.append (fun _ : Fin b ↦ (0 : ℝ)) (fun j ↦ (t j : ℝ))) = T x)
    (hbase : ∀ y : Fin a → ℝ,
      (T (Fin.append p₀ y) * (T (Fin.append p₀ y))ᵀ).det ≠ 0) :
    let C := fun x ↦ (T x)ᵀ * (T x * (T x)ᵀ)⁻¹
    let fA := fun x (q : Fin (N * M)) ↦
      C x (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2
    ∃ W : Set (Fin b → ℝ), IsOpen W ∧ p₀ ∈ W ∧ W ⊆ V ∧
      ∀ x : Fin (b + a) → ℝ, (fun i : Fin b ↦ x (Fin.castAdd a i)) ∈ W →
        (T x * (T x)ᵀ).det ≠ 0 ∧ T x * C x = 1 ∧ AnalyticAt ℝ fA x ∧
        ∀ t : Fin a → ℤ,
          fA (x + Fin.append (fun _ : Fin b ↦ (0 : ℝ)) (fun j ↦ (t j : ℝ))) = fA x := by
  classical
  dsimp only
  let append : ((Fin b → ℝ) × (Fin a → ℝ)) → (Fin (b + a) → ℝ) :=
    fun z ↦ Fin.append z.1 z.2
  have happend : Continuous append := by
    apply continuous_pi
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [append, Fin.append_left, Function.comp_def] using
        (continuous_apply j).comp continuous_fst
    · intro j
      simpa only [append, Fin.append_right, Function.comp_def] using
        (continuous_apply j).comp continuous_snd
  have hnearK : ∀ᶠ p : Fin b → ℝ in 𝓝 p₀,
      ∀ y ∈ Icc (0 : Fin a → ℝ) 1,
        (T (Fin.append p y) * (T (Fin.append p y))ᵀ).det ≠ 0 := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro y _
    have hentry : ∀ i j, ContinuousAt (fun z ↦ T (append z) i j) (p₀, y) := by
      intro i j
      have ha := hT (Fin.append p₀ y) (by simpa only [Fin.append_left] using hp₀) i j
      exact ha.continuousAt.comp' (f := append) (x := (p₀, y)) happend.continuousAt
    have hc : ContinuousAt (fun z ↦ T (append z)) (p₀, y) :=
      continuousAt_pi.mpr (fun i ↦ continuousAt_pi.mpr (hentry i))
    have hD : Continuous (fun A : Matrix (Fin M) (Fin N) ℝ ↦ (A * Aᵀ).det) :=
      (continuous_id.matrix_mul continuous_id.matrix_transpose).matrix_det
    exact (hD.continuousAt.comp' hc).eventually_ne (hbase y)
  have hnear : ∀ᶠ p : Fin b → ℝ in 𝓝 p₀, p ∈ V ∧
      ∀ y : Fin a → ℝ, (T (Fin.append p y) * (T (Fin.append p y))ᵀ).det ≠ 0 := by
    filter_upwards [hV.mem_nhds hp₀, hnearK] with p hp hK
    refine ⟨hp, ?_⟩
    intro y
    let x : Fin a → ℝ := fun i ↦ Int.fract (y i)
    let t : Fin a → ℤ := fun i ↦ ⌊y i⌋
    have hx : x ∈ Icc (0 : Fin a → ℝ) 1 :=
      ⟨fun _ ↦ Int.fract_nonneg _, fun _ ↦ (Int.fract_lt_one _).le⟩
    have he : Fin.append p x +
        Fin.append (fun _ : Fin b ↦ (0 : ℝ)) (fun j ↦ (t j : ℝ)) = Fin.append p y := by
      ext i
      refine Fin.addCases ?_ ?_ i <;> intro j
      · simp only [Pi.add_apply, Fin.append_left, add_zero]
      · simpa only [Pi.add_apply, Fin.append_right, x, t] using Int.fract_add_floor (y j)
    have hperiod := hperiodT (Fin.append p x)
      (by simpa only [Fin.append_left] using hp) t
    rw [he] at hperiod
    simpa only [hperiod] using hK x hx
  obtain ⟨W, hW, hWo, hpW⟩ := eventually_nhds_iff.mp hnear
  refine ⟨W, hWo, hpW, fun p hp ↦ (hW p hp).1, ?_⟩
  intro x hx
  let p : Fin b → ℝ := fun i ↦ x (Fin.castAdd a i)
  let y : Fin a → ℝ := fun j ↦ x (Fin.natAdd b j)
  have hxy : Fin.append p y = x := by
    ext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp only [Fin.append_left, Fin.append_right, p, y]
  have hdet : (T x * (T x)ᵀ).det ≠ 0 := by
    simpa only [hxy] using (hW p hx).2 y
  have hTx := hT x (hW p hx).1
  let B := fun z ↦ T z * (T z)ᵀ
  have hB (i j : Fin M) : AnalyticAt ℝ (fun z ↦ B z i j) x := by
    simp only [B, Matrix.mul_apply, Matrix.transpose_apply]
    apply Finset.analyticAt_fun_sum
    intro l _
    exact (hTx i l).mul (hTx j l)
  have hdetA (A : (Fin (b + a) → ℝ) → Matrix (Fin M) (Fin M) ℝ)
      (hA : ∀ i j, AnalyticAt ℝ (fun z ↦ A z i j) x) :
      AnalyticAt ℝ (fun z ↦ (A z).det) x := by
    simp only [Matrix.det_apply']
    apply Finset.analyticAt_fun_sum
    intro σ _
    apply analyticAt_const.mul
    exact Finset.univ.analyticAt_fun_prod (fun i _ ↦ hA (σ i) i)
  have hAdj (i j : Fin M) : AnalyticAt ℝ (fun z ↦ (B z).adjugate i j) x := by
    simp only [Matrix.adjugate_apply]
    apply hdetA
    intro l m
    by_cases hl : l = j
    · subst l
      simpa only [Matrix.updateRow_self] using
        (analyticAt_const (𝕜 := ℝ) (E := Fin (b + a) → ℝ)
          (v := (Pi.single i (1 : ℝ) : Fin M → ℝ) m) (x := x))
    · simpa only [Matrix.updateRow_apply, hl, ite_false] using hB l m
  have hInv (i j : Fin M) : AnalyticAt ℝ (fun z ↦ (B z)⁻¹ i j) x := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
    exact ((hdetA B hB).inv hdet).mul (hAdj i j)
  refine ⟨hdet, ?_, ?_, ?_⟩
  · rw [← Matrix.mul_assoc]
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)
  · apply AnalyticAt.pi
    intro q
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    apply Finset.analyticAt_fun_sum
    intro l _
    exact (hTx l (finProdFinEquiv.symm q).1).mul (hInv l (finProdFinEquiv.symm q).2)
  · intro t
    simp only [hperiodT x (hW p hx).1 t]

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_real_gram_source_coefficients
