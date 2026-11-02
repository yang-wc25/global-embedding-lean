import GlobalEmbedding.Paper.CollarCKTaylorHomogeneousPolynomial
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Shared commutative coefficients of nonlinear formal composition

Source: Gantumur, notes2, Theorem 18, nonlinear substitution in the CK proof.
Reuse the accepted word/fiber/Taylor coefficients and native finite composition reindexing.
All polynomial expressions below are native finite polynomials, not another Taylor carrier.
-/

noncomputable section
open scoped BigOperators
namespace GlobalEmbedding.Paper

variable {σ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]

omit [DecidableEq τ] in
/-- Component projection commutes with the same finite shared word fiber.
Source: Gantumur, componentwise vector Taylor coefficients. Apply the actual coordinate
projection to the original finite sum; no new coefficient convention is introduced. -/
theorem collarCKTaylorCoeff_component
    (q : FormalMultilinearSeries ℝ (σ → ℝ) (τ → ℝ)) (i : τ) (d : σ →₀ ℕ) :
    collarCKTaylorCoeff ((ContinuousLinearMap.proj i).compFormalMultilinearSeries q) d =
      collarCKTaylorCoeff q d i := by
  simp only [collarCKTaylorCoeff, ContinuousLinearMap.compFormalMultilinearSeries_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousLinearMap.proj_apply, Finset.sum_apply]

omit [DecidableEq τ] in
/-- Every projected package has zero native constant coefficient when the inner constant
vanishes. Source: Gantumur, zero-origin substitution. Use the accepted constant coefficient
formula on the original complete fiber and the actual component projection. -/
theorem collarCKTaylorCoeff_component_constantCoeff
    (q : FormalMultilinearSeries ℝ (σ → ℝ) (τ → ℝ)) (h0 : ∀ v, q 0 v = 0) (i : τ) :
    MvPowerSeries.constantCoeff
      (fun d ↦ collarCKTaylorCoeff
        ((ContinuousLinearMap.proj i).compFormalMultilinearSeries q) d : MvPowerSeries σ ℝ) =
          0 := by
  change collarCKTaylorCoeff
    ((ContinuousLinearMap.proj i).compFormalMultilinearSeries q) 0 = 0
  rw [collarCKTaylorCoeff_component, collarCKTaylorCoeff_zero q h0]
  rfl

omit [DecidableEq τ] in
/-- Zero inner constant term gives genuine native lawful substitution for all component
packages, including no variables. Source: Gantumur, zero-origin substitution; directly reuse
native HasSubst from the preceding exact zero constant coefficient identity. -/
theorem collarCKTaylorCoeff_components_hasSubst
    (q : FormalMultilinearSeries ℝ (σ → ℝ) (τ → ℝ)) (h0 : ∀ v, q 0 v = 0) :
    MvPowerSeries.HasSubst (fun i ↦
      (fun d ↦ collarCKTaylorCoeff
        ((ContinuousLinearMap.proj i).compFormalMultilinearSeries q) d : MvPowerSeries σ ℝ)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero
    (collarCKTaylorCoeff_component_constantCoeff q h0)

omit [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] in
/-- Extracting a coefficient of degree less than `N` from the native composition target keeps
exactly all compositions of that degree. Source: the finite composition expansion used in
Gantumur's substitution argument. Native block/length bounds put every required composition in
the target; homogeneity kills every other degree. -/
theorem collarCKCompositionTarget_coeff (N : ℕ) (d : σ →₀ ℕ) (hd : d.degree < N)
    (P : ∀ k, Composition k → MvPolynomial σ ℝ)
    (hP : ∀ k c e, e.degree ≠ k → (P k c).coeff e = 0) :
    (∑ a ∈ FormalMultilinearSeries.compPartialSumTarget 0 N N, P a.1 a.2).coeff d =
      ∑ c : Composition d.degree, (P d.degree c).coeff d := by
  classical
  let S : Finset (Σ k, Composition k) := Finset.univ.map (Function.Embedding.sigmaMk d.degree)
  have hsub : S ⊆ FormalMultilinearSeries.compPartialSumTarget 0 N N := by
    intro a ha
    obtain ⟨c, _, rfl⟩ := Finset.mem_map.mp ha
    apply FormalMultilinearSeries.mem_compPartialSumTarget_iff.mpr
    exact ⟨Nat.zero_le _, c.length_le.trans_lt hd,
      fun j ↦ (c.blocksFun_le j).trans_lt hd⟩
  rw [MvPolynomial.coeff_sum]
  have heq := Finset.sum_subset hsub (f := fun a ↦ (P a.1 a.2).coeff d) (by
    intro a ha hnot
    apply hP
    intro heq
    apply hnot
    rcases a with ⟨k, c⟩
    dsimp at heq
    subst k
    exact Finset.mem_map.mpr ⟨c, Finset.mem_univ _, rfl⟩)
  rw [← heq]
  simp only [S, Finset.sum_map]
  rfl

omit [DecidableEq σ] [DecidableEq τ] in
/-- Native finite composition reindexing also identifies any genuine polynomial
representatives of the same diagonal terms. Source: Gantumur, substitution of finite Taylor
polynomials. Polynomial function extensionality and the native `comp_partialSum` theorem
supply the whole identity; no product or word-permutation proof is repeated. -/
theorem collarCKFiniteCompositionPolynomial
    (p : FormalMultilinearSeries ℝ (τ → ℝ) ℝ)
    (q : FormalMultilinearSeries ℝ (σ → ℝ) (τ → ℝ)) (M N : ℕ)
    (P : MvPolynomial τ ℝ) (Q : τ → MvPolynomial σ ℝ)
    (T : ∀ k, Composition k → MvPolynomial σ ℝ)
    (hP : ∀ z, MvPolynomial.eval z P = p.partialSum M z)
    (hQ : ∀ i z, MvPolynomial.eval z (Q i) =
      (∑ j ∈ Finset.Ico 1 N, q j (fun _ ↦ z)) i)
    (hT : ∀ k c z, MvPolynomial.eval z (T k c) =
      p.compAlongComposition q c (fun _ ↦ z)) :
    MvPolynomial.aeval Q P =
      ∑ a ∈ FormalMultilinearSeries.compPartialSumTarget 0 M N, T a.1 a.2 := by
  apply MvPolynomial.funext
  intro z
  simp only [MvPolynomial.aeval_def, MvPolynomial.eval_eval₂, map_sum, hT]
  have hc : (MvPolynomial.eval z).comp
      (algebraMap ℝ (MvPolynomial σ ℝ)) = RingHom.id ℝ := by
    ext x
    simp
  rw [hc, MvPolynomial.eval₂_id, hP]
  have hq : (fun i ↦ MvPolynomial.eval z (Q i)) =
      ∑ j ∈ Finset.Ico 1 N, q j (fun _ ↦ z) := by
    funext i
    exact hQ i z
  rw [hq]
  exact p.comp_partialSum q M N z

/-- A polynomial dictionary with the native homogeneous coefficient and evaluation laws
identifies nonlinear formal composition with native substitution. Source: Gantumur, finite
Taylor substitution. This intermediate lemma makes reuse of the independently owned polynomial
dictionary explicit; the final theorem instantiates it with the accepted shared truncations. -/
theorem collarCKTaylorComposition_of_polynomial
    (Hσ : FormalMultilinearSeries ℝ (σ → ℝ) ℝ → ℕ → MvPolynomial σ ℝ)
    (Hτ : FormalMultilinearSeries ℝ (τ → ℝ) ℝ → ℕ → MvPolynomial τ ℝ)
    (hcσ : ∀ r k d, (Hσ r k).coeff d =
      if d.degree = k then collarCKTaylorCoeff r d else 0)
    (hcτ : ∀ r k d, (Hτ r k).coeff d =
      if d.degree = k then collarCKTaylorCoeff r d else 0)
    (heσ : ∀ r k z, MvPolynomial.eval z (Hσ r k) = r k (fun _ ↦ z))
    (heτ : ∀ r k z, MvPolynomial.eval z (Hτ r k) = r k (fun _ ↦ z))
    (p : FormalMultilinearSeries ℝ (τ → ℝ) ℝ)
    (q : FormalMultilinearSeries ℝ (σ → ℝ) (τ → ℝ)) (h0 : ∀ v, q 0 v = 0) :
    (fun d ↦ collarCKTaylorCoeff (p.comp q) d : MvPowerSeries σ ℝ) =
      MvPowerSeries.subst (fun i ↦
        (fun d ↦ collarCKTaylorCoeff
          ((ContinuousLinearMap.proj i).compFormalMultilinearSeries q) d : MvPowerSeries σ ℝ))
        (fun d ↦ collarCKTaylorCoeff p d : MvPowerSeries τ ℝ) := by
  classical
  let f : MvPowerSeries τ ℝ := fun d ↦ collarCKTaylorCoeff p d
  let qi (i : τ) : FormalMultilinearSeries ℝ (σ → ℝ) ℝ :=
    (ContinuousLinearMap.proj i).compFormalMultilinearSeries q
  let a (i : τ) : MvPowerSeries σ ℝ := fun d ↦ collarCKTaylorCoeff (qi i) d
  have hconst (i : τ) : MvPowerSeries.constantCoeff (a i) = 0 :=
    collarCKTaylorCoeff_component_constantCoeff q h0 i
  have htruncσ (r : FormalMultilinearSeries ℝ (σ → ℝ) ℝ) (N : ℕ) :
      MvPowerSeries.truncTotal N (fun d ↦ collarCKTaylorCoeff r d : MvPowerSeries σ ℝ) =
        ∑ k ∈ Finset.range N, Hσ r k := by
    let A : MvPowerSeries σ ℝ := fun d ↦ collarCKTaylorCoeff r d
    change MvPowerSeries.truncTotal N A = _
    ext d
    have hA : MvPowerSeries.coeff d A = collarCKTaylorCoeff r d := rfl
    rw [MvPowerSeries.coeff_truncTotal_eq_ite, hA, MvPolynomial.coeff_sum]
    simp [hcσ]
  have htruncτ (r : FormalMultilinearSeries ℝ (τ → ℝ) ℝ) (N : ℕ) :
      MvPowerSeries.truncTotal N (fun d ↦ collarCKTaylorCoeff r d : MvPowerSeries τ ℝ) =
        ∑ k ∈ Finset.range N, Hτ r k := by
    let A : MvPowerSeries τ ℝ := fun d ↦ collarCKTaylorCoeff r d
    change MvPowerSeries.truncTotal N A = _
    ext d
    have hA : MvPowerSeries.coeff d A = collarCKTaylorCoeff r d := rfl
    rw [MvPowerSeries.coeff_truncTotal_eq_ite, hA, MvPolynomial.coeff_sum]
    simp [hcτ]
  have hcoe (P : MvPolynomial τ ℝ) (Q : τ → MvPolynomial σ ℝ) :
      MvPowerSeries.subst (fun i ↦ (Q i : MvPowerSeries σ ℝ))
        (P : MvPowerSeries τ ℝ) =
          (MvPolynomial.aeval Q P : MvPowerSeries σ ℝ) := by
    rw [MvPowerSeries.subst_coe]
    have h := MvPolynomial.comp_aeval_apply
      (MvPolynomial.coeToMvPowerSeries.algHom (σ := σ) ℝ) (f := Q) P
    simpa only [MvPolynomial.coeToMvPowerSeries.algHom_apply,
      Algebra.algebraMap_self, MvPowerSeries.map_id, RingHom.id_apply] using h.symm
  apply MvPowerSeries.ext
  intro d
  let N := d.degree + 1
  have hN : 0 < N := Nat.succ_pos _
  have hd : d.degree < N := Nat.lt_succ_self _
  let R (k : ℕ) (c : Composition k) : FormalMultilinearSeries ℝ (σ → ℝ) ℝ :=
    Pi.single k (p.compAlongComposition q c)
  let T (k : ℕ) (c : Composition k) : MvPolynomial σ ℝ := Hσ (R k c) k
  have hcT (k : ℕ) (c : Composition k) (e : σ →₀ ℕ) :
      (T k c).coeff e = if e.degree = k then collarCKTaylorCoeff (R k c) e else 0 :=
    hcσ (R k c) k e
  have hT (k : ℕ) (c : Composition k) (z : σ → ℝ) :
      MvPolynomial.eval z (T k c) = p.compAlongComposition q c (fun _ ↦ z) := by
    simpa only [R, Pi.single_eq_same] using heσ (R k c) k z
  have hpoly :
      MvPolynomial.aeval (fun i ↦ MvPowerSeries.truncTotal N (a i))
          (MvPowerSeries.truncTotal N f) =
        ∑ b ∈ FormalMultilinearSeries.compPartialSumTarget 0 N N, T b.1 b.2 := by
    apply collarCKFiniteCompositionPolynomial p q N N _ _ T
    · intro z
      rw [htruncτ]
      simp only [map_sum, heτ, FormalMultilinearSeries.partialSum]
    · intro i z
      rw [htruncσ]
      simp only [map_sum, heσ]
      have hsum : (∑ k ∈ Finset.range N, q k (fun _ ↦ z)) =
          ∑ k ∈ Finset.Ico 1 N, q k (fun _ ↦ z) := by
        rw [Finset.sum_range_eq_add_Ico _ hN, h0, zero_add]
      simpa only [qi, ContinuousLinearMap.compFormalMultilinearSeries_apply,
        ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
        ContinuousLinearMap.proj_apply, Finset.sum_apply] using congrFun hsum i
    · exact hT
  have htarget :
      (∑ b ∈ FormalMultilinearSeries.compPartialSumTarget 0 N N, T b.1 b.2).coeff d =
        collarCKTaylorCoeff (p.comp q) d := by
    rw [collarCKCompositionTarget_coeff N d hd T]
    · simp only [hcT, ite_true, collarCKTaylorCoeff, R, Pi.single_eq_same]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w _
      simp only [FormalMultilinearSeries.comp, sum_apply,
        FormalMultilinearSeries.compAlongComposition_apply]
    · intro k c e he
      rw [hcT, ite_eq_right he]
  have hnative := MvPowerSeries.truncTotal_subst (f := f) (k := N) hconst
  rw [hcoe] at hnative
  have hcoeff := congrArg (fun P : MvPolynomial σ ℝ ↦ P.coeff d) hnative
  rw [MvPowerSeries.coeff_truncTotal _ hd, MvPowerSeries.coeff_truncTotal _ hd,
    MvPolynomial.coeff_coe, hpoly, htarget] at hcoeff
  exact hcoeff.symm

/-- The actual shared coefficient package of arbitrary formal composition is the native
multivariate substitution of the actual component packages. Source: Gantumur, Theorem 18,
nonlinear Taylor substitution. Instantiate the finite-polynomial bridge with precisely the
accepted native homogeneous truncations. No convergence or polynomial dictionary is assumed. -/
theorem collarCKTaylorComposition
    (p : FormalMultilinearSeries ℝ (τ → ℝ) ℝ)
    (q : FormalMultilinearSeries ℝ (σ → ℝ) (τ → ℝ)) (h0 : ∀ v, q 0 v = 0) :
    (fun d ↦ collarCKTaylorCoeff (p.comp q) d : MvPowerSeries σ ℝ) =
      MvPowerSeries.subst (fun i ↦
        (fun d ↦ collarCKTaylorCoeff
          ((ContinuousLinearMap.proj i).compFormalMultilinearSeries q) d : MvPowerSeries σ ℝ))
        (fun d ↦ collarCKTaylorCoeff p d : MvPowerSeries τ ℝ) := by
  classical
  exact collarCKTaylorComposition_of_polynomial
    (fun r k ↦ MvPowerSeries.truncFinset ℝ
      (Finset.univ.image (collarCKWordIndex (σ := σ) (k := k)))
      (fun d ↦ collarCKTaylorCoeff r d : MvPowerSeries σ ℝ))
    (fun r k ↦ MvPowerSeries.truncFinset ℝ
      (Finset.univ.image (collarCKWordIndex (σ := τ) (k := k)))
      (fun d ↦ collarCKTaylorCoeff r d : MvPowerSeries τ ℝ))
    collarCKTaylorHomogeneous_coeff collarCKTaylorHomogeneous_coeff
    collarCKTaylorHomogeneous_eval collarCKTaylorHomogeneous_eval p q h0

/-- Actual nonlinear analytic composition has exactly the same native formal substitution,
for every genuine output expansion witness. Source: Gantumur, Theorem 18. Native analytic
composition supplies the true composed expansion, zero inner value supplies the lawful constant
condition, and accepted witness independence identifies every output coefficient. -/
theorem collarCKTaylorCoeff_analytic_comp
    (f : (σ → ℝ) → (τ → ℝ)) (g : (τ → ℝ) → ℝ)
    (p : FormalMultilinearSeries ℝ (τ → ℝ) ℝ)
    (q : FormalMultilinearSeries ℝ (σ → ℝ) (τ → ℝ))
    (r : FormalMultilinearSeries ℝ (σ → ℝ) ℝ)
    (hf : HasFPowerSeriesAt f q 0) (hg : HasFPowerSeriesAt g p 0)
    (hr : HasFPowerSeriesAt (g ∘ f) r 0) (hf0 : f 0 = 0) :
    (fun d ↦ collarCKTaylorCoeff r d : MvPowerSeries σ ℝ) =
      MvPowerSeries.subst (fun i ↦
        (fun d ↦ collarCKTaylorCoeff
          ((ContinuousLinearMap.proj i).compFormalMultilinearSeries q) d : MvPowerSeries σ ℝ))
        (fun d ↦ collarCKTaylorCoeff p d : MvPowerSeries τ ℝ) := by
  have hq0 (v) : q 0 v = 0 := (hf.coeff_zero v).trans hf0
  have hg' : HasFPowerSeriesAt g p (f 0) := by simpa only [hf0] using hg
  have hcomp := hg'.comp hf
  have hsame : (fun d ↦ collarCKTaylorCoeff r d : MvPowerSeries σ ℝ) =
      (fun d ↦ collarCKTaylorCoeff (p.comp q) d : MvPowerSeries σ ℝ) := by
    apply MvPowerSeries.ext
    intro d
    exact collarCKTaylorCoeff_unique (g ∘ f) r (p.comp q) hr hcomp d
  exact hsame.trans (collarCKTaylorComposition p q hq0)

#print axioms collarCKTaylorCoeff_component
#print axioms collarCKTaylorCoeff_component_constantCoeff
#print axioms collarCKTaylorCoeff_components_hasSubst
#print axioms collarCKCompositionTarget_coeff
#print axioms collarCKFiniteCompositionPolynomial
#print axioms collarCKTaylorComposition_of_polynomial
#print axioms collarCKTaylorComposition
#print axioms collarCKTaylorCoeff_analytic_comp
end GlobalEmbedding.Paper
