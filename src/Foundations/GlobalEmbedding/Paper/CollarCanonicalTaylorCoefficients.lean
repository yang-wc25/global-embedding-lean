import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Canonical smooth periodic parameter Taylor coefficients

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. Normalized joint derivatives in parameter directions construct actual
complex multilinear coefficient functions, before the separate uniform Cauchy estimates.
-/

open Set WithLp
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Joint complex analyticity near the real orbit slice constructs canonical parameter Taylor
coefficients that are complex multilinear, genuinely smooth in space and integer-periodic.

Source: Proposition `prop:collar`, proof lines 530–534. Restrict the nth joint derivative to
vectors (m_i,0) and divide by n!. Its pointwise family is algebraically complex multilinear.
Joint analyticity makes the nth joint derivative analytic near every real slice point.
Restricting scalars to the reals, composing with the real affine slice map, and applying the
bounded evaluation at the fixed parameter tuple prove genuine C∞ spatial regularity. Integer
translation invariance of g passes to its full joint derivative by the exact shift identity
for iterated derivatives, and therefore to the canonical coefficients. Uniform convergence
radii and uniform mixed-jet Cauchy bounds remain separate obligations.
-/
theorem collar_canonical_taylor_coefficients {b a N : ℕ}
    (g : (EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin a)) →
      EuclideanSpace ℂ (Fin N))
    (z₀ : EuclideanSpace ℂ (Fin b))
    (hg : ∀ x : EuclideanSpace ℝ (Fin a),
      AnalyticAt ℂ g (z₀, toLp 2 (fun i : Fin a ↦ (x i : ℂ))))
    (hperiodic : ∀ (w : EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin a))
      (t : Fin a → ℤ), g (w + (0, toLp 2 (fun i ↦ (t i : ℂ)))) = g w)
    (n : ℕ) :
    ∃ G : MultilinearMap ℂ (fun _ : Fin n ↦ EuclideanSpace ℂ (Fin b))
        (EuclideanSpace ℝ (Fin a) → EuclideanSpace ℂ (Fin N)),
      (∀ m x, G m x = (n.factorial : ℂ)⁻¹ •
        iteratedFDeriv ℂ n g (z₀, toLp 2 (fun i : Fin a ↦ (x i : ℂ)))
          (fun i ↦ (m i, 0))) ∧
      (∀ m, ContDiff ℝ ∞ (G m)) ∧
      (∀ m (x : EuclideanSpace ℝ (Fin a)) (t : Fin a → ℤ),
        G m (x + toLp 2 (fun i ↦ (t i : ℝ))) = G m x) := by
  let J : EuclideanSpace ℝ (Fin a) →L[ℝ] EuclideanSpace ℂ (Fin a) :=
    ({ toFun := fun x ↦ toLp 2 (fun i ↦ (x i : ℂ))
       map_add' := by intro x y; ext i; simp
       map_smul' := by intro c x; ext i; simp } :
      EuclideanSpace ℝ (Fin a) →ₗ[ℝ] EuclideanSpace ℂ (Fin a)).toContinuousLinearMap
  let B (x : EuclideanSpace ℝ (Fin a)) :=
    (iteratedFDeriv ℂ n g (z₀, J x)).compContinuousLinearMap
      (fun _ : Fin n ↦ ContinuousLinearMap.inl ℂ
        (EuclideanSpace ℂ (Fin b)) (EuclideanSpace ℂ (Fin a)))
  let G := (n.factorial : ℂ)⁻¹ • MultilinearMap.pi (fun x ↦ (B x).toMultilinearMap)
  have hG (m : Fin n → EuclideanSpace ℂ (Fin b)) (x : EuclideanSpace ℝ (Fin a)) :
      G m x = (n.factorial : ℂ)⁻¹ • iteratedFDeriv ℂ n g (z₀, J x)
        (fun i ↦ (m i, 0)) := rfl
  have hsmooth (m : Fin n → EuclideanSpace ℂ (Fin b)) : ContDiff ℝ ∞ (G m) := by
    let L : ((EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin a)) [×n]→L[ℂ]
        EuclideanSpace ℂ (Fin N)) →ₗ[ℂ] EuclideanSpace ℂ (Fin N) :=
      { toFun := fun f ↦ f (fun i ↦ (m i, 0))
        map_add' := by intro f h; rfl
        map_smul' := by intro c f; rfl }
    have hL (f : (EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin a)) [×n]→L[ℂ]
        EuclideanSpace ℂ (Fin N)) :
        ‖L f‖ ≤ (∏ i : Fin n, ‖(m i, (0 : EuclideanSpace ℂ (Fin a)))‖) * ‖f‖ := by
      simpa only [L, LinearMap.coe_mk, AddHom.coe_mk, mul_comm] using
        f.le_opNorm (fun i ↦ (m i, 0))
    let ev := (L.mkContinuous _ hL).restrictScalars ℝ
    have hloc : AnalyticOnNhd ℂ g (Set.range (fun x ↦ (z₀, J x))) := by
      rintro w ⟨x, rfl⟩
      exact hg x
    apply contDiff_iff_contDiffAt.mpr
    intro x
    have hD : ContDiffAt ℝ ∞ (iteratedFDeriv ℂ n g) (z₀, J x) :=
      ((hloc.iteratedFDeriv n) _ ⟨x, rfl⟩).restrictScalars.contDiffAt
    have hgraph : ContDiff ℝ ∞ (fun y ↦ (z₀, J y)) := contDiff_const.prodMk J.contDiff
    have hcomp := ev.contDiff.contDiffAt.comp x (hD.comp x hgraph.contDiffAt)
    exact hcomp.const_smul (n.factorial : ℂ)⁻¹
  refine ⟨G, hG, hsmooth, ?_⟩
  intro m x t
  let v : EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin a) :=
    (0, toLp 2 (fun i ↦ (t i : ℂ)))
  have htrans : (fun w ↦ g (w + v)) = g := funext (fun w ↦ hperiodic w t)
  have hD := iteratedFDeriv_comp_add_right (𝕜 := ℂ) (f := g) n v (z₀, J x)
  rw [htrans] at hD
  have hpoint : (z₀, J (x + toLp 2 (fun i ↦ (t i : ℝ)))) = (z₀, J x) + v := by
    ext i <;> simp [J, v]
  rw [hG, hG, hpoint, ← hD]

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_canonical_taylor_coefficients
