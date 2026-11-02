import GlobalEmbedding.Paper.FreeHopfCompactOrbitBranch
import GlobalEmbedding.Paper.FreeHopfOrbitBranchEquivariance
import GlobalEmbedding.Paper.FreeHopfOrbitLift
import GlobalEmbedding.Paper.CollarLittleHolderEvaluation
import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# An actual native correction from the genuine whole-product orbit branch

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines403–418 and477–495.
DAG node: `free-hopf-orbit-correction`.
-/

noncomputable section

open Set WithLp
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- Actual sources construct an actual jointly smooth correction with its true orbit lift.

Proof: the genuine compact orbit-branch constructor supplies actual little profiles,
fixed equations and strict-small bounds on one interval over the whole product. Actual
source transport and strict-small uniqueness force profile covariance at every real orbit
shift. Evaluate time times the actual profile at zero by the accepted bounded evaluation
CLM. This gives native joint smoothness; covariance gives the exact entire orbit lift.
The actual original little norm bound and genuine native jet pullback then give the
uniform vertical C² bound. The pointwise fixed-source equation follows by applying actual
linear evaluation to the genuine fixed equation. No desired correction, compatibility,
orbit lift, smoothness or jet bound is an assumption. The bounded symmetric equivariant Q
is a separate analytic construction input, instantiated by the canonical actual Q in the
full balanced bridge. Source: lem:balanced, lines403–418. -/
theorem freeHopf_orbit_correction {a d N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] {α : ℝ}
    (Q : LittlePeriodicCAlphaFunction a N 2 α →L[ℝ]
      LittlePeriodicCAlphaFunction a N 2 α →L[ℝ] LittlePeriodicCAlphaFunction a d 2 α)
    (hQsym : ∀ v w, Q v w = Q w v)
    (hQτ : ∀ h v w, Q (littlePeriodicCAlphaTranslateIsometry h v)
      (littlePeriodicCAlphaTranslateIsometry h w) =
        littlePeriodicCAlphaTranslateIsometry h (Q v w))
    (R : ℝ) (hR : 0 < R)
    (sourceA : ℝ × FreeHopfProduct C →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (sourcef : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hA : ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N)) ∞
      sourceA (Metric.ball (0 : ℝ) R ×ˢ univ))
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ sourcef (Metric.ball (0 : ℝ) R ×ˢ univ))
    (hf0 : ∀ x, sourcef (0, x) = 0) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ δ L : ℝ, 0 < δ ∧ 0 < L ∧ δ < R ∧
      ∃ v : ℝ × FreeHopfProduct C → LittlePeriodicCAlphaFunction a N 2 α,
      ∃ U : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N),
        ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
          𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ U
          (Metric.ball (0 : ℝ) δ ×ˢ univ) ∧
        (∀ x, U (0, x) = 0) ∧
        ∀ (t : ℝ), t ∈ Metric.ball (0 : ℝ) δ → ∀ x : FreeHopfProduct C,
          ‖v (t, x)‖ ≤ L * |t| ∧
          (∀ y, (v (t, x)).val.toFun y =
            sourcef (t, freeHopfRealAction C (fun i ↦ y i) x) +
              sourceA (t, freeHopfRealAction C (fun i ↦ y i) x)
                ((Q (v (t, x)) (v (t, x))).val.toFun y)) ∧
          (∀ y, U (t, freeHopfOrbitLift C x y) = (t • v (t, x)).val.toFun y) ∧
          balancedVerticalC2Size (freeHopfGenerator C) (fun z ↦ U (t, z)) x ≤
            ((1 + (a : ℝ) + (a : ℝ) ^ 2) * L) * t ^ 2 := by
  obtain ⟨δ, L, hδ, hL, hδR, f, A, v, hv, hv0, hspec⟩ :=
    freeHopf_compact_orbit_branch C Q hQsym R hR sourceA sourcef hA hf hf0 hα0 hα1
  obtain ⟨ev, hev, _⟩ := collar_little_holder_evaluation (a := a) (N := N) (k := 2)
    (α := α) 0
  let U : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N) :=
    fun z ↦ ev (z.1 • v z)
  have hU : ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ U (Metric.ball (0 : ℝ) δ ×ˢ univ) :=
    ev.contMDiff.comp_contMDiffOn (contMDiffOn_fst.smul hv)
  have hcov (t : ℝ) (ht : t ∈ Metric.ball (0 : ℝ) δ) (x : FreeHopfProduct C)
      (s : EuclideanSpace ℝ (Fin a)) :
      v (t, freeHopfRealAction C (fun i ↦ s i) x) =
        littlePeriodicCAlphaTranslateIsometry s (v (t, x)) := by
    rcases hspec t ht x with ⟨hfx, hAx, hvx, _, hsx⟩
    rcases hspec t ht (freeHopfRealAction C (fun i ↦ s i) x) with
      ⟨hfs, hAs, hvs, _, hss⟩
    exact freeHopf_orbit_fixed_branch_translate C x s Q hQsym hQτ
      (fun z ↦ sourceA (t, z)) (fun z ↦ sourcef (t, z))
      (f (t, x)) (f (t, freeHopfRealAction C (fun i ↦ s i) x))
      (v (t, x)) (v (t, freeHopfRealAction C (fun i ↦ s i) x))
      (A (t, x)) (A (t, freeHopfRealAction C (fun i ↦ s i) x))
      hfx hfs hAx hAs hvx hvs hsx hss
  have hlift (t : ℝ) (ht : t ∈ Metric.ball (0 : ℝ) δ) (x : FreeHopfProduct C)
      (y : EuclideanSpace ℝ (Fin a)) :
      U (t, freeHopfOrbitLift C x y) = (t • v (t, x)).val.toFun y := by
    change ev (t • v (t, freeHopfRealAction C (fun i ↦ y i) x)) = _
    rw [hcov t ht x y, ← map_smul, hev]
    change (t • v (t, x)).val.toFun (0 + y) = (t • v (t, x)).val.toFun y
    rw [zero_add]
  refine ⟨δ, L, hδ, hL, hδR, v, U, hU, ?_, ?_⟩
  · intro x
    simp [U]
  · intro t ht x
    rcases hspec t ht x with ⟨hfx, hAx, hfix, hnorm, _⟩
    refine ⟨hnorm, ?_, hlift t ht x, ?_⟩
    · intro y
      obtain ⟨ey, hey, _⟩ := collar_little_holder_evaluation (a := a) (N := N) (k := 2)
        (α := α) y
      have he := congrArg ey hfix
      rw [map_add] at he
      simp only [hey] at he
      rw [hfx, hAx] at he
      exact he
    · have hUt : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
          (fun z ↦ U (t, z)) :=
        hU.comp_contMDiff (contMDiff_const.prodMk contMDiff_id)
          (fun z ↦ ⟨ht, mem_univ z⟩)
      have hjet := freeHopf_verticalC2Size_le_little_norm C (fun z ↦ U (t, z)) hUt x
        (t • v (t, x)) (hlift t ht x) 0
      rw [freeHopfOrbitLift_zero] at hjet
      have hscaled : ‖t • v (t, x)‖ ≤ L * t ^ 2 := by
        calc
          ‖t • v (t, x)‖ = |t| * ‖v (t, x)‖ := by rw [norm_smul, Real.norm_eq_abs]
          _ ≤ |t| * (L * |t|) := mul_le_mul_of_nonneg_left hnorm (abs_nonneg t)
          _ = L * |t| ^ 2 := by ring
          _ = L * t ^ 2 := by rw [sq_abs]
      calc
        balancedVerticalC2Size (freeHopfGenerator C) (fun z ↦ U (t, z)) x ≤
            (1 + (a : ℝ) + (a : ℝ) ^ 2) * ‖t • v (t, x)‖ := hjet
        _ ≤ (1 + (a : ℝ) + (a : ℝ) ^ 2) * (L * t ^ 2) :=
          mul_le_mul_of_nonneg_left hscaled (by positivity)
        _ = ((1 + (a : ℝ) + (a : ℝ) ^ 2) * L) * t ^ 2 := by ring

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.freeHopf_orbit_correction
