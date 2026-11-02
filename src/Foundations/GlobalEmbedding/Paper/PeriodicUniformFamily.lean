import GlobalEmbedding.Paper.PeriodicFlatTorusDistance
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Jointly continuous periodic lift families vary globally uniformly

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 399–418.
DAG node: `balanced-holder-periodic-uniform-family`.
-/

open Set WithLp
open scoped Topology

namespace GlobalEmbedding.Paper

/-- A jointly continuous integer-periodic family varies uniformly on every lift point near
each parameter, using the actual compact fundamental cube.

Proof: restrict the spatial variable to the compact cube and apply the local-parameter
Heine–Cantor theorem. Integer periodicity reduces every lift point to its fractional-part
cube representative, so the same eventual bound holds globally.
Source: compact-torus parameter estimates in the proof of `lem:balanced`. -/
theorem periodic_uniform_family {P Z : Type*} [UniformSpace P]
    [WeaklyLocallyCompactSpace P] [PseudoMetricSpace Z] {a : ℕ}
    (F : P → EuclideanSpace ℝ (Fin a) → Z)
    (hF : Continuous (fun z : P × EuclideanSpace ℝ (Fin a) ↦ F z.1 z.2))
    (hperiodic : ∀ (p : P) (x : EuclideanSpace ℝ (Fin a)) (n : Fin a → ℤ),
      F p (x + toLp 2 (fun i ↦ (n i : ℝ))) = F p x) (p₀ : P) :
    TendstoUniformly F (F p₀) (𝓝 p₀) := by
  let K := Icc (0 : Fin a → ℝ) 1
  have hc : Continuous (fun z : P × K ↦ F z.1 (toLp 2 z.2.val)) :=
    hF.comp (continuous_fst.prodMk ((PiLp.continuous_toLp _ _).comp
      (continuous_subtype_val.comp continuous_snd)))
  have hlim := Continuous.tendstoUniformly (fun p (y : K) ↦ F p (toLp 2 y.val)) hc p₀
  have hreduce (p : P) (x : EuclideanSpace ℝ (Fin a)) :
      F p x = F p (toLp 2 (fun i ↦ Int.fract (x i))) := by
    have hxy : toLp 2 (fun i ↦ Int.fract (x i)) +
        toLp 2 (fun i ↦ (⌊x i⌋ : ℝ)) = x := by ext i; simp [Int.fract_add_floor]
    simpa only [hxy] using
      hperiodic p (toLp 2 (fun i ↦ Int.fract (x i))) (fun i ↦ ⌊x i⌋)
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hlim ε hε] with p hp
  intro x
  let y : K := ⟨fun i ↦ Int.fract (x i),
    ⟨fun i ↦ Int.fract_nonneg _, fun i ↦ (Int.fract_lt_one _).le⟩⟩
  rw [hreduce p₀ x, hreduce p x]
  exact hp y

#print axioms periodic_uniform_family

end GlobalEmbedding.Paper
