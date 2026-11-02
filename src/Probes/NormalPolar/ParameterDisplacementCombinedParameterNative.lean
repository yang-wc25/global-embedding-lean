import NormalPolar.ParameterDisplacementCombinedParameterNaturality

/-!
# Exact native binding and all-joint-jet naturality for the physical U1

Every normed-coordinate realization is the same complete common array on P.
The chart-target identity holds on a neighborhood, so arbitrary joint jets,
including parameter-direction derivatives, are preserved. The input tensor
may vary with those variables; it remains the same physical input on both
sides.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Manifold Function Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {E H M P Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [TopologicalSpace P]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N p r : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

section NativeBinding
variable
  (F : Ep → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ b, ContMDiff I 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F b))
  (g : Round3ParameterPrimaryFamily (I := I) (m := m) (Λ := Λ) (Β := Β) F)
  (label : (Fin r × Bool) ↪ Fin p)
  (c : Fin r → Ep → EuclideanSpace ℝ (Fin (m+1)) → M)
  (vf : (l : Fin r) → (b : Ep) → (x : EuclideanSpace ℝ (Fin (m+1))) →
    normalSpace (I := I) (F b) (c l b x))
  (phase : Fin r → Ep × M → ℝ) (tau delta : ℝ) (backgroundLength probeLength : ℕ)
  (a : Fin r → OpenPartialHomeomorph (Ep × M) (Ep × EuclideanSpace ℝ (Fin (m+1))))
  (input : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))

theorem actualParameterProbeCombinedAmplitude_native :
    actualParameterProbeCombinedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input =
      round4ParameterProbeCombinedAmplitude F hF (g.toNative F) label c vf tau delta
        backgroundLength probeLength a input := rfl

theorem actualParameterProbeCombinedPrimary_native :
    actualParameterProbeCombinedPrimary F hF g label c vf phase tau delta backgroundLength probeLength a input =
      round4ParameterProbeCombinedPrimary F hF (g.toNative F) label c vf phase tau delta
        backgroundLength probeLength a input := rfl

theorem actualParameterProbeCombinedMean_native :
    actualParameterProbeCombinedMean F hF g label c vf phase tau delta backgroundLength probeLength a input =
      round4ParameterProbeCombinedMean F hF (g.toNative F) label c vf phase tau delta
        backgroundLength probeLength a input := rfl

end NativeBinding

variable
  (F : P → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ b, ContMDiff I 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F b))
  (g : Round3ParameterPrimaryFamily (I := I) (m := m) (Λ := Λ) (Β := Β) F)
  (label : (Fin r × Bool) ↪ Fin p)
  (c : Fin r → P → EuclideanSpace ℝ (Fin (m+1)) → M)
  (vf : (l : Fin r) → (b : P) → (x : EuclideanSpace ℝ (Fin (m+1))) →
    normalSpace (I := I) (F b) (c l b x))
  (phase : Fin r → P × M → ℝ) (tau delta : ℝ) (backgroundLength probeLength : ℕ)
  (a : Fin r → OpenPartialHomeomorph (P × M) (P × EuclideanSpace ℝ (Fin (m+1))))
  (B : OpenPartialHomeomorph P Ep)
  (hg : ∀ l k, Round3ParameterChartPreserves (g.chart l k))
  (ha : ∀ l, Round3ParameterChartPreserves (a l))

include hg ha

theorem actualParameterProbeCombinedPrimary_native_pullback
    (input : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (u : Fin p → ℝ) (b : Ep) (hb : b ∈ B.target) (x : M) :
    round4ParameterProbeCombinedPrimary (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      ((round3ParameterPrimaryPullback F g B).toNative (fun t => F (B.symm t)))
      label (fun l t => c l (B.symm t)) (fun l t => vf l (B.symm t))
      (fun l z => phase l (B.symm z.1,z.2)) tau delta backgroundLength probeLength
      (fun l => round3ParameterChartPullback B (a l)) (fun t => input (B.symm t)) u (b,x) =
    actualParameterProbeCombinedPrimary F hF g label c vf phase tau delta backgroundLength probeLength a input u (B.symm b,x) :=
  actualParameterProbeCombinedPrimary_pullback F hF g label c vf phase tau delta
    backgroundLength probeLength a B hg ha input u b hb x

theorem actualParameterProbeCombinedMean_native_pullback
    (input : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (u : Fin p → ℝ) (b : Ep) (hb : b ∈ B.target) (x : M) :
    round4ParameterProbeCombinedMean (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      ((round3ParameterPrimaryPullback F g B).toNative (fun t => F (B.symm t)))
      label (fun l t => c l (B.symm t)) (fun l t => vf l (B.symm t))
      (fun l z => phase l (B.symm z.1,z.2)) tau delta backgroundLength probeLength
      (fun l => round3ParameterChartPullback B (a l)) (fun t => input (B.symm t)) u b x =
    actualParameterProbeCombinedMean F hF g label c vf phase tau delta backgroundLength probeLength a input u (B.symm b) x :=
  actualParameterProbeCombinedMean_pullback F hF g label c vf phase tau delta
    backgroundLength probeLength a B hg ha input u b hb x

theorem actualParameterProbeCombinedPrimary_native_pullback_germ
    {Y : Type*} [TopologicalSpace Y]
    (input : Y → (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (u : Y → Fin p → ℝ) (b : Y → Ep) (x : Y → M) (y : Y)
    (hb : ContinuousAt b y) (hy : b y ∈ B.target) :
    (fun z => round4ParameterProbeCombinedPrimary (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      ((round3ParameterPrimaryPullback F g B).toNative (fun t => F (B.symm t)))
      label (fun l t => c l (B.symm t)) (fun l t => vf l (B.symm t))
      (fun l w => phase l (B.symm w.1,w.2)) tau delta backgroundLength probeLength
      (fun l => round3ParameterChartPullback B (a l)) (fun t => input z (B.symm t))
      (u z) (b z,x z)) =ᶠ[𝓝 y]
    (fun z => actualParameterProbeCombinedPrimary F hF g label c vf phase tau delta
      backgroundLength probeLength a (input z) (u z) (B.symm (b z),x z)) := by
  filter_upwards [hb.preimage_mem_nhds (B.open_target.mem_nhds hy)] with z hz
  exact actualParameterProbeCombinedPrimary_native_pullback F hF g label c vf phase tau delta
    backgroundLength probeLength a B hg ha (input z) (u z) (b z) hz (x z)

/-- Every native joint derivative is that of the literal physical U1 in its
genuine chart. This includes arbitrary orders such as the original 442 jets. -/
theorem actualParameterProbeCombinedPrimary_native_pullback_jets
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (input : Y → (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (u : Y → Fin p → ℝ) (b : Y → Ep) (x : Y → M) (y : Y)
    (hb : ContinuousAt b y) (hy : b y ∈ B.target) (j : ℕ) :
    iteratedFDeriv ℝ j (fun z => round4ParameterProbeCombinedPrimary
      (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      ((round3ParameterPrimaryPullback F g B).toNative (fun t => F (B.symm t)))
      label (fun l t => c l (B.symm t)) (fun l t => vf l (B.symm t))
      (fun l w => phase l (B.symm w.1,w.2)) tau delta backgroundLength probeLength
      (fun l => round3ParameterChartPullback B (a l)) (fun t => input z (B.symm t))
      (u z) (b z,x z)) y =
    iteratedFDeriv ℝ j (fun z => actualParameterProbeCombinedPrimary F hF g label c vf phase tau delta
      backgroundLength probeLength a (input z) (u z) (B.symm (b z),x z)) y :=
  ((actualParameterProbeCombinedPrimary_native_pullback_germ F hF g label c vf phase tau delta
    backgroundLength probeLength a B hg ha input u b x y hb hy).iteratedFDeriv ℝ j).eq_of_nhds

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualParameterProbeCombinedPrimary_native_pullback
#print axioms GlobalEmbedding.Continuation.actualParameterProbeCombinedMean_native_pullback
#print axioms GlobalEmbedding.Continuation.actualParameterProbeCombinedPrimary_native_pullback_jets
