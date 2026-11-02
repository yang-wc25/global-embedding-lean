import GlobalEmbedding.Paper.IncrementsGlobalPrimaryMeanBinding

/-! Exact locality of the SAME finite differential polynomial and geometric
reconstruction. These identities require no smoothness assumptions: native
derivatives respect actual neighborhood equality, including totalized values.
They will transport the finite mean construction into its proved positivity
neighborhood without changing the computed field there. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

section DifferentialPolynomial
variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]

theorem parameterRound2_actual_firstOrder_eqOn
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E)
    (u v : D → E) (O : Set D) (hO : IsOpen O) (he : EqOn u v O) :
    EqOn (incrementsActualFirstOrder A B u) (incrementsActualFirstOrder A B v) O := by
  intro x hx
  have hg : u =ᶠ[𝓝 x] v := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact he hy
  simp only [incrementsActualFirstOrder,he hx,hg.fderiv_eq]

theorem parameterRound2_actual_modeIterate_eqOn
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E)
    (alpha : ℂ) (length : ℕ) (u v : D → E) (O : Set D) (hO : IsOpen O)
    (he : EqOn u v O) :
    EqOn ((incrementsActualModeStep A B alpha)^[length] u)
      ((incrementsActualModeStep A B alpha)^[length] v) O := by
  induction length with
  | zero => exact he
  | succ length ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    intro x hx
    exact congrArg (fun z => (-alpha) • z)
      (parameterRound2_actual_firstOrder_eqOn A B _ _ O hO ih hx)

theorem parameterRound2_actual_modeSum_eqOn
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E)
    (alpha : ℂ) (length : ℕ) (u v : D → E) (O : Set D) (hO : IsOpen O)
    (he : EqOn u v O) :
    EqOn (incrementsActualModeSum A B alpha length u)
      (incrementsActualModeSum A B alpha length v) O := by
  intro x hx
  unfold incrementsActualModeSum
  congr 1
  exact Finset.sum_congr rfl fun k hk =>
    parameterRound2_actual_modeIterate_eqOn A B alpha k u v O hO he hx
end DifferentialPolynomial

section Reconstruction
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

theorem parameterRound2_actual_reconstruction_germ
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ,V) ∞ F) (c : D → M)
    (u v : D → D) (x : D) (he : u =ᶠ[𝓝 x] v) :
    incrementsModeReconstruction F hF c u x = incrementsModeReconstruction F hF c v x := by
  rw [incrementsModeReconstruction_split,incrementsModeReconstruction_split,
    he.eq_of_nhds,he.fderiv_eq]

theorem parameterRound2_actual_fullReconstruction_germ
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ,V) ∞ F) (c : D → M)
    (u v : D → D)
    (h : D → Fin (m+1) → Fin (m+1) → ℝ)
    (vf wf : (x : D) → normalSpace (I := I) F (c x))
    (x : D) (he : u =ᶠ[𝓝 x] v) (hv : vf x = wf x) :
    incrementsModeFullReconstruction F hF c u h vf x =
      incrementsModeFullReconstruction F hF c v h wf x := by
  simp only [incrementsModeFullReconstruction,
    parameterRound2_actual_reconstruction_germ F hF c u v x he,hv]
end Reconstruction

#print axioms parameterRound2_actual_modeSum_eqOn
#print axioms parameterRound2_actual_fullReconstruction_germ
end GlobalEmbedding.Continuation
