import Repair.SourceCollarNovParameterLocalization
import Probes.Round3ParameterNativeParent

/-! The single actual parameter localization is identically one near every
original parameter sample. Its product with a parent therefore has exactly
the same full mixed jets in the unchanged original charts, at every order.
No derivative budget for the auxiliary localization is used. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {P M : Type*} [TopologicalSpace P] [TopologicalSpace M]

def sourceCollarNovParameterLocalized (psi : P → ℝ) (theta : P × M → ℝ) (z : P × M) : ℝ :=
  psi z.1 * theta z

theorem sourceCollarNov_parameter_localized_tsupport (psi : P → ℝ) (theta : P × M → ℝ) :
    tsupport (sourceCollarNovParameterLocalized psi theta) ⊆
      tsupport theta ∩ Prod.fst ⁻¹' tsupport psi := by
  intro z hz
  exact ⟨tsupport_mul_subset_right hz,
    tsupport_comp_subset_preimage _ continuous_fst (tsupport_mul_subset_left hz)⟩

theorem sourceCollarNov_parameter_localized_germ
    (psi : P → ℝ) (V K : Set P) (hV : IsOpen V) (hKV : K ⊆ V) (hOne : EqOn psi 1 V)
    (theta : P × M → ℝ) (z : P × M) (hz : z.1 ∈ K) :
    sourceCollarNovParameterLocalized psi theta =ᶠ[𝓝 z] theta := by
  filter_upwards [(hV.preimage continuous_fst).mem_nhds (hKV hz)] with w hw
  change psi w.1 * theta w = theta w
  rw [hOne hw]
  simp only [Pi.one_apply,one_mul]

theorem sourceCollarNov_parameter_localized_comp_germ
    {X : Type*} [TopologicalSpace X]
    (psi : P → ℝ) (V K : Set P) (hV : IsOpen V) (hKV : K ⊆ V) (hOne : EqOn psi 1 V)
    (theta : P × M → ℝ) (q : X → P × M) (y : X) (hq : ContinuousAt q y)
    (hy : (q y).1 ∈ K) :
    (sourceCollarNovParameterLocalized psi theta ∘ q) =ᶠ[𝓝 y] (theta ∘ q) :=
  (sourceCollarNov_parameter_localized_germ psi V K hV hKV hOne theta (q y) hy).comp_tendsto hq

theorem sourceCollarNov_parameter_localized_mixed_jets
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (psi : P → ℝ) (V K : Set P) (hV : IsOpen V) (hKV : K ⊆ V) (hOne : EqOn psi 1 V)
    (theta : P × M → ℝ) (q : X → P × M) (y : X) (hq : ContinuousAt q y)
    (hy : (q y).1 ∈ K) (j : ℕ) :
    iteratedFDeriv ℝ j (sourceCollarNovParameterLocalized psi theta ∘ q) y =
      iteratedFDeriv ℝ j (theta ∘ q) y :=
  ((sourceCollarNov_parameter_localized_comp_germ psi V K hV hKV hOne theta q y hq hy).iteratedFDeriv ℝ j).eq_of_nhds

variable {d : ℕ}
local notation "Ep" => EuclideanSpace ℝ (Fin d)

/-- The supported native pullback retains a strong neighborhood equality,
including its actual indicator at the original parameter-chart boundary. -/
theorem sourceCollarNov_parameter_native_parent_germ
    (psi : P → ℝ) (V K : Set P) (hV : IsOpen V) (hKV : K ⊆ V) (hOne : EqOn psi 1 V)
    (B : OpenPartialHomeomorph P Ep) (theta : P × M → ℝ)
    (z : Ep × M) (hz : z.1 ∈ B.target) (hK : B.symm z.1 ∈ K) :
    round3ParameterNativeParent B (sourceCollarNovParameterLocalized psi theta) =ᶠ[𝓝 z]
      round3ParameterNativeParent B theta := by
  classical
  let q := round3ParameterProductChart (M := M) B
  have hzq : z ∈ q.target := ⟨hz,mem_univ _⟩
  have hEq := sourceCollarNov_parameter_localized_comp_germ psi V K hV hKV hOne theta
    q.symm z (q.symm.continuousAt hzq) hK
  filter_upwards [q.open_target.mem_nhds hzq,hEq] with w hw heq
  change (if w ∈ q.target then sourceCollarNovParameterLocalized psi theta (q.symm w) else 0) =
    (if w ∈ q.target then theta (q.symm w) else 0)
  rw [if_pos hw,if_pos hw]
  exact heq

/-- Strong native-parent equality after any unchanged original source chart.
This directly transports every mixed derivative used by the host supplier. -/
theorem sourceCollarNov_parameter_native_parent_host_germ
    {n : ℕ} (psi : P → ℝ) (V K : Set P) (hV : IsOpen V) (hKV : K ⊆ V) (hOne : EqOn psi 1 V)
    (B : OpenPartialHomeomorph P Ep) (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (theta : P × M → ℝ) (y : Ep × EuclideanSpace ℝ (Fin n))
    (hp : y.1 ∈ B.target) (hx : y.2 ∈ e.target) (hK : B.symm y.1 ∈ K) :
    (round3ParameterNativeParent B (sourceCollarNovParameterLocalized psi theta) ∘
      ((OpenPartialHomeomorph.refl Ep).prod e).symm) =ᶠ[𝓝 y]
    (round3ParameterNativeParent B theta ∘ ((OpenPartialHomeomorph.refl Ep).prod e).symm) := by
  let q := (OpenPartialHomeomorph.refl Ep).prod e
  exact (sourceCollarNov_parameter_native_parent_germ psi V K hV hKV hOne B theta
    (q.symm y) hp hK).comp_tendsto (q.symm.continuousAt ⟨mem_univ _,hx⟩)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.sourceCollarNov_parameter_localized_mixed_jets
#print axioms GlobalEmbedding.Continuation.sourceCollarNov_parameter_native_parent_host_germ
