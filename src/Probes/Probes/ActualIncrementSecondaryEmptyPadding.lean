import Probes.ActualSecondaryOriginalConstruction

/-! Actual zero padding for varying finite secondary refinements. The empty
chart is an honest open restriction of a given original host chart. Every
padded displacement is literally zero for all scales and polynomial lengths;
no formal dummy source or output budget is substituted. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {Ep M : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

def actualSecondaryEmptyChart (host : OpenPartialHomeomorph M D) : OpenPartialHomeomorph (Ep × M) X :=
  ((OpenPartialHomeomorph.refl Ep).prod host).restrOpen ∅ isOpen_empty

@[simp] theorem actualSecondaryEmptyChart_source (host : OpenPartialHomeomorph M D) :
    (actualSecondaryEmptyChart (Ep := Ep) host).source = ∅ := by
  change ((OpenPartialHomeomorph.refl Ep).prod host).source ∩ ∅ = ∅
  exact inter_empty _

@[simp] theorem actualSecondaryEmptyChart_target (host : OpenPartialHomeomorph M D) :
    (actualSecondaryEmptyChart (Ep := Ep) host).target = ∅ := by
  change ((OpenPartialHomeomorph.refl Ep).prod host).target ∩
    ((OpenPartialHomeomorph.refl Ep).prod host).symm ⁻¹' ∅ = ∅
  simp only [preimage_empty, inter_empty]

def actualSecondaryEmptyChoice (host : OpenPartialHomeomorph M D) : ActualOriginalSecondaryChoice Ep M m where
  host := host
  chart := actualSecondaryEmptyChart host
  c := fun _ x => host.symm x
  cutoff := 0

/-- Empty padding has no geometric reserve or derivative-budget requirements.
All genuine coefficient functions are retained on the actual empty domain. -/
def actualSecondaryEmptyRawGeometry
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (n j : ℕ) (ell Mg : ℝ) (W : Set (Ep × M))
    (host : OpenPartialHomeomorph M D) (hhost : host ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (phase : Ep × M → ℝ) : ActualSecondaryRawGeometry F hF n j ell Mg W where
  c := fun _ x => host.symm x
  chart := actualSecondaryEmptyChart host
  sample := ∅
  sample_subset := empty_subset _
  support := ∅
  support_closed := by simp only [preimage_empty]; exact isClosed_empty
  support_source := empty_subset _
  source_domain := by rw [actualSecondaryEmptyChart_source]; exact empty_subset W
  chart_smooth := by rw [actualSecondaryEmptyChart_source]; exact contMDiffOn_empty
  inverse := by intro z hz; exact (by simpa only [actualSecondaryEmptyChart_target,mem_empty_iff_false] using hz : False).elim
  phase := phase
  phase_smooth := by rw [actualSecondaryEmptyChart_source]; exact contMDiffOn_empty
  adaptation := by intro z hz; exact (by simpa only [actualSecondaryEmptyChart_source,mem_empty_iff_false] using hz : False).elim
  brows_smooth := by rw [actualSecondaryEmptyChart_target]; exact contDiffOn_empty
  inverse_smooth := by rw [actualSecondaryEmptyChart_target]; exact contDiffOn_empty
  transverse_smooth := by rw [actualSecondaryEmptyChart_target]; exact contDiffOn_empty
  value_smooth := by rw [actualSecondaryEmptyChart_target]; exact contDiffOn_empty
  coefficientA_smooth := by rw [actualSecondaryEmptyChart_target]; exact contDiffOn_empty
  coefficientB_smooth := by rw [actualSecondaryEmptyChart_target]; exact contDiffOn_empty
  brows_bound := fun _ _ _ hz => hz.elim
  transverse_bound := fun _ _ _ hz => hz.elim
  inverse_bound := fun _ _ _ hz => hz.elim
  value_bound := fun _ _ _ hz => hz.elim
  coefficientA_bound := fun _ _ _ hz => hz.elim
  coefficientB_bound := fun _ _ _ hz => hz.elim
  spatialChart := fun _ => host
  coordinate := rfl
  maximal := fun _ => hhost
  target := by intro z hz; exact (by simpa only [actualSecondaryEmptyChart_target,mem_empty_iff_false] using hz : False).elim
  immersion := by intro z hz; exact (by simpa only [actualSecondaryEmptyChart_target,mem_empty_iff_false] using hz : False).elim
  gram := by intro z hz; exact (by simpa only [actualSecondaryEmptyChart_target,mem_empty_iff_false] using hz : False).elim

variable {Label SubPrimary : Type*} [Fintype Label] [DecidableEq Label] [Fintype SubPrimary]

theorem actual_secondary_empty_piece
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (input : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (length : ℕ) (tau delta : ℝ) (r : (Label × Label) × Fin 4)
    (host : OpenPartialHomeomorph M D) :
    actualOriginalSecondaryPiece F hF g input length tau delta r (actualSecondaryEmptyChoice host) = 0 := by
  funext y
  simp only [actualOriginalSecondaryPiece,actualSecondarySupportedWave,
    actualSecondaryEmptyChoice,actualSecondaryEmptyChart_source,mem_empty_iff_false,ite_false,Pi.zero_apply,smul_zero,sub_self]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualSecondaryEmptyRawGeometry
#print axioms GlobalEmbedding.Continuation.actual_secondary_empty_piece
