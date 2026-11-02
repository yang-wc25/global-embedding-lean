import Probes.ActualRefinementBumpJets

/-! A fixed plateau equals one on a neighborhood of the radius-2 support
ball and is supported in the radius-3 ball. All full joint derivative
constants precede the center and scale. -/

noncomputable section
open Set Function Filter Metric
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def repairReferenceUnitPlateau : ContDiffBump (0 : E) := ⟨5/2,3,by norm_num,by norm_num⟩

theorem repair_reference_unit_plateau_jets (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, ‖iteratedFDeriv ℝ j (repairReferenceUnitPlateau E : E → ℝ) x‖ ≤ C := by
  have hsm : ContDiff ℝ ∞ (repairReferenceUnitPlateau E : E → ℝ) := (repairReferenceUnitPlateau E).contDiff
  have hB : BddAbove (range (fun x : E => ‖iteratedFDeriv ℝ j (repairReferenceUnitPlateau E : E → ℝ) x‖)) := by
    apply (hsm.continuous_iteratedFDeriv (by simp)).norm.bddAbove_range_of_hasCompactSupport
    apply HasCompactSupport.comp_left _ norm_zero
    exact (repairReferenceUnitPlateau E).hasCompactSupport.iteratedFDeriv j
  obtain ⟨C,hC⟩ := hB
  exact ⟨max C 0,le_max_right _ _,fun x => (hC (mem_range_self x)).trans (le_max_left _ _)⟩

def repairReferencePlateauJetCost (j : ℕ) : ℝ :=
  Classical.choose (repair_reference_unit_plateau_jets E j)

theorem repair_reference_plateau_jet_cost_nonneg (j : ℕ) : 0 ≤ repairReferencePlateauJetCost E j :=
  (Classical.choose_spec (repair_reference_unit_plateau_jets E j)).1

def repairReferencePlateau (r : ℝ) (c : E) : E → ℝ :=
  fun x => repairReferenceUnitPlateau E (r⁻¹ • (x-c))

theorem repair_reference_plateau_native (r : ℝ) (hr : 0 < r) (c : E) :
    repairReferencePlateau E r c = (⟨5*r/2,3*r,by positivity,by linarith⟩ : ContDiffBump c) := by
  funext x
  have hratio : (3*r)/(5*r/2)=3/(5/2) := by field_simp
  have hscale : (5/2 : ℝ)⁻¹ * r⁻¹ = (5*r/2)⁻¹ := by field_simp
  simp only [repairReferencePlateau,repairReferenceUnitPlateau,ContDiffBump.apply,
    sub_zero,smul_smul,hratio,hscale]

theorem repair_reference_plateau_smooth (r : ℝ) (c : E) : ContDiff ℝ ∞ (repairReferencePlateau E r c) :=
  (repairReferenceUnitPlateau E).contDiff.comp ((contDiff_id.sub contDiff_const).const_smul r⁻¹)

theorem repair_reference_plateau_support (r : ℝ) (hr : 0 < r) (c : E) :
    tsupport (repairReferencePlateau E r c) = closedBall c (3*r) := by
  rw [repair_reference_plateau_native E r hr c]
  exact ContDiffBump.tsupport_eq _

theorem repair_reference_plateau_one (r : ℝ) (hr : 0 < r) (c x : E)
    (hx : dist x c ≤ 5*r/2) : repairReferencePlateau E r c x = 1 := by
  rw [repair_reference_plateau_native E r hr c]
  exact ContDiffBump.one_of_mem_closedBall _ hx

theorem repair_reference_plateau_germ (r : ℝ) (hr : 0 < r) (c x : E)
    (hx : x ∈ closedBall c (2*r)) : repairReferencePlateau E r c =ᶠ[𝓝 x] fun _ => 1 := by
  have hball : x ∈ ball c (5*r/2) := (closedBall_subset_ball (by linarith : 2*r<5*r/2)) hx
  filter_upwards [isOpen_ball.mem_nhds hball] with y hy
  exact repair_reference_plateau_one E r hr c y (mem_ball.mp hy).le

theorem repair_reference_plateau_weighted_jets (r : ℝ) (hr : 0 < r) (c x : E) (j : ℕ) :
    r^j*‖iteratedFDeriv ℝ j (repairReferencePlateau E r c) x‖ ≤ repairReferencePlateauJetCost E j := by
  let u : E → ℝ := repairReferenceUnitPlateau E
  have he : repairReferencePlateau E r c =
      fun y => (u ∘ slowDilation r⁻¹ (inv_ne_zero hr.ne')) (y-c) := rfl
  rw [he,iteratedFDeriv_comp_sub,norm_iteratedFDeriv_slowDilation u r⁻¹ (inv_pos.mpr hr)]
  have hp : r^j*(r⁻¹)^j=1 := by rw [← mul_pow,mul_inv_cancel₀ hr.ne',one_pow]
  rw [← mul_assoc,hp,one_mul]
  exact (Classical.choose_spec (repair_reference_unit_plateau_jets E j)).2 _

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repair_reference_plateau_germ
#print axioms GlobalEmbedding.Continuation.repair_reference_plateau_weighted_jets
