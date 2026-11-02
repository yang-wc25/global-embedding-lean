import Probes.ActualOriginalHostRefinement

/-!
# The fixed template chart in every original observing host

The chart is the literal original observer-to-owner transition followed
by the already chosen weighted template chart.  It is restricted only in
source, so both full function expressions are retained.  Actual manifold
slices are produced from this same chart, and the first derivative costs
are products of the original transition and template bounds.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "I" => 𝓘(ℝ,D)
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]

def repairReferenceHostTransition (observer owner : OpenPartialHomeomorph M D) :
    OpenPartialHomeomorph X X :=
  (OpenPartialHomeomorph.refl Ep).prod (observer.symm.trans owner)

theorem repair_reference_host_transition_smooth
    (observer owner : OpenPartialHomeomorph M D)
    (hobserver : observer ∈ IsManifold.maximalAtlas I ∞ M)
    (howner : owner ∈ IsManifold.maximalAtlas I ∞ M) :
    ContDiffOn ℝ ∞ (repairReferenceHostTransition (Ep := Ep) observer owner)
      (repairReferenceHostTransition (Ep := Ep) observer owner).source ∧
    ContDiffOn ℝ ∞ (repairReferenceHostTransition (Ep := Ep) observer owner).symm
      (repairReferenceHostTransition (Ep := Ep) observer owner).target := by
  have hs (a b : OpenPartialHomeomorph M D)
      (ha : a ∈ IsManifold.maximalAtlas I ∞ M) (hb : b ∈ IsManifold.maximalAtlas I ∞ M) :
      ContDiffOn ℝ ∞ (fun z : X => (z.1,b (a.symm z.2)))
        (Set.univ ×ˢ (a.target ∩ a.symm ⁻¹' b.source)) := by
    have ht : ContDiffOn ℝ ∞ (b ∘ a.symm) (a.target ∩ a.symm ⁻¹' b.source) :=
      ((contMDiffOn_of_mem_maximalAtlas hb).comp
        ((contMDiffOn_symm_of_mem_maximalAtlas ha).mono inter_subset_left)
        (fun _ hz => hz.2)).contDiffOn
    exact contDiffOn_fst.prodMk (ht.comp contDiffOn_snd (fun _ hz => hz.2))
  exact ⟨hs observer owner hobserver howner,hs owner observer howner hobserver⟩

def repairReferenceRehostedChart (observer owner : OpenPartialHomeomorph M D)
    (own : OpenPartialHomeomorph X X) (U : Set X) (hU : IsOpen U) :
    OpenPartialHomeomorph X X :=
  ((repairReferenceHostTransition observer owner).trans own).restrOpen U hU

theorem repair_reference_rehosted_functions
    (observer owner : OpenPartialHomeomorph M D)
    (own : OpenPartialHomeomorph X X) (U : Set X) (hU : IsOpen U) :
    (∀ z, repairReferenceRehostedChart observer owner own U hU z =
      own (z.1,owner (observer.symm z.2))) ∧
    (∀ z, (repairReferenceRehostedChart observer owner own U hU).symm z =
      ((own.symm z).1,observer (owner.symm (own.symm z).2))) := ⟨fun _ => rfl,fun _ => rfl⟩

/-- A real observed-host phase chart, with no new adapted-chart choice.
The only new choice is its canonical slice description. -/
theorem repair_reference_rehosted_phase_chart
    (observer owner : OpenPartialHomeomorph M D)
    (hobserver : observer ∈ IsManifold.maximalAtlas I ∞ M)
    (howner : owner ∈ IsManifold.maximalAtlas I ∞ M)
    (own : OpenPartialHomeomorph X X) (U : Set X) (hU : IsOpen U)
    (psi : Ep × M → ℝ)
    (hOwnSource : own.source ⊆ (actualOriginalHostJointChart (Ep := Ep) owner).target)
    (hOwn : ContDiffOn ℝ ∞ own own.source)
    (hOwnInv : ContDiffOn ℝ ∞ own.symm own.target)
    (hParam : ∀ z ∈ own.source, (own z).1=z.1)
    (hPhase : ∀ z ∈ own.source, (own z).2 0=psi (z.1,owner.symm z.2))
    (Bforward Binverse Tforward Tinverse : ℝ)
    (hBforward : 0 ≤ Bforward) (hBinverse : 0 ≤ Binverse)
    (hTforward : 0 ≤ Tforward) (hTinverse : 0 ≤ Tinverse)
    (hOwnForward : ∀ z ∈ own.source, ‖fderiv ℝ own z‖ ≤ Bforward)
    (hOwnInverse : ∀ z ∈ own.target, ‖fderiv ℝ own.symm z‖ ≤ Binverse)
    (hForward : ∀ z ∈ (repairReferenceHostTransition (Ep := Ep) observer owner).source,
      ‖fderiv ℝ (repairReferenceHostTransition (Ep := Ep) observer owner) z‖ ≤ Tforward)
    (hInverse : ∀ z ∈ (repairReferenceHostTransition (Ep := Ep) observer owner).target,
      ‖fderiv ℝ (repairReferenceHostTransition (Ep := Ep) observer owner).symm z‖ ≤ Tinverse) :
    let native := repairReferenceRehostedChart observer owner own U hU
    native.source ⊆ U ∧
    native.source ⊆ (actualOriginalHostJointChart (Ep := Ep) observer).target ∧
    ContDiffOn ℝ ∞ native native.source ∧ ContDiffOn ℝ ∞ native.symm native.target ∧
    (∀ z ∈ native.source, ‖fderiv ℝ native z‖ ≤ Bforward*Tforward) ∧
    (∀ z ∈ native.target, ‖fderiv ℝ native.symm z‖ ≤ Tinverse*Binverse) ∧
    ∃ slices : Ep → OpenPartialHomeomorph M D,
      ActualOriginalHostSliceData observer native psi slices := by
  intro native
  let transition := repairReferenceHostTransition (Ep := Ep) observer owner
  have ht := repair_reference_host_transition_smooth (Ep := Ep) observer owner hobserver howner
  have hSource (z : X) (hz : z ∈ native.source) :
      z ∈ transition.source ∧ transition z ∈ own.source ∧ z ∈ U :=
    ⟨hz.1.1,hz.1.2,hz.2⟩
  have hTarget (z : X) (hz : z ∈ native.target) :
      z ∈ own.target ∧ own.symm z ∈ transition.target := hz.1
  have hn : ContDiffOn ℝ ∞ native native.source :=
    hOwn.comp (ht.1.mono (fun z hz => (hSource z hz).1)) (fun z hz => (hSource z hz).2.1)
  have hni : ContDiffOn ℝ ∞ native.symm native.target :=
    ht.2.comp (hOwnInv.mono (fun z hz => (hTarget z hz).1)) (fun z hz => (hTarget z hz).2)
  have hnsource : native.source ⊆ (actualOriginalHostJointChart (Ep := Ep) observer).target :=
    fun z hz => ⟨mem_univ _,(hSource z hz).1.2.1⟩
  have hnp (z : X) (hz : z ∈ native.source) : (native z).1=z.1 :=
    hParam (transition z) (hSource z hz).2.1
  have hnf (z : X) (hz : z ∈ native.source) :
      (native z).2 0=psi (z.1,observer.symm z.2) := by
    have hh := hPhase (transition z) (hSource z hz).2.1
    change (native z).2 0=psi (z.1,owner.symm (owner (observer.symm z.2))) at hh
    have hi : owner.symm (owner (observer.symm z.2))=observer.symm z.2 :=
      owner.left_inv (hSource z hz).1.2.2
    rwa [hi] at hh
  obtain ⟨hat,ha,hai,hforw,slices,he⟩ := actual_adapted_chart_original_host observer hobserver
    psi native hnsource hn hni hnp hnf
  refine ⟨fun z hz => (hSource z hz).2.2,hnsource,hn,hni,?_,?_,slices,hat,ha,hai,hforw,he⟩
  · intro z hz
    have hts := (hSource z hz).1
    have hos := (hSource z hz).2.1
    have htd := (ht.1.contDiffAt (transition.open_source.mem_nhds hts)).differentiableAt (by simp)
    have hod := (hOwn.contDiffAt (own.open_source.mem_nhds hos)).differentiableAt (by simp)
    change ‖fderiv ℝ (own ∘ transition) z‖ ≤ _
    rw [fderiv_comp z hod htd]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hOwnForward _ hos) (hForward _ hts) (norm_nonneg _) hBforward)
  · intro z hz
    have hott := (hTarget z hz).1
    have htt := (hTarget z hz).2
    have hod := (hOwnInv.contDiffAt (own.open_target.mem_nhds hott)).differentiableAt (by simp)
    have htd := (ht.2.contDiffAt (transition.open_target.mem_nhds htt)).differentiableAt (by simp)
    change ‖fderiv ℝ (transition.symm ∘ own.symm) z‖ ≤ _
    rw [fderiv_comp z htd hod]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hInverse _ htt) (hOwnInverse _ hott) (norm_nonneg _) hTinverse)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repair_reference_rehosted_phase_chart
#print axioms GlobalEmbedding.Continuation.repair_reference_rehosted_functions
