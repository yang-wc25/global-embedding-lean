import NormalPolar.PassiveOriginalHostLift

/-! Canonical original-parameter-chart realization of the passive host.
The B conjugation remains in both global function representatives. Only on
its real target is B composed with its inverse simplified to the identity. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {m d : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [TopologicalSpace P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "E₀" => EuclideanSpace ℝ (Fin 0)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)

def passiveOriginalCanonicalNativeHost (B : OpenPartialHomeomorph P Ep)
    (b₀ : OpenPartialHomeomorph (E₀ × D) (E₀ × D)) : OpenPartialHomeomorph X X :=
  round3ParameterChartPullback B (passiveParameterChart (P := P) (0 : E₀) b₀)

theorem passiveOriginalCanonicalNativeHost_source (B : OpenPartialHomeomorph P Ep)
    (b₀ : OpenPartialHomeomorph (E₀ × D) (E₀ × D)) (z : X) :
    z ∈ (passiveOriginalCanonicalNativeHost B b₀).source ↔
      z.1 ∈ B.target ∧ ((0 : E₀),z.2) ∈ b₀.source := by
  rw [passiveOriginalCanonicalNativeHost,round3ParameterChartPullback_source]
  constructor
  · exact fun h => ⟨h.1,h.2.1⟩
  · exact fun h => ⟨h.1,h.2,B.map_target h.1⟩

theorem passiveOriginalCanonicalNativeHost_target (B : OpenPartialHomeomorph P Ep)
    (b₀ : OpenPartialHomeomorph (E₀ × D) (E₀ × D)) (z : X) :
    z ∈ (passiveOriginalCanonicalNativeHost B b₀).target ↔
      z.1 ∈ B.target ∧ ((0 : E₀),z.2) ∈ b₀.target := by
  rw [passiveOriginalCanonicalNativeHost,round3ParameterChartPullback_target]
  constructor
  · exact fun h => ⟨h.1,h.2.1⟩
  · exact fun h => ⟨h.1,h.2,B.map_target h.1⟩

theorem passiveOriginalCanonicalNativeHost_factorization
    (B : OpenPartialHomeomorph P Ep) (c : OpenPartialHomeomorph M D)
    (b₀ : OpenPartialHomeomorph (E₀ × D) (E₀ × D)) :
    actualHostAdaptedChart c (passiveOriginalCanonicalNativeHost B b₀) =
      round3ParameterChartPullback B
        (passiveParameterChart (P := P) (0 : E₀) (actualHostAdaptedChart c b₀)) := by
  apply OpenPartialHomeomorph.ext
  · intro z; rfl
  · intro z; rfl
  · ext z
    constructor
    · intro hz
      have hh := (passiveOriginalCanonicalNativeHost_source B b₀ (z.1,c z.2)).mp hz.2
      apply (round3ParameterChartPullback_source_iff B _
        (passiveParameterChart_preserves (0 : E₀) _) z hh.1).mpr
      exact ⟨⟨mem_univ _,hz.1.2⟩,hh.2⟩
    · intro hz
      have hh := (round3ParameterChartPullback_source B _ z).mp hz
      refine ⟨⟨mem_univ _,hh.2.1.1.2⟩,?_⟩
      exact (passiveOriginalCanonicalNativeHost_source B b₀ (z.1,c z.2)).mpr ⟨hh.1,hh.2.1.2⟩

theorem passiveOriginal_canonical_host_lift
    (B : OpenPartialHomeomorph P Ep)
    (c : OpenPartialHomeomorph M D) (hc : c ∈ maximalAtlas IM ∞ M)
    (b₀ : OpenPartialHomeomorph (E₀ × D) (E₀ × D))
    (psi₀ : E₀ × M → ℝ) (e₀ : E₀ → OpenPartialHomeomorph M D)
    (hdata : ActualOriginalHostSliceData c b₀ psi₀ e₀) :
    let b := passiveOriginalCanonicalNativeHost B b₀
    let psi := fun z : Ep × M => psi₀ (0,z.2)
    ∃ e : Ep → OpenPartialHomeomorph M D,
      ActualOriginalHostSliceData c b psi e ∧
      (∀ p, ((e p).symm : D → M) = (e₀ 0).symm) ∧
      (∀ p x, e p x = e₀ 0 x) := by
  intro b psi
  let bL := passiveParameterChart (P := Ep) (0 : E₀) b₀
  obtain ⟨eL,hdataL,hInvL,hForwL⟩ := passiveOriginal_host_lift (d := d) c hc b₀ psi₀ e₀ hdata
  have hg := actual_host_slice_geometry_inputs c hc bL psi eL hdataL
  have hS : b.source ⊆ bL.source := fun z hz =>
    ((passiveOriginalCanonicalNativeHost_source B b₀ z).mp hz).2
  have hT : b.target ⊆ bL.target := fun z hz =>
    ((passiveOriginalCanonicalNativeHost_target B b₀ z).mp hz).2
  have hForward : EqOn b bL b.source := by
    intro z hz
    have hzB := ((passiveOriginalCanonicalNativeHost_source B b₀ z).mp hz).1
    change (B (B.symm z.1),(b₀ ((0 : E₀),z.2)).2) = (z.1,(b₀ ((0 : E₀),z.2)).2)
    rw [B.right_inv hzB]
  have hInverse : EqOn b.symm bL.symm b.target := by
    intro z hz
    have hzB := ((passiveOriginalCanonicalNativeHost_target B b₀ z).mp hz).1
    change (B (B.symm z.1),(b₀.symm ((0 : E₀),z.2)).2) = (z.1,(b₀.symm ((0 : E₀),z.2)).2)
    rw [B.right_inv hzB]
  have hb : ContDiffOn ℝ ∞ b b.source := (hg.2.1.mono hS).congr hForward
  have hbi : ContDiffOn ℝ ∞ b.symm b.target := (hg.2.2.1.mono hT).congr hInverse
  have hParam : ∀ z ∈ b.source, (b z).1 = z.1 := by
    intro z hz
    rw [hForward hz]
    rfl
  have hPhase : ∀ z ∈ b.source, (b z).2 0 = psi (z.1,c.symm z.2) := by
    intro z hz
    rw [hForward hz]
    have hzt := (hg.1 (hS hz)).2
    have hs : (z.1,c.symm z.2) ∈ (actualHostAdaptedChart c bL).source := by
      refine ⟨⟨mem_univ _,c.map_target hzt⟩,?_⟩
      change (z.1,c (c.symm z.2)) ∈ bL.source
      rw [c.right_inv hzt]
      exact hS hz
    have hh := (hdataL.2.2.2.1 (z.1,c.symm z.2) hs).2
    change (bL (z.1,c (c.symm z.2))).2 0 = _ at hh
    rwa [c.right_inv hzt] at hh
  obtain ⟨hat,ha,hai,hforw,e,he,hes,het,hef,hei,hpair,hadapt,hback,hforward,hbj,hfj⟩ :=
    actual_adapted_chart_original_host c hc psi b (hS.trans hg.1) hb hbi hParam hPhase
  refine ⟨e,⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hadapt,hback,hforward,hbj,hfj⟩,?_,?_⟩
  · intro p
    funext y
    rw [hei]
    rw [← hInvL p]
    rcases hdataL with ⟨_,_,_,_,_,_,_,_,heiL,_,_,_,_,_,_⟩
    rw [heiL]
    rfl
  · intro p x
    rw [hef,← hForwL p x]
    rcases hdataL with ⟨_,_,_,_,_,_,_,hefL,_,_,_,_,_,_,_⟩
    rw [hefL]
    rfl

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveOriginalCanonicalNativeHost_factorization
#print axioms GlobalEmbedding.Continuation.passiveOriginal_canonical_host_lift
