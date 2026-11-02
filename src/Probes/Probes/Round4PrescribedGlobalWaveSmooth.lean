import Probes.Round4PrescribedGlobalWave

/-!
# Actual global first-block jets and native parameter/spatial-Hessian responses

The smoothness of every actual column is produced from the primitive supported
chart data, before differentiating it. Arbitrary auxiliary parameters and each
mode's actual chart are retained. The observed functions are literal pullbacks
of the same global displacement through a smooth spatial observation chart.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff BigOperators Topology
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Pspace" => Fin p → ℝ

theorem round4_prescribed_global_wave_joint_smooth
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (tau : ℝ) (length : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (W : Set (Ep × M)) (K : Fin r → Set (Ep × M)) (hW : IsOpen W)
    (hK : ∀ l, IsClosed (Subtype.val ⁻¹' K l : Set W)) (hKsource : ∀ l, K l ⊆ (a l).source)
    (hchart : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,X) ∞ (a l) (a l).source)
    (hA : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hB : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hG : ∀ l, ContDiffOn ℝ ∞ (fun z : X => freeGramRightInverse (fderiv ℝ (F z.1 ∘ c l z.1) z.2)) (a l).target)
    (hJ : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (normalSpace (I := I) (F z.1) (c l z.1 z.2)).subtypeL.comp
      (incrementsModeCoordinateJ (F z.1) (hF z.1) (c l z.1) z.2)) (a l).target)
    (hT : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeTransverseValue (F z.1) (c l z.1) z.2) (a l).target)
    (hBR : ∀ l, ContDiffOn ℝ ∞ (fun z : X => fun k : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c l z.1) z.2 0 k : V)) (a l).target)
    (hvf : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (vf l z.1 z.2 : V)) (a l).target)
    (hinput : ∀ l z, z ∈ (a l).target → z ∈ tsupport (fun w : X => (vf l w.1 w.2 : V)) → (a l).symm z ∈ K l)
    (hphase : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,ℝ) ∞ (phase l) W)
    : ContMDiffOn ((𝓘(ℝ,Pspace)).prod ((𝓘(ℝ,Ep)).prod I)) 𝓘(ℝ,V) ∞
      (fun z : Pspace × (Ep × M) => round4PrescribedGlobalWave label F hF c vf phase tau length a z.1 z.2)
      (univ ×ˢ W) := by
  classical
  have ha (l : Fin r) (ch : Bool) := round4_prescribed_global_parameter_joint_smooth ch label l F hF
    (c l) (vf l) tau length (a l) W (K l) hW (hK l) (hKsource l) (hchart l)
    (hA l) (hB l) (hG l) (hJ l) (hT l) (hBR l) (hvf l) (hinput l)
  apply contMDiffOn_finsetSum
  intro l _
  have hp : ContMDiffOn ((𝓘(ℝ,Pspace)).prod ((𝓘(ℝ,Ep)).prod I)) 𝓘(ℝ,ℝ) ∞
      (fun z : Pspace × (Ep × M) => phase l z.2/tau) (univ ×ˢ W) :=
    ((hphase l).div_const tau).comp contMDiffOn_snd (fun z hz => hz.2)
  exact ((Real.contDiff_cos.contMDiff.comp_contMDiffOn hp).smul (ha l false)).sub
    ((Real.contDiff_sin.contMDiff.comp_contMDiffOn hp).smul (ha l true))

theorem round4_prescribed_global_observed_contDiffOn
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (tau : ℝ) (length : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (W : Set (Ep × M)) (K : Fin r → Set (Ep × M)) (hW : IsOpen W)
    (hK : ∀ l, IsClosed (Subtype.val ⁻¹' K l : Set W)) (hKsource : ∀ l, K l ⊆ (a l).source)
    (hchart : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,X) ∞ (a l) (a l).source)
    (hA : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hB : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hG : ∀ l, ContDiffOn ℝ ∞ (fun z : X => freeGramRightInverse (fderiv ℝ (F z.1 ∘ c l z.1) z.2)) (a l).target)
    (hJ : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (normalSpace (I := I) (F z.1) (c l z.1 z.2)).subtypeL.comp
      (incrementsModeCoordinateJ (F z.1) (hF z.1) (c l z.1) z.2)) (a l).target)
    (hT : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeTransverseValue (F z.1) (c l z.1) z.2) (a l).target)
    (hBR : ∀ l, ContDiffOn ℝ ∞ (fun z : X => fun k : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c l z.1) z.2 0 k : V)) (a l).target)
    (hvf : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (vf l z.1 z.2 : V)) (a l).target)
    (hinput : ∀ l z, z ∈ (a l).target → z ∈ tsupport (fun w : X => (vf l w.1 w.2 : V)) → (a l).symm z ∈ K l)
    (hphase : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,ℝ) ∞ (phase l) W)
    (b : Ep) (obs : D → M) (O : Set D)
    (hobs : ContMDiffOn 𝓘(ℝ,D) I ∞ obs O) (hOW : ∀ y ∈ O, (b,obs y) ∈ W)
    (u : Pspace) :
    ContDiffOn ℝ ∞ (fun y => round4PrescribedGlobalWave label F hF c vf phase tau length a u (b,obs y)) O := by
  have hw := round4_prescribed_global_wave_joint_smooth label F hF c vf phase tau length a W K hW hK hKsource hchart hA hB hG hJ hT hBR hvf hinput hphase
  have he : ContMDiffOn 𝓘(ℝ,D) ((𝓘(ℝ,Pspace)).prod ((𝓘(ℝ,Ep)).prod I)) ∞
      (fun y => (u,(b,obs y))) O := contMDiffOn_const.prodMk (contMDiffOn_const.prodMk hobs)
  exact (hw.comp he (fun y hy => ⟨mem_univ _,hOW y hy⟩)).contDiffOn

theorem round4_prescribed_global_observed_jet_response
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (tau : ℝ) (length : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (W : Set (Ep × M)) (K : Fin r → Set (Ep × M)) (hW : IsOpen W)
    (hK : ∀ l, IsClosed (Subtype.val ⁻¹' K l : Set W)) (hKsource : ∀ l, K l ⊆ (a l).source)
    (hchart : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,X) ∞ (a l) (a l).source)
    (hA : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hB : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hG : ∀ l, ContDiffOn ℝ ∞ (fun z : X => freeGramRightInverse (fderiv ℝ (F z.1 ∘ c l z.1) z.2)) (a l).target)
    (hJ : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (normalSpace (I := I) (F z.1) (c l z.1 z.2)).subtypeL.comp
      (incrementsModeCoordinateJ (F z.1) (hF z.1) (c l z.1) z.2)) (a l).target)
    (hT : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeTransverseValue (F z.1) (c l z.1) z.2) (a l).target)
    (hBR : ∀ l, ContDiffOn ℝ ∞ (fun z : X => fun k : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c l z.1) z.2 0 k : V)) (a l).target)
    (hvf : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (vf l z.1 z.2 : V)) (a l).target)
    (hinput : ∀ l z, z ∈ (a l).target → z ∈ tsupport (fun w : X => (vf l w.1 w.2 : V)) → (a l).symm z ∈ K l)
    (hphase : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,ℝ) ∞ (phase l) W)
    (b : Ep) (obs : D → M) (O : Set D) (hO : IsOpen O)
    (hobs : ContMDiffOn 𝓘(ℝ,D) I ∞ obs O) (hOW : ∀ y ∈ O, (b,obs y) ∈ W)
    (j : ℕ) (u : Pspace) (x : D) (hx : x ∈ O) :
    let wave := fun v y => round4PrescribedGlobalWave label F hF c vf phase tau length a v (b,obs y)
    let J := probeColumnMap (fun q => iteratedFDeriv ℝ j (wave (Pi.single q 1)) x)
    iteratedFDeriv ℝ j (wave u) x = J u ∧
      HasFDerivAt (fun v => iteratedFDeriv ℝ j (wave v) x) J u := by
  intro wave J
  have hc (q : Fin p) : ContDiffAt ℝ j (wave (Pi.single q 1)) x :=
    ((round4_prescribed_global_observed_contDiffOn label F hF c vf phase tau length a W K hW hK hKsource hchart hA hB hG hJ hT hBR hvf hinput hphase
      b obs O hobs hOW (Pi.single q 1)).contDiffAt (hO.mem_nhds hx)).of_le (by simp)
  have heq (v : Pspace) : wave v = finiteProbeSource (fun q => wave (Pi.single q 1)) v := by
    funext y
    exact round4PrescribedGlobalWave_columns label F hF c vf phase tau length a hA hB hBR hvf v (b,obs y)
  have hj (v : Pspace) : iteratedFDeriv ℝ j (wave v) x = J v := by
    rw [heq]
    exact iteratedFDeriv_finiteProbeSource (fun q => wave (Pi.single q 1)) v j x hc
  refine ⟨hj u,?_⟩
  have hf : (fun v => iteratedFDeriv ℝ j (wave v) x) = J := funext hj
  rw [hf]
  exact J.hasFDerivAt

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_prescribed_global_wave_joint_smooth
#print axioms GlobalEmbedding.Continuation.round4_prescribed_global_observed_contDiffOn
#print axioms GlobalEmbedding.Continuation.round4_prescribed_global_observed_jet_response
