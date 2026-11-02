import Probes.Round4PrescribedGlobalSmooth

/-! The original globally extended complete prescribed amplitudes have exact
finite parameter columns, hence genuine joint smoothness including the probe
parameter. This resolves a qualitative regularity obligation of the actual
probe source; it makes no claim about the nonlinear background iteration. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff BigOperators
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

theorem round4PrescribedGlobalAmplitude_columns
    (imag : Bool) (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b)) (c : Ep → D → M)
    (vf : (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c b x))
    (tau : ℝ) (length : ℕ) (a : OpenPartialHomeomorph (Ep × M) X)
    (hA : ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1) z.2) a.target)
    (hB : ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1) z.2) a.target)
    (hBR : ContDiffOn ℝ ∞ (fun z : X => fun k : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c z.1) z.2 0 k : V)) a.target)
    (hvf : ContDiffOn ℝ ∞ (fun z : X => (vf z.1 z.2 : V)) a.target)
    (u : Pspace) :
    round4PrescribedGlobalAmplitude imag label l F hF c vf tau length a u =
      fun z => ∑ q, u q • round4PrescribedGlobalAmplitude imag label l F hF c vf tau length a (Pi.single q 1) z := by
  classical
  funext z
  by_cases hz : z ∈ a.source
  · let b := (a z).1
    let y := (a z).2
    let O := (fun x : D => (b,x)) ⁻¹' a.target
    have hO : IsOpen O := a.open_target.preimage (continuous_const.prodMk continuous_id)
    have hy : y ∈ O := a.map_source hz
    have ht : ContDiffOn ℝ ∞ (fun x : D => (b,x)) O :=
      (contDiff_const.prodMk contDiff_id).contDiffOn
    have hm : MapsTo (fun x : D => (b,x)) O a.target := fun _ hx => hx
    have hAs := hA.comp ht hm
    have hBs := hB.comp ht hm
    have hBRs := hBR.comp ht hm
    have hvfs := hvf.comp ht hm
    have hs := round4_actual_homogeneous_source_smooth (F b) (hF b) (c b) (vf b) O hBRs hvfs
    have hh := round4PrescribedAmplitude_finite_source imag label l (F b) (hF b) (c b)
      (vf b) tau length O hO hAs hBs hs u y hy
    simpa only [round4PrescribedGlobalAmplitude,hz,ite_true,finiteProbeSource] using hh
  · simp only [round4PrescribedGlobalAmplitude,hz,ite_false,smul_zero,Finset.sum_const_zero]

/-- Joint smoothness in u, all auxiliary parameters, and the manifold source,
with the literal chart extension and no output cutoff. -/
theorem round4_prescribed_global_parameter_joint_smooth
    (imag : Bool) (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b)) (c : Ep → D → M)
    (vf : (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c b x))
    (tau : ℝ) (length : ℕ) (a : OpenPartialHomeomorph (Ep × M) X)
    (W K : Set (Ep × M)) (hW : IsOpen W)
    (hK : IsClosed (Subtype.val ⁻¹' K : Set W)) (hKsource : K ⊆ a.source)
    (hchart : ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,X) ∞ a a.source)
    (hA : ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1) z.2) a.target)
    (hB : ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1) z.2) a.target)
    (hG : ContDiffOn ℝ ∞ (fun z : X => freeGramRightInverse (fderiv ℝ (F z.1 ∘ c z.1) z.2)) a.target)
    (hJ : ContDiffOn ℝ ∞ (fun z : X => (normalSpace (I := I) (F z.1) (c z.1 z.2)).subtypeL.comp
      (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2)) a.target)
    (hT : ContDiffOn ℝ ∞ (fun z : X => incrementsModeTransverseValue (F z.1) (c z.1) z.2) a.target)
    (hBR : ContDiffOn ℝ ∞ (fun z : X => fun k : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c z.1) z.2 0 k : V)) a.target)
    (hvf : ContDiffOn ℝ ∞ (fun z : X => (vf z.1 z.2 : V)) a.target)
    (hinput : ∀ z ∈ a.target, z ∈ tsupport (fun w : X => (vf w.1 w.2 : V)) → a.symm z ∈ K) :
    ContMDiffOn ((𝓘(ℝ,Pspace)).prod ((𝓘(ℝ,Ep)).prod I)) 𝓘(ℝ,V) ∞
      (fun z : Pspace × (Ep × M) =>
        round4PrescribedGlobalAmplitude imag label l F hF c vf tau length a z.1 z.2)
      (univ ×ˢ W) := by
  classical
  have hcolumn (q : Fin p) := (round4_prescribed_global_amplitude_smooth imag label l F hF c vf
    tau length a W K hW hK hKsource hchart hA hB hG hJ hT hBR hvf hinput (Pi.single q 1)).1
  have hterm (q : Fin p) :
      ContMDiffOn ((𝓘(ℝ,Pspace)).prod ((𝓘(ℝ,Ep)).prod I)) 𝓘(ℝ,V) ∞
        (fun z : Pspace × (Ep × M) => z.1 q •
          round4PrescribedGlobalAmplitude imag label l F hF c vf tau length a (Pi.single q 1) z.2)
        (univ ×ˢ W) := by
    have hp : ContMDiff ((𝓘(ℝ,Pspace)).prod ((𝓘(ℝ,Ep)).prod I)) 𝓘(ℝ,ℝ) ∞
        (fun z : Pspace × (Ep × M) => z.1 q) :=
      (ContinuousLinearMap.proj q : Pspace →L[ℝ] ℝ).contMDiff.comp contMDiff_fst
    exact hp.contMDiffOn.smul ((hcolumn q).comp contMDiffOn_snd (fun z hz => hz.2))
  apply (contMDiffOn_finsetSum (fun q _ => hterm q)).congr
  intro z hz
  exact congrFun (round4PrescribedGlobalAmplitude_columns imag label l F hF c vf tau length a
    hA hB hBR hvf z.1) z.2

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4PrescribedGlobalAmplitude_columns
#print axioms GlobalEmbedding.Continuation.round4_prescribed_global_parameter_joint_smooth
