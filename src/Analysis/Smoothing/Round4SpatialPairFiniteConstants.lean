import Smoothing.Round4SpatialClosedPairTail
import Smoothing.Round4SpatialClosedPairGain
import Smoothing.Round4PreparedPairFiniteGeometry

/-!
# Finite raw-geometry constants for literal spatial-two-jet (6.4)

Every raw cutoff and coordinate-transition profile is read only through m+2.
The same constants apply to the existing actual map and native tensor, and
are selected before either chart family, both fields, and all small scales.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline MeasureTheory
open scoped BigOperators
namespace GlobalEmbedding.Continuation

def round4SpatialPairTailConstant (n d q : ℕ) (rho : ℝ) (hrho : 0 < rho)
    (BS₀ TS BP₀ TP : ℕ → ℝ) (Ds Dp m r : ℕ) : ℝ :=
  let mu := (volume : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)))
  let kappa := normalizedSmoothingBase mu rho hrho
  let Bc := round4ProductCutoffProfile BS₀ TS BP₀ TP Ds Dp
  let T := fun j => max (TP j) (TS j)
  let D := (Ds+1)*(Dp+1)
  max (parameterModelSmoothingTailConstant
    (EuclideanSpace.equiv (Fin d) ℝ) (EuclideanSpace.equiv (Fin n) ℝ)
    (EuclideanSpace.equiv (Fin q) ℝ) mu kappa
    (parameterSpatialTransferCoefficient (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin q)) Bc T) T D m r)
    (modelTensorSmoothingTailConstant n (parameterTensorModelEquiv n d) mu kappa
      Bc T (fun j => T (j+1)) D 0 m r)

def round4SpatialPairGainConstant (n d q : ℕ) (rho : ℝ) (hrho : 0 < rho)
    (BS₀ TS BP₀ TP : ℕ → ℝ) (Ds Dp m r : ℕ) : ℝ :=
  let mu := (volume : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)))
  let K := fixedSmoothingKernel mu rho hrho r
  let Bc := round4ProductCutoffProfile BS₀ TS BP₀ TP Ds Dp
  let T := fun j => max (TP j) (TS j)
  let D := (Ds+1)*(Dp+1)
  max (parameterModelSmoothingGainConstant
    (EuclideanSpace.equiv (Fin d) ℝ) (EuclideanSpace.equiv (Fin n) ℝ)
    (EuclideanSpace.equiv (Fin q) ℝ) mu K
    (parameterSpatialTransferCoefficient (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin q)) Bc T) T D m)
    (modelTensorSmoothingGainConstant n (parameterTensorModelEquiv n d) mu K
      Bc T (fun j => T (j+1)) D 0 m)

def round4SpatialPairConstant (n d q : ℕ) (rho : ℝ) (hrho : 0 < rho)
    (BS₀ TS BP₀ TP : ℕ → ℝ) (Ds Dp m r : ℕ) : ℝ :=
  max (round4SpatialPairTailConstant n d q rho hrho BS₀ TS BP₀ TP Ds Dp m r)
    (round4SpatialPairGainConstant n d q rho hrho BS₀ TS BP₀ TP Ds Dp m r)

theorem round4SpatialPairTailConstant_congr_prefix
    (n d q : ℕ) (rho : ℝ) (hrho : 0 < rho) (Ds Dp m r : ℕ)
    {BS₁ BS₂ TS₁ TS₂ BP₁ BP₂ TP₁ TP₂ : ℕ → ℝ}
    (hBS : ∀ a ≤ m+2, BS₁ a = BS₂ a) (hTS : ∀ a ≤ m+2, TS₁ a = TS₂ a)
    (hBP : ∀ a ≤ m+2, BP₁ a = BP₂ a) (hTP : ∀ a ≤ m+2, TP₁ a = TP₂ a) :
    round4SpatialPairTailConstant n d q rho hrho BS₁ TS₁ BP₁ TP₁ Ds Dp m r =
      round4SpatialPairTailConstant n d q rho hrho BS₂ TS₂ BP₂ TP₂ Ds Dp m r := by
  apply parameterPairTailConstant_congr_prefix
  · intro a ha
    exact round4ProductCutoffProfile_congr_prefix Ds Dp a
      (fun k hk => hBS k (hk.trans ha)) (fun k hk => hTS k (hk.trans ha))
      (fun k hk => hBP k (hk.trans ha)) (fun k hk => hTP k (hk.trans ha))
  · intro a ha
    rw [hTP a ha,hTS a ha]

theorem round4SpatialPairGainConstant_congr_prefix
    (n d q : ℕ) (rho : ℝ) (hrho : 0 < rho) (Ds Dp m r : ℕ)
    {BS₁ BS₂ TS₁ TS₂ BP₁ BP₂ TP₁ TP₂ : ℕ → ℝ}
    (hBS : ∀ a ≤ m+2, BS₁ a = BS₂ a) (hTS : ∀ a ≤ m+2, TS₁ a = TS₂ a)
    (hBP : ∀ a ≤ m+2, BP₁ a = BP₂ a) (hTP : ∀ a ≤ m+2, TP₁ a = TP₂ a) :
    round4SpatialPairGainConstant n d q rho hrho BS₁ TS₁ BP₁ TP₁ Ds Dp m r =
      round4SpatialPairGainConstant n d q rho hrho BS₂ TS₂ BP₂ TP₂ Ds Dp m r := by
  have hBc (a : ℕ) (ha : a ≤ m+2) := round4ProductCutoffProfile_congr_prefix Ds Dp a
    (fun k hk => hBS k (hk.trans ha)) (fun k hk => hTS k (hk.trans ha))
    (fun k hk => hBP k (hk.trans ha)) (fun k hk => hTP k (hk.trans ha))
  have hT (a : ℕ) (ha : a ≤ m+2) : max (TP₁ a) (TS₁ a) = max (TP₂ a) (TS₂ a) := by
    rw [hTP a ha,hTS a ha]
  unfold round4SpatialPairGainConstant
  dsimp only
  rw [parameterMapGainConstant_congr_prefix _ _ _ _ _ _ m hBc hT,
    round4TensorGainConstant_congr_prefix n _ _ _ _ m
      (fun a ha => hBc a (by omega)) (fun a ha => hT a (by omega))]

theorem round4SpatialPairConstant_congr_prefix
    (n d q : ℕ) (rho : ℝ) (hrho : 0 < rho) (Ds Dp m r : ℕ)
    {BS₁ BS₂ TS₁ TS₂ BP₁ BP₂ TP₁ TP₂ : ℕ → ℝ}
    (hBS : ∀ a ≤ m+2, BS₁ a = BS₂ a) (hTS : ∀ a ≤ m+2, TS₁ a = TS₂ a)
    (hBP : ∀ a ≤ m+2, BP₁ a = BP₂ a) (hTP : ∀ a ≤ m+2, TP₁ a = TP₂ a) :
    round4SpatialPairConstant n d q rho hrho BS₁ TS₁ BP₁ TP₁ Ds Dp m r =
      round4SpatialPairConstant n d q rho hrho BS₂ TS₂ BP₂ TP₂ Ds Dp m r := by
  unfold round4SpatialPairConstant
  rw [round4SpatialPairTailConstant_congr_prefix n d q rho hrho Ds Dp m r hBS hTS hBP hTP,
    round4SpatialPairGainConstant_congr_prefix n d q rho hrho Ds Dp m r hBS hTS hBP hTP]

#print axioms round4SpatialPairConstant_congr_prefix
end GlobalEmbedding.Continuation
