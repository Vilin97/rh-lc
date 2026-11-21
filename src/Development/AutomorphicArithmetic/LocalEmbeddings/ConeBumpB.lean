module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UAtMemIsoB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrablePowerNormCompact

@[expose] public section

noncomputable section

namespace GlobalTheory.ConeBumpB

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.VanishLoc (liftT)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Points

variable {n n₁ d d₁ : ℕ}

def uS (σ : E →ₐ[F] E) (H : Plane E n n₁) (H' : Plane E d d₁) (v : Pl F) (s : Fv F v ⊗[F] E) :
    Matrix (Fin n) (Fin d) (AE F E) :=
  cA σ (liftT v s) • Matrix.vecMulVec (incV F H.y) (incV F H'.x)

def yAt (H' : Plane E d d₁) (v : Pl F) (y : Fin n → Fv F v ⊗[F] E) : Matrix (Fin n) (Fin d) (AE F E) :=
  Matrix.vecMulVec (fun i => liftT v (y i)) (incV F H'.x)

def atV (v : Pl F) (x : Fin n → AE F E) : Fin n → Fv F v ⊗[F] E := fun i => compFin F E v (x i)

def pairV (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (v : Pl F) (x y : Fin n → Fv F v ⊗[F] E) : Fv F v ⊗[F] E :=
  x ⬝ᵥ (J.map (inclR (F := F) (Fv F v)) *ᵥ fun i => sigR (Fv F v) σ (y i))

theorem pairV_add_right (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (v : Pl F) (x y y' : Fin n → Fv F v ⊗[F] E) :
    pairV σ J v x (y + y') = pairV σ J v x y + pairV σ J v x y' := by
  have e : (fun i => sigR (Fv F v) σ ((y + y') i)) =
      (fun i => sigR (Fv F v) σ (y i)) + fun i => sigR (Fv F v) σ (y' i) := funext fun i => map_add _ _ _
  rw [pairV, pairV, pairV, e, Matrix.mulVec_add, dotProduct_add]

end Points

def four (v : Pl F) (ψ : AddChar (Fv F v) ℂ) [MeasurableSpace (Fv F v ⊗[F] E)] (m : Measure (Fv F v ⊗[F] E))
    (T : Fv F v ⊗[F] E → ℂ) (t : Fv F v ⊗[F] E) : ℂ :=
  ∫ s, T s * ψ (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (t * s)) ∂m

end GlobalTheory.ConeBumpB

end
