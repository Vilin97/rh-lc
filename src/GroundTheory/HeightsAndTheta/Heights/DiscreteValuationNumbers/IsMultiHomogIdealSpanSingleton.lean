module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Cartier
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Defs

variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def IsEffectiveVertical (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (ϖ : O) (b : K → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) : Prop :=
  IsVerticalDivisor P ϖ b f g ∧ ∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), W.IsPrime → P ≤ W → IsRelevant W →
    ∃ u v : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι, u ∉ W ∧ u * f - v * g ∈ P


def cutIdentity (ϖ : O) (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (b : K → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) (c : K → ℕ)
    (s : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) {d : ℕ} (L : Fin d → K → ℤ) : Prop :=
  cycEval (fun G => vNum G (Matrix.vecCons (fun k => (c k : ℤ)) L)) (ratDiv P f g) =
    cycEval (fun W => if (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∈ W then vNum W (Matrix.vecCons b L)
        else cycEval (fun G => vNum G L) (ratDiv W f g)) ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) W : ℤ)))

end Defs

section Lemmas

def DivCycleMul.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) (x y : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι), P.IsPrime → x ∉ P → y ∉ P →
    (fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (x * y)) W : ℤ)) = divCycle P x + ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P y) def : ℤ) DivCycleFiniteSupport.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) (f : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι),
    (Function.support ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f) W : ℤ)))).Finite

def SupSpanMultiHomog.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [DecidableEq K] (ι : K → Type) (I : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι))
    (x : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) (e : K → ℕ), IsMultiHomogIdeal I → IsMultiHomog x e →
    IsMultiHomogIdeal (I ⊔ Ideal.span {x})

def MinimalPrimeMultiHomog.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    (J W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)), IsMultiHomogIdeal J → W ∈ J.minimalPrimes → IsMultiHomogIdeal W

def IntNumAddFirst.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (n : ℕ) (G : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)), G.IsPrime → IsMultiHomogIdeal G →
    ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ G) < ((n + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (b₁ b₂ : K → ℤ) (L : Fin n → K → ℤ),
      intNum F G (Matrix.vecCons (b₁ + b₂) L) =
        intNum F G (Matrix.vecCons b₁ L) + intNum F G (Matrix.vecCons b₂ L)

def SpecialQuotDim.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)), (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∈ W →
    ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) =
      ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ W)

def GenericDimBound.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)),
    IsMultiProjPrime P → P.comap (C : O →+* ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) = ⊥ →
    ringKrullDim (MRing ι (FractionRing O) ⧸ genFib P) + 1 ≤ ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ P)

def GenericFibProps.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)),
    IsMultiProjPrime P → P.comap (C : O →+* ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) = ⊥ →
    (genFib P).IsPrime ∧ IsMultiHomogIdeal (genFib P) ∧
    ∀ (s : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) (c : K → ℕ), IsMultiHomog s c → s ∉ P →
      IsMultiHomog (MvPolynomial.map (algebraMap O (FractionRing O)) s) c ∧
        MvPolynomial.map (algebraMap O (FractionRing O)) s ∉ genFib P


def GenericCycleCorresp.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (s : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), P.IsPrime →
    P.comap (C : O →+* ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) = ⊥ → s ∉ P →
    ∀ n : Ideal (MRing ι (FractionRing O)) → ℤ,
      cycEval (fun W => if (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∈ W then 0 else n (genFib W)) ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) W : ℤ))) =
        cycEval n ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (genFib P) (MvPolynomial.map (algebraMap O (FractionRing O)) s)) W : ℤ)))

def ConservationOfNumberLE.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (d : ℕ), IsMultiProjPrime P →
    P.comap (C : O →+* ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) = ⊥ →
    ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ P) ≤ ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ a : Fin d → K → ℤ, cycEval (fun W => vNum W a) ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (C ϖ)) W : ℤ))) = gNum P a

def UniformiserCase.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (c : K → ℕ) (s : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog s c → s ∉ P →
    ∀ L : Fin d → K → ℤ, cutIdentity ϖ P 0 (C ϖ) 1 c s L

def ShiftByUniformiser.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsVerticalDivisor P ϖ b f g →
    ∀ (c : K → ℕ) (s : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog s c → s ∉ P →
    (∀ H, ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) H : ℤ) ≠ 0 → (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∉ H → IsVerticalDivisor H ϖ b f g) →
    ∀ (L : Fin d → K → ℤ) (n : ℕ),
      cutIdentity ϖ P b (C ϖ ^ n * f) g c s L → cutIdentity ϖ P 0 (C ϖ) 1 c s L →
        cutIdentity ϖ P b f g c s L

def EffectiveShift.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (e : ℕ), IsModelOver P e →
    ∀ (b : K → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsVerticalDivisor P ϖ b f g →
    ∃ n : ℕ, IsEffectiveVertical P ϖ b (C ϖ ^ n * f) g

def EffectiveCase.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog s c → s ∉ P →
    (∀ H, ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) H : ℤ) ≠ 0 → (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∉ H → IsVerticalDivisor H ϖ b f g) →
    ∀ L : Fin d → K → ℤ, cutIdentity ϖ P b f g c s L

def Representative.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (b : K → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiProjPrime P →
    IsVerticalDivisor P ϖ b f g → ∀ T : Finset (Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)),
    (∀ H ∈ T, IsMultiProjPrime H ∧ P ≤ H ∧ (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∉ H ∧
      ∃ h : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι, h ∉ P ∧ H ∈ (P ⊔ Ideal.span {h}).minimalPrimes) →
    ∃ f₁ g₁ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι, IsVerticalDivisor P ϖ b f₁ g₁ ∧ ratDiv P f₁ g₁ = ratDiv P f g ∧
      ∀ H ∈ T, IsVerticalDivisor H ϖ b f₁ g₁

end Lemmas

section Examples

theorem isMultiHomogIdeal_span_singleton {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*}
    [CommRing R] {x : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι} {e : K → ℕ} (hx : IsMultiHomog x e) :
    IsMultiHomogIdeal (Ideal.span {x}) := by
  classical
  letI := MvPolynomial.weightedGradedAlgebra R (blockWeight ι)
  have h : (Ideal.span {x}).IsHomogeneous (weightedHomogeneousSubmodule R (blockWeight ι)) :=
    Ideal.homogeneous_span _ _ (by
      rintro y rfl
      exact ⟨e, hx⟩)
  intro f hf b
  exact MvPolynomial.weightedHomogeneousComponent_mem_of_mem R (blockWeight ι) h hf b

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
