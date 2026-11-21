module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Defs

variable {K : Type*}

def DegLT (f : (K → ℤ) → ℤ) (n : ℕ) : Prop :=
  ∀ bs : Fin n → K → ℤ, ∀ᶠ m in Filter.atTop, mixedDiff bs f m = 0

def shiftFn (s : K → ℤ) (f : (K → ℤ) → ℤ) : (K → ℤ) → ℤ := fun m => f (m - s)

variable {ι : K → Type*}

open Classical in

def idealCycle {R : Type*} [CommRing R] (J W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) : ℤ :=
  if h : W ∈ J.minimalPrimes ∧ IsRelevant W then
    haveI : W.IsPrime := h.1.1.1
    ((multAt J W).toNat : ℤ)
  else 0

theorem divCycle_eq_idealCycle {R : Type*} [CommRing R] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) (f : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) :
    (fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f) W : ℤ)) = idealCycle (P ⊔ Ideal.span {f}) := rfl

variable [DecidableEq K]

def gradedPieceR {R : Type*} [CommRing R] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) (m : K → ℕ) :
    Submodule R (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι ⧸ P) :=
  (weightedHomogeneousSubmodule R (blockWeight ι) m).map (Ideal.Quotient.mkₐ R P).toLinearMap

end Defs

section FunctionsOnMultidegrees

def MixedDiffLinear.Statement : Prop :=
  ∀ (K : Type) (n : ℕ) (bs : Fin n → K → ℤ) (f g : (K → ℤ) → ℤ) (c : ℤ) (s b : K → ℤ),
    mixedDiff bs (f + g) = mixedDiff bs f + mixedDiff bs g ∧
    mixedDiff bs (c • f) = c • mixedDiff bs f ∧
    mixedDiff bs (shiftFn s f) = shiftFn s (mixedDiff bs f) ∧
    mixedDiff bs (diffStep b f) = diffStep b (mixedDiff bs f) ∧
    mixedDiff (Matrix.vecCons b bs) f = diffStep b (mixedDiff bs f)

def DegLTClosure.Statement : Prop :=
  ∀ (K : Type) (n : ℕ) (f g : (K → ℤ) → ℤ) (c : ℤ) (s : K → ℤ),
    (DegLT f n → DegLT g n → DegLT (f + g) n) ∧
    (DegLT f n → DegLT (c • f) n) ∧
    (DegLT f n → DegLT (shiftFn s f) n) ∧
    (DegLT f n → DegLT f (n + 1)) ∧
    (f =ᶠ[Filter.atTop] g → DegLT f n → DegLT g n)

def DiffStepExpansion.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (b : K → ℤ),
    ∃ l : List ((K × (K → ℤ)) × ℤ), ∀ f : (K → ℤ) → ℤ,
      diffStep b f = (l.map fun t => t.2 • shiftFn t.1.2 (diffStep (Pi.single t.1.1 1) f)).sum

def DegLTOfUnitSteps.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (n : ℕ) (f : (K → ℤ) → ℤ),
    (∀ k, DegLT (diffStep (Pi.single k 1) f) n) → DegLT f (n + 1)

def DegLTEventuallyConst.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (n : ℕ) (f : (K → ℤ) → ℤ), DegLT f (n + 1) →
    ∀ bs : Fin n → K → ℤ, ∃ c : ℤ, ∀ᶠ m in Filter.atTop, mixedDiff bs f m = c

def EventualValueFacts.Statement : Prop :=
  ∀ (K : Type) (f : (K → ℤ) → ℤ) (c : ℤ) (s : K → ℤ),
    ((∀ᶠ m in Filter.atTop, f m = c) → eventualValue f = c) ∧
    ((∀ᶠ m in Filter.atTop, f m = c) → ∀ᶠ m in Filter.atTop, shiftFn s f m = c)

end FunctionsOnMultidegrees

section HilbertFunctions

def HilbFnVanishBlock.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Q : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) (k : K),
    (∀ i, (X ⟨k, i⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) ∈ Q) → ∀ m : K → ℤ, 1 ≤ m k → hilbFn Q m = 0

def GradedPieceQuot.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) (m : K → ℕ),
    (Module.finrank F (gradedPiece I m) : ℤ) =
      Module.finrank F (weightedHomogeneousSubmodule F (blockWeight ι) m) -
        Module.finrank F ↥(weightedHomogeneousSubmodule F (blockWeight ι) m ⊓ I.restrictScalars F)

open Classical in

def CutPieces.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) (x : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) (e m : K → ℕ),
    IsMultiHomogIdeal I → IsMultiHomog x e → (∀ y, x * y ∈ I → y ∈ I) →
    (Module.finrank F ↥(weightedHomogeneousSubmodule F (blockWeight ι) m ⊓
        (I ⊔ Ideal.span {x}).restrictScalars F) : ℤ) =
      Module.finrank F ↥(weightedHomogeneousSubmodule F (blockWeight ι) m ⊓ I.restrictScalars F) +
        if e ≤ m then
          (Module.finrank F (weightedHomogeneousSubmodule F (blockWeight ι) (m - e)) : ℤ) -
            Module.finrank F ↥(weightedHomogeneousSubmodule F (blockWeight ι) (m - e) ⊓
              I.restrictScalars F)
        else 0

def HilbFnCut.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) (x : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) (e : K → ℕ),
    IsMultiHomogIdeal I → IsMultiHomog x e → (∀ y, x * y ∈ I → y ∈ I) →
    ∀ m : K → ℤ, hilbFn (I ⊔ Ideal.span {x}) m = hilbFn I m - hilbFn I (m - fun k => (e k : ℤ))

end HilbertFunctions

section Filtrations

def MultiHomogPrimeCriterion.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    (Q : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)), IsMultiHomogIdeal Q → Q ≠ ⊤ →
    (∀ (a b : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) (sa sb : K → ℕ), IsMultiHomog a sa → IsMultiHomog b sb → a * b ∈ Q →
      a ∈ Q ∨ b ∈ Q) →
    Q.IsPrime

def ColonMultiHomog.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [DecidableEq K] (ι : K → Type) (I : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι))
    (f : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) (s : K → ℕ), IsMultiHomogIdeal I → IsMultiHomog f s →
    IsMultiHomogIdeal (I.colon {f})

def AssociatedMultiHomogPrime.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (J : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)), IsMultiHomogIdeal J → J ≠ ⊤ →
    ∃ (f : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) (s : K → ℕ), IsMultiHomog f s ∧ f ∉ J ∧ (J.colon {f}).IsPrime

def FiltrationStepHilb.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (L : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) (f : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) (s : K → ℕ),
    IsMultiHomogIdeal L → IsMultiHomog f s →
    ∀ m : K → ℤ, hilbFn L m = hilbFn (L ⊔ Ideal.span {f}) m +
      hilbFn (L.colon {f}) (m - fun k => (s k : ℤ))

def FiltrationStepLength.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) (ι : K → Type) (L W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) [W.IsPrime]
    (f : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι),
    multAt L W = multAt (L ⊔ Ideal.span {f}) W + multAt (L.colon {f}) W

def PrimeFiltration.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (J : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)), IsMultiHomogIdeal J →
    ∃ l : List (Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) × (K → ℕ)),
      (∀ p ∈ l, p.1.IsPrime ∧ IsMultiHomogIdeal p.1 ∧ J ≤ p.1) ∧
      (∀ m : K → ℤ, hilbFn J m = (l.map fun p => hilbFn p.1 (m - fun k => (p.2 k : ℤ))).sum) ∧
      (∀ (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) [W.IsPrime], multAt J W = (l.map fun p => multAt p.1 W).sum)

open Classical in

def MultAtPrimeAtMinimal.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) (ι : K → Type) (J Q W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) [Q.IsPrime]
    [W.IsPrime], J ≤ Q → W ∈ J.minimalPrimes → multAt Q W = if Q = W then 1 else 0

end Filtrations

section Dimension

def DimStrictDrop.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] (Q Q' : Ideal A) [Q.IsPrime] [Q'.IsPrime], Q < Q' →
    ringKrullDim (A ⧸ Q') + 1 ≤ ringKrullDim (A ⧸ Q)

def BlockAdjoinPrime.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    (Q : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) (B : Set K), Q.IsPrime → IsMultiHomogIdeal Q →
    (Q ⊔ Ideal.span {p | ∃ v : Σ k, ι k, v.1 ∈ B ∧ p = X v}).IsPrime ∧
    ∀ v : Σ k, ι k, v.1 ∉ B →
      (X v ∈ Q ⊔ Ideal.span {p | ∃ w : Σ k, ι k, w.1 ∈ B ∧ p = X w} ↔ X v ∈ Q)

def RelevantDimGe.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    (Q : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)), IsMultiProjPrime Q →
    ((Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι ⧸ Q)

def HilbDegBound.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (n : ℕ) (Q : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)), Q.IsPrime → IsMultiHomogIdeal Q →
    ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ Q) < ((n + Fintype.card K : ℕ) : WithBot ℕ∞) → DegLT (hilbFn Q) n

def TopDimMinimal.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] (J Q : Ideal A) [Q.IsPrime] (N : ℕ), J ≤ Q →
    ringKrullDim (A ⧸ J) < ((N + 1 : ℕ) : WithBot ℕ∞) →
    ¬ ringKrullDim (A ⧸ Q) < ((N : ℕ) : WithBot ℕ∞) → Q ∈ J.minimalPrimes

end Dimension

section Numbers

def IntNumVanish.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (n : ℕ) (Q : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)), Q.IsPrime → IsMultiHomogIdeal Q →
    (¬ IsRelevant Q ∨ ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ Q) < ((n + Fintype.card K : ℕ) : WithBot ℕ∞)) →
    ∀ bs : Fin n → K → ℤ, intNum F Q bs = 0

def IntNumOfFiltration.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (n : ℕ) (J : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι))
    (l : List (Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) × (K → ℕ))), (∀ p ∈ l, DegLT (hilbFn p.1) (n + 1)) →
    (∀ m : K → ℤ, hilbFn J m = (l.map fun p => hilbFn p.1 (m - fun k => (p.2 k : ℤ))).sum) →
    ∀ bs : Fin n → K → ℤ, intNum F J bs = (l.map fun p => intNum F p.1 bs).sum

def IntNumAssoc.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (n : ℕ) (J : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)), IsMultiHomogIdeal J →
    ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ J) < ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ bs : Fin n → K → ℤ, intNum F J bs = cycEval (fun W => intNum F W bs) (idealCycle J)

def CutByForm.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (n : ℕ) (G : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)), G.IsPrime → IsMultiHomogIdeal G →
    ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ G) < ((n + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (s : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) (c : K → ℕ), IsMultiHomog s c → s ∉ G →
    ∀ bs : Fin n → K → ℤ,
      intNum F G (Matrix.vecCons (fun k => (c k : ℤ)) bs) =
        cycEval (fun W => intNum F W bs) ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle G s) W : ℤ)))

end Numbers

section Fibres

def GradedPieceFree.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)),
    (∀ x, C ϖ * x ∈ P → x ∈ P) → ∀ m : K → ℕ,
      Module.Free O (gradedPieceR P m) ∧ Module.Finite O (gradedPieceR P m)

def SpecialPieceRank.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)),
    IsMultiHomogIdeal P → (∀ x, C ϖ * x ∈ P → x ∈ P) → ∀ m : K → ℕ,
      Module.finrank (IsLocalRing.ResidueField O) (gradedPiece (specialIdeal P) m) =
        Module.finrank O (gradedPieceR P m)

def GenericPieceRank.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)),
    IsMultiHomogIdeal P → ∀ m : K → ℕ,
      Module.finrank (FractionRing O) (gradedPiece (genFib P) m) = Module.finrank O (gradedPieceR P m)

def SpecialIdealMultiHomog.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [DecidableEq K]
    (ι : K → Type) (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)), IsMultiHomogIdeal P → IsMultiHomogIdeal (specialIdeal P)

def SpecialIdealCorresp.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)), W.IsPrime → (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∈ W →
    (specialIdeal W).IsPrime ∧
    (W ∈ (P ⊔ Ideal.span {C ϖ}).minimalPrimes ↔ specialIdeal W ∈ (specialIdeal P).minimalPrimes) ∧
    (IsRelevant W ↔ IsRelevant (specialIdeal W)) ∧
    ∀ W' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), W'.IsPrime → (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∈ W' →
      specialIdeal W' = specialIdeal W → W' = W

def SpecialIdealSurj.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (V : Ideal (MRing ι (IsLocalRing.ResidueField O))), V.IsPrime →
    ∃ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), W.IsPrime ∧ (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∈ W ∧ specialIdeal W = V

def SpecialMultAt.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) [W.IsPrime], (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∈ W →
    ∀ [(specialIdeal W).IsPrime],
      multAt (P ⊔ Ideal.span {C ϖ}) W = multAt (specialIdeal P) (specialIdeal W)

def SpecialCycleEval.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (n : Ideal (MRing ι (IsLocalRing.ResidueField O)) → ℤ),
    cycEval (fun W => n (specialIdeal W)) ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (C ϖ)) W : ℤ))) = cycEval n (idealCycle (specialIdeal P))

def SpecialDimBound.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (d : ℕ), IsModelOver P d →
    ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P) <
      ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞)

end Fibres

section Examples

theorem mixedDiff_zero {K : Type*} {n : ℕ} (bs : Fin n → K → ℤ) :
    mixedDiff bs (0 : (K → ℤ) → ℤ) = 0 := by
  unfold mixedDiff
  induction List.ofFn bs with
  | nil => rfl
  | cons b l ih =>
    rw [List.foldr_cons, ih]
    funext m
    simp [diffStep]

theorem degLT_zero {K : Type*} (n : ℕ) : DegLT (0 : (K → ℤ) → ℤ) n := fun bs =>
  Filter.Eventually.of_forall fun m => by rw [mixedDiff_zero]; rfl

theorem hilbFn_top {F : Type*} [Field F] {K : Type*} [DecidableEq K] {ι : K → Type*}
    (m : K → ℤ) : hilbFn (⊤ : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) m = 0 := by
  unfold hilbFn
  split_ifs
  · have : Subsingleton (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ (⊤ : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι))) :=
      Ideal.Quotient.subsingleton_iff.mpr rfl
    rw [Module.finrank_zero_of_subsingleton, Nat.cast_zero]
  · rfl

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
