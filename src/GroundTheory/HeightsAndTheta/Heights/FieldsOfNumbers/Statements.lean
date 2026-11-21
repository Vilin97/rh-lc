module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u v

section Objects

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

def relDim [Fintype K] (I : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) : WithBot (WithTop ℤ) :=
  WithBot.map (fun d : ℕ∞ => WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) d)
    (ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ I))

def EventuallyPoly (h : (K → ℤ) → ℤ) (p : MvPolynomial K ℚ) : Prop :=
  ∀ᶠ m in Filter.atTop, (h m : ℚ) = MvPolynomial.eval (fun k => (m k : ℚ)) p

def homFracDegZero (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) [P.IsPrime] :
    IntermediateField F (FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P)) :=
  IntermediateField.adjoin F {x | ∃ (b : K → ℕ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι), IsMultiHomog f b ∧
    IsMultiHomog g b ∧ g ∉ P ∧
    x = algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P) _ (Ideal.Quotient.mk P f) /
      algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P) _ (Ideal.Quotient.mk P g)}

open Classical in

def resDeg (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) : ℕ :=
  if h : P.IsPrime then haveI := h; Module.finrank F (homFracDegZero P) else 0

open Classical in

def topCycle [Fintype K] (I : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) (n : ℕ) (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) : ℤ :=
  if h : W ∈ I.minimalPrimes ∧ IsRelevant W ∧ relDim W = n then
    haveI : W.IsPrime := h.1.1.1
    ((multAt I W).toNat : ℤ)
  else 0

end Objects

section Blocks

variable {K K' : Type*} {F : Type*} [Field F]

def blockIncl (j : K ↪ K') (ι' : K' → Type*) : (Σ k, ι' (j k)) → (Σ k', ι' k') :=
  fun v => ⟨j v.1, v.2⟩

def pullDeg (j : K ↪ K') (b : K → ℤ) : K' → ℤ :=
  Function.extend j b 0

def contractPrime (j : K ↪ K') {ι' : K' → Type*} (P' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι')) :
    Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F (fun k => ι' (j k))) :=
  P'.comap (rename (blockIncl j ι'))

instance contractPrime.isPrime (j : K ↪ K') {ι' : K' → Type*} (P' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι'))
    [P'.IsPrime] : (contractPrime j P').IsPrime :=
  Ideal.comap_isPrime _ _

def contractQuot (j : K ↪ K') {ι' : K' → Type*} (P' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι')) :
    (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F (fun k => ι' (j k)) ⧸ contractPrime j P') →ₐ[F] (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι' ⧸ P') :=
  Ideal.quotientMapₐ P' (rename (blockIncl j ι')) le_rfl

def contractFracMap (j : K ↪ K') {ι' : K' → Type*} (P' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι')) [P'.IsPrime] :
    FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F (fun k => ι' (j k)) ⧸ contractPrime j P') →ₐ[F]
      FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι' ⧸ P') :=
  IsFractionRing.liftAlgHom
    (g := (IsScalarTower.toAlgHom F (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι' ⧸ P') (FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι' ⧸ P'))).comp
      (contractQuot j P'))
    ((IsFractionRing.injective (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι' ⧸ P') (FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι' ⧸ P'))).comp
      (Ideal.quotientMap_injective))

def relDeg [DecidableEq K] [DecidableEq K'] (j : K ↪ K') {ι' : K' → Type*}
    (P' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι')) [P'.IsPrime] : ℕ :=
  IntermediateField.relfinrank ((homFracDegZero (contractPrime j P')).map (contractFracMap j P'))
    (homFracDegZero P')

end Blocks

def GradedFinite.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) (m : K → ℕ),
    FiniteDimensional F (gradedPiece I m) ∧
      hilbFn I (fun k => (m k : ℤ)) = Module.finrank F (gradedPiece I m)

def HilbExactDivide.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)), IsMultiHomogIdeal I →
    ∀ (c : K → ℕ) (s : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι), IsMultiHomog s c → ∀ m : K → ℤ,
      hilbFn I m - hilbFn (I.colon (Ideal.span {s})) (m - fun k => (c k : ℤ)) =
        hilbFn (I ⊔ Ideal.span {s}) m

def PolyOfDiffs.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (h : (K → ℤ) → ℤ) (d : ℕ),
    (∀ k, ∃ q : MvPolynomial K ℚ, (q = 0 ∨ q.totalDegree < d) ∧
      EventuallyPoly (diffStep (Pi.single k 1) h) q) →
    ∃ p : MvPolynomial K ℚ, p.totalDegree ≤ d ∧ EventuallyPoly h p

def HilbEventuallyPoly.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)), IsMultiHomogIdeal I →
    ∃ p : MvPolynomial K ℚ, EventuallyPoly (hilbFn I) p

def HilbDegreeBound.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)), IsMultiHomogIdeal I →
    (IsRelevant I → ∀ p : MvPolynomial K ℚ, EventuallyPoly (hilbFn I) p → p ≠ 0 →
        (p.totalDegree : WithBot (WithTop ℤ)) ≤ relDim I) ∧
      (¬ IsRelevant I → ∀ᶠ m in Filter.atTop, hilbFn I m = 0)

def MixedDiffConst.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)), IsMultiHomogIdeal I → IsRelevant I →
    ∀ n : ℕ, relDim I = n →
      (∀ bs : Fin n → K → ℤ, ∀ᶠ m in Filter.atTop, mixedDiff bs (hilbFn I) m = intNum F I bs) ∧
      (∀ r : ℕ, n < r → ∀ bs : Fin r → K → ℤ,
        ∀ᶠ m in Filter.atTop, mixedDiff bs (hilbFn I) m = 0)

def IntNumSymm.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) (n : ℕ) (bs : Fin n → K → ℤ)
    (σ : Equiv.Perm (Fin n)), intNum F I (bs ∘ σ) = intNum F I bs

def IntNumAdd.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)), IsMultiHomogIdeal I → IsRelevant I →
    ∀ n : ℕ, relDim I = n → ∀ (bs : Fin n → K → ℤ) (i : Fin n) (b b' : K → ℤ),
      intNum F I (Function.update bs i (b + b')) =
        intNum F I (Function.update bs i b) + intNum F I (Function.update bs i b')

def IntNumZeroSlot.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)),
    (∀ (n : ℕ) (bs : Fin n → K → ℤ) (i : Fin n), bs i = 0 → intNum F I bs = 0) ∧
      (IsMultiHomogIdeal I → ∀ (n : ℕ) (bs : Fin n → K → ℤ), relDim I < n → intNum F I bs = 0)

def IntNumBase.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) (hP : IsMultiProjPrime P), relDim P = 0 →
    haveI := hP.isPrime
    FiniteDimensional F (homFracDegZero P) ∧
      intNum F P (n := 0) ![] = Module.finrank F (homFracDegZero P)

open Classical in

def PrimeFiltration.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)), IsMultiHomogIdeal I →
    ∃ (r : ℕ) (Q : Fin r → Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) (c : Fin r → K → ℕ),
      (∀ j, (Q j).IsPrime ∧ IsMultiHomogIdeal (Q j) ∧ I ≤ Q j) ∧
      (∀ᶠ m in Filter.atTop, hilbFn I m = ∑ j, hilbFn (Q j) (m - fun k => (c j k : ℤ))) ∧
      (∀ W (hW : W ∈ I.minimalPrimes), IsRelevant W → relDim W = relDim I →
        haveI : W.IsPrime := hW.1.1
        ((((Finset.univ.filter fun j => Q j = W).card : ℕ) : ℕ∞) = multAt I W)) ∧
      (∀ j, ¬ IsRelevant (Q j) ∨ relDim (Q j) < relDim I ∨
        (Q j ∈ I.minimalPrimes ∧ relDim (Q j) = relDim I))

def MultEqualsCoeff.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)), IsMultiHomogIdeal I → IsRelevant I →
    ∀ n : ℕ, relDim I = n → ∀ bs : Fin n → K → ℤ,
      intNum F I bs = cycEval (fun W => intNum F W bs) (topCycle I n)

def CutRegular.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)), IsMultiProjPrime P →
    ∀ n : ℕ, relDim P = (n + 1 : ℕ) → ∀ (c : K → ℕ) (s : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι), IsMultiHomog s c → s ∉ P →
    ∀ bs : Fin n → K → ℤ,
      intNum F P (Fin.snoc (α := fun _ => K → ℤ) bs (fun k => (c k : ℤ))) =
        cycEval (fun W => intNum F W bs) ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) W : ℤ)))

def CutRational.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)), IsMultiProjPrime P →
    ∀ n : ℕ, relDim P = (n + 1 : ℕ) → ∀ (bf bg : K → ℕ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι),
    IsMultiHomog f bf → IsMultiHomog g bg → f ∉ P → g ∉ P → ∀ bs : Fin n → K → ℤ,
      intNum F P (Fin.snoc (α := fun _ => K → ℤ) bs (fun k => (bf k : ℤ) - bg k)) =
        cycEval (fun W => intNum F W bs) (ratDiv P f g)

def ExistsForm.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)), IsMultiProjPrime P → ∀ b : K → ℤ,
    ∃ (bf bg : K → ℕ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι), IsMultiHomog f bf ∧ IsMultiHomog g bg ∧ f ∉ P ∧
      g ∉ P ∧ (fun k => (bf k : ℤ) - bg k) = b

structure IsIntersectionTheory {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*}
    (F : Type*) [Field F] (N : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) → (n : ℕ) → (Fin n → K → ℤ) → ℤ) : Prop where
  base : ∀ P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι), IsMultiProjPrime P → relDim P = 0 → N P 0 ![] = resDeg P
  cut : ∀ (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) (n : ℕ), IsMultiProjPrime P → relDim P = (n + 1 : ℕ) →
    ∀ (bf bg : K → ℕ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι), IsMultiHomog f bf → IsMultiHomog g bg → f ∉ P → g ∉ P →
    ∀ bs : Fin n → K → ℤ,
      N P (n + 1) (Fin.snoc (α := fun _ => K → ℤ) bs (fun k => (bf k : ℤ) - bg k)) =
        cycEval (fun W => N W n bs) (ratDiv P f g)

def IntNumUnique.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (N : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) → (n : ℕ) → (Fin n → K → ℤ) → ℤ),
    IsIntersectionTheory F N → ∀ P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι), IsMultiProjPrime P →
    ∀ n : ℕ, relDim P = n → ∀ bs : Fin n → K → ℤ, N P n bs = intNum F P bs

def IntNumBaseChange.Statement : Prop :=
  (∀ (F : Type u) [Field F] (F' : Type v) [Field F'] [Algebra F F'] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)),
    (∀ m, hilbFn (I.map (MvPolynomial.map (algebraMap F F'))) m = hilbFn I m) ∧
      ∀ (n : ℕ) (bs : Fin n → K → ℤ),
        intNum F' (I.map (MvPolynomial.map (algebraMap F F'))) bs = intNum F I bs) ∧
  (∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)), IsMultiProjPrime P →
    IsMultiProjPrime (P.map (MvPolynomial.map (algebraMap F (RatFunc F)))))

def ProjectionFormulaContracted.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι')), IsMultiProjPrime P' → ∀ n : ℕ, relDim P' = n →
    relDim (contractPrime j P') < n → ∀ bs : Fin n → K → ℤ,
      intNum F P' (fun i => pullDeg j (bs i)) = 0

def ProjectionFormulaDegree.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι')) (hP' : IsMultiProjPrime P'), ∀ n : ℕ, relDim P' = n →
    relDim (contractPrime j P') = n → ∀ bs : Fin n → K → ℤ,
      haveI := hP'.isPrime
      (homFracDegZero (contractPrime j P')).map (contractFracMap j P') ≤ homFracDegZero P' ∧
        intNum F P' (fun i => pullDeg j (bs i)) =
          relDeg j P' * intNum F (contractPrime j P') bs

end

end GroundTheory.Heights₂.Heights.FieldNumbers
