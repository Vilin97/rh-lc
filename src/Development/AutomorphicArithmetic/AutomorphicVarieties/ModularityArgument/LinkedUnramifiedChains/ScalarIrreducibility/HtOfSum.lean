module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.HasObs
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IsInternalCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocFlat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.CmOfRegularLocal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.FlatAss
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FlipTwoThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.HtPres

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.FlatHt

section

@[expose] public section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

theorem UpperTheory.V.J.flatHt :
    ∀ (A R : Type) [CommRing A] [CommRing R] [IsNoetherianRing A] [IsNoetherianRing R] (ι : A →+* R), ι.Flat → ∀ (q : Ideal A) (Q : Ideal R),
        Q.IsPrime → Q.comap ι = q → Q ∈ (q.map ι).minimalPrimes → Q.height = q.height := by
  intro A R _ _ _ _ ι hι q Q hQ hcomap hmin
  letI : Algebra A R := ι.toAlgebra
  haveI : Module.Flat A R := hι
  haveI : Algebra.HasGoingDown A R := Algebra.HasGoingDown.of_flat
  haveI : q.IsPrime := hcomap ▸ Ideal.comap_isPrime ι Q
  haveI : Q.LiesOver q := ⟨hcomap.symm⟩
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown q Q]
  suffices h0 : (Q.map (Ideal.Quotient.mk (q.map (algebraMap A R)))).height = 0 by
    rw [h0, add_zero]
  have hJQ : q.map (algebraMap A R) ≤ Q := hmin.1.2
  have hker : RingHom.ker (Ideal.Quotient.mk (q.map (algebraMap A R))) ≤ Q := by
    rw [Ideal.mk_ker]
    exact hJQ
  haveI : (Q.map (Ideal.Quotient.mk (q.map (algebraMap A R)))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  rw [Ideal.height_eq_zero_iff]
  refine ⟨⟨inferInstance, bot_le⟩, ?_⟩
  rintro K ⟨hK, -⟩ hKQ
  have hle : K.comap (Ideal.Quotient.mk (q.map (algebraMap A R))) ≤ Q := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp (hKQ hx)
    have hd : y - x ∈ q.map (algebraMap A R) := Ideal.Quotient.eq.mp hxy
    have hx' : x = y - (y - x) := by ring
    rw [hx']
    exact Q.sub_mem hy (hJQ hd)
  have hc : Q ≤ K.comap (Ideal.Quotient.mk (q.map (algebraMap A R))) := by
    refine hmin.2 ⟨Ideal.comap_isPrime _ K, ?_⟩ hle
    intro x hx
    have hx2 : x ∈ q.map (algebraMap A R) := hx
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx2]
    exact K.zero_mem
  exact Ideal.map_le_iff_le_comap.mpr hc
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.HtOfSum

section

@[expose] public section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

private theorem ht_of_sum {h : ℕ∞} {N : ℕ} {D : WithBot ℕ∞} (hD : D = 1)
    (e : (h : WithBot ℕ∞) + D = (N + 1 : ℕ)) : h = N := by
  subst hD
  have e2 : ((h + 1 : ℕ∞) : WithBot ℕ∞) = (((N + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    rw [WithBot.coe_add, WithBot.coe_one, WithBot.coe_natCast]
    exact e
  have e3 : h + 1 = ((N + 1 : ℕ) : ℕ∞) := WithBot.coe_injective e2
  induction h using ENat.recTopCoe with
  | top =>
    rw [top_add] at e3
    exact absurd e3.symm (ENat.coe_ne_top _)
  | coe k =>
    norm_cast at e3 ⊢
    omega

private theorem le_of_add {a : ℕ∞} {b c : ℕ} (h : ((c + b : ℕ) : ℕ∞) ≤ a + b) : (c : ℕ∞) ≤ a := by
  induction a using ENat.recTopCoe with
  | top => exact le_top
  | coe k =>
    norm_cast at h ⊢
    omega

theorem UpperTheory.V.J.htLow :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (F : Fr.Frame l (ResidueField c.O)) (C₀ n : ℕ), F.Ok C₀ → (n = 2 ∨ n = 3) →
        ∀ (S : Fr.Space c.O F n), ∀ (q x : Ideal S.A) (L : S.Loc x) (Q : Ideal L.R), Over S L q Q →
          ((n * F.d + 1 : ℕ) : ℕ∞) ≤ q.height ∧ (Q.height ≤ ((n * F.d + 1 : ℕ) : ℕ∞) → ∀ P ∈ associatedPrimes S.A S.A, P ≤ q → P ∈ minimalPrimes S.A) := by
  intro l _ c _ F C₀ n hF hn S q x L Q hO
  obtain ⟨hQ, him, hmin, hdim⟩ := hO
  obtain ⟨N, N', p, f, hN, hp, hker⟩ := Fr.pres hF hn S x L
  obtain ⟨hfl, -, -⟩ := Fr.loc_flat hF hn S x L
  have hA : IsNoetherianRing S.A := (Fr.gr_A hF hn S).2.2.2.2.2.1
  have hR : IsNoetherianRing L.R := inferInstance
  obtain ⟨h1, h2⟩ := htPres L.O' N N' L.R p f hp hker Q hQ
  have hc : (Ideal.comap p Q).height = N := ht_of_sum hdim h1
  have hfh : Q.height = q.height := flatHt S.A L.R L.ι hfl q Q hQ him hmin
  have hlow : ((n * F.d + 1 : ℕ) : ℕ∞) ≤ Q.height := by
    apply le_of_add (b := N')
    rw [Nat.add_comm, ← hN, ← hc]
    exact h2
  refine ⟨hfh ▸ hlow, fun hle P hP hPq => ?_⟩
  have hu : Q.height + N' ≤ (Ideal.comap p Q).height := by
    rw [hc, hN, Nat.cast_add, add_comm (N' : ℕ∞)]
    exact add_le_add hle le_rfl
  refine flatAss S.A L.R L.ι hfl Q hQ (unmix L.O' N N' L.R p f hp hker Q hQ hu) P hP ?_
  change P ≤ L.im Q
  rw [him]
  exact hPq
end
end
