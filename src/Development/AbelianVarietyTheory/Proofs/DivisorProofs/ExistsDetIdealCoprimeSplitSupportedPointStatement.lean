module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.Divisors.RealisedChainTorusEq
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelSpanOverClasses
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.IndefiniteTreeX
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeIntegerInIdeal

section

@[expose] public section

open NumberField IsDedekindDomain

namespace GlobalTheory.NormCoprime

theorem coprime_absNorm_of_sup {K : Type} [Field K] [NumberField K] (p : ℕ) (hp : p.Prime)
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (h : I ⊔ Ideal.span {((p : ℕ) : 𝓞 K)} = ⊤) : Nat.Coprime (Ideal.absNorm I) p := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  have := Ideal.finiteQuotientOfFreeOfNeBot I hI
  let _ : Fintype (𝓞 K ⧸ I) := Fintype.ofFinite _
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card] at hdvd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card p hdvd
  have h1 : (1 : 𝓞 K) ∈ I ⊔ Ideal.span {((p : ℕ) : 𝓞 K)} := by rw [h]; trivial
  obtain ⟨i, hi, r, hr, hir⟩ := Submodule.mem_sup.mp h1
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hr
  have hpx : (p : ℕ) • x = 0 := by rw [← hx]; exact addOrderOf_nsmul_eq_zero x
  have hq : (Ideal.Quotient.mk I i) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hi
  have hx0 : x = 0 := by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    have e0 : y = i * y + t * (((p : ℕ) : 𝓞 K) * y) := by linear_combination (-(y)) * hir
    have e : Ideal.Quotient.mk I y = Ideal.Quotient.mk I i * Ideal.Quotient.mk I y +
        Ideal.Quotient.mk I t * ((p : ℕ) • Ideal.Quotient.mk I y) := by
      rw [nsmul_eq_mul, ← map_natCast (Ideal.Quotient.mk I) p, ← map_mul, ← map_mul, ← map_mul, ← map_add (f := _), ← e0]
    rw [e, hpx, mul_zero, add_zero, hq, zero_mul]
  rw [hx0, addOrderOf_zero] at hx
  exact hp.one_lt.ne hx

end GlobalTheory.NormCoprime
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetIdealCoprimeSplitSupportedPoint

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

namespace GlobalTheory.DetIdealPrime

theorem exists_ideal_coprime : ∀ (D : D7) (V : HSp D), HSpace.gram V = 1 → Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∀ (h : GA D V) (e : AE D) (P : Finset (HeightOneSpectrum (𝓞 D.host.E))) (y : (AE D)ˣ), IsIdemSum e P → SuppAt e V h → IsDetAt e V h y → ∀ (b : ℕ), (∀ Q ∈ P, (b : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (c : (AE D)ˣ →* Circle) (ψ : Formalism.L2.Host.HChar D.host.E), ChrEq c ψ → (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (b : 𝓞 D.host.E) ∉ Q.asIdeal → ψ.UnrAt Q) → (∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q → ∀ k : D.host.Fˣ, ψ.resFin (Q.under (𝓞 D.host.F)) k = 1) → ∀ (Λ : GenLat D.host.E V.rank), (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat V (fin V h)) → ∀ p : ℕ, p.Prime → Λ.TrivAt p → ∃ cc : Ideal (𝓞 D.host.E), cc ≠ ⊥ ∧ cc ⊔ Ideal.span {(b : 𝓞 D.host.E)} = ⊤ ∧ Nat.Coprime (Ideal.absNorm cc) p ∧ ((c y : Circle) : ℂ) = ((ψ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : ℂˣ) : ℂ) := by
  intro D V hg hL h e P y he hs hy b hb c ψ hc hu hr Λ hΛ p hp hT
  obtain ⟨cc, c0, c1, c2, c3, c4⟩ := GlobalTheory.ClassScalarValue.exists_ideal V hg hL h e P y he hs hy b hb c ψ hc hu hr
  refine ⟨cc, c0, c2, ?_, c4⟩
  refine GlobalTheory.NormCoprime.coprime_absNorm_of_sup p hp c0 ?_
  obtain ⟨k, hk, -, hk2⟩ := hT
  have hdet : ((k : D.host.E) ^ V.rank) ∈ Submodule.span (𝓞 D.host.E) (detSet (Bridge.hLat V (fin V h))) := by
    refine Submodule.subset_span ⟨fun i => (k : D.host.E) • (Pi.single i 1 : Fin V.rank → D.host.E), fun i => ?_, ?_⟩
    · have hstd : (Pi.single i (1 : D.host.E) : Fin V.rank → D.host.E) ∈ Formalism.L2.Pj.stdLat D.host.E V.rank := by
        rw [Formalism.L2.Pj.stdLat, Submodule.mem_pi]
        intro j _
        by_cases hj : j = i
        · subst hj; simpa using (Submodule.one_le.1 le_rfl : (1 : D.host.E) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E))
        · simp [Pi.single_apply, hj]
      have h1 := hk2 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self (k : 𝓞 D.host.E)) hstd)
      have h2 : ((k : 𝓞 D.host.E) • (Pi.single i (1 : D.host.E) : Fin V.rank → D.host.E)) =
          (k : D.host.E) • (Pi.single i 1 : Fin V.rank → D.host.E) := by
        rw [← map_natCast (algebraMap (𝓞 D.host.E) D.host.E) k, algebraMap_smul]
      rw [h2] at h1
      have h3 := (hΛ _).1 h1
      convert h3 using 1
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_apply, hj]
    · have : (Matrix.of fun i j => ((k : D.host.E) • (Pi.single j 1 : Fin V.rank → D.host.E)) i) =
          (k : D.host.E) • (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) := by
        ext i j
        simp [Matrix.one_apply, Pi.single_apply, eq_comm]
      rw [this, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hcM : cc ≤ M := le_trans le_sup_left hle
  have hpM : ((p : ℕ) : 𝓞 D.host.E) ∈ M := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hkM : ((k : ℕ) : 𝓞 D.host.E) ∉ M := by
    intro hkM
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hk
    have e1 := congrArg (Int.cast : ℤ → 𝓞 D.host.E) huv
    push_cast at e1
    refine hM.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    rw [← e1]
    exact M.add_mem (M.mul_mem_left _ hkM) (M.mul_mem_left _ hpM)
  have hkn : ((k : ℕ) : 𝓞 D.host.E) ^ V.rank ∉ M := fun h0 => hkM (hM.isPrime.mem_of_pow_mem _ h0)
  have hc'M : cc.map (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ M := by
    intro x hx
    have hm : (k : D.host.E) ^ V.rank * (x : D.host.E) ∈ idlE cc := by
      rw [← c3]
      exact Submodule.mul_mem_mul hdet ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hzeq⟩ := hm
    have hz' : z = ((k : ℕ) : 𝓞 D.host.E) ^ V.rank * x := by
      apply RingOfIntegers.ext
      rw [show (z : D.host.E) = Algebra.linearMap (𝓞 D.host.E) D.host.E z from rfl, hzeq]
      push_cast
      rfl
    rw [hz'] at hz
    exact ((hM.isPrime.mem_or_mem (hcM hz)).resolve_left hkn)
  exact hM.ne_top (top_le_iff.1 (c1 ▸ sup_le hcM hc'M))

end GlobalTheory.DetIdealPrime
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetIdealCoprimeSplitSupportedPointStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

theorem _root_.GlobalTheory.T.exists_detIdeal_coprime_splitSupportedPoint : ∀ (D : D7) (V : HSp D), HSpace.gram V = 1 → Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∀ (h : GA D V) (e : AE D) (P : Finset (HeightOneSpectrum (𝓞 D.host.E))) (y : (AE D)ˣ), IsIdemSum e P → SuppAt e V h → IsDetAt e V h y → ∀ (b : ℕ), (∀ Q ∈ P, (b : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (c : (AE D)ˣ →* Circle) (ψ : Formalism.L2.Host.HChar D.host.E), ChrEq c ψ → (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (b : 𝓞 D.host.E) ∉ Q.asIdeal → ψ.UnrAt Q) → (∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q → ∀ k : D.host.Fˣ, ψ.resFin (Q.under (𝓞 D.host.F)) k = 1) → ∀ (Λ : GenLat D.host.E V.rank), (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat V (fin V h)) → ∀ p : ℕ, p.Prime → Λ.TrivAt p → ∃ cc : Ideal (𝓞 D.host.E), cc ≠ ⊥ ∧ cc ⊔ Ideal.span {(b : 𝓞 D.host.E)} = ⊤ ∧ Nat.Coprime (Ideal.absNorm cc) p ∧ ((c y : Circle) : ℂ) = ((ψ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.DetIdealPrime.exists_ideal_coprime | exact GlobalTheory.DetIdealPrime.exists_ideal_coprime | (intros; apply GlobalTheory.DetIdealPrime.exists_ideal_coprime <;> assumption)
end
end
