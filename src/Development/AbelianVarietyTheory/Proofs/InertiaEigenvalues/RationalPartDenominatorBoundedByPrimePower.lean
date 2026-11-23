module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceIdempotentComponentsConjValuationStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BndMul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBoundedPrimeToDenomGLAndInvOfEqOneOffFinite
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicMatrixExistsPrimePowClearsDenominatorsOverStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedDenomRationalMatrixOfFinitePartStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteMatrixEqOneOfEqOneAtPlacesOverStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentAddConjSupportFinitePrimeToPStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBoundedPrimeToDenomGLAndInvOfEqOneOffFinite
import Formalism.LocalRingCardinality.DataHost
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.IndefiniteReal.BridgeTie
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BndMul
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicMatrixBoundedDenominatorPrimeToOfIntegral

section

@[expose] public section

open NumberField IsDedekindDomain

namespace GlobalTheory.StdAtPrime

theorem bnd_of_integral_over_prime : ∀ {E : Type} [Field E] [NumberField E] (p : ℕ), p.Prime → ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)), (∀ Q : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ Q.asIdeal → ∀ i j, Valued.v ((A i j) Q) ≤ 1) → GlobalTheory.StdAtPrime.Bnd p A := by
  intro E _ _ p hp n A hA
  let S : Set (HeightOneSpectrum (𝓞 E)) := {Q | ∃ i j, ¬ Valued.v ((A i j) Q) ≤ 1}
  have hS : S.Finite := by
    have hsub : S ⊆ ⋃ i, ⋃ j, {Q | ¬ (A i j) Q ∈ Q.adicCompletionIntegers E} := by
      rintro Q ⟨i, j, h⟩
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨i, j, fun hm => h ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hm)⟩
    refine Set.Finite.subset (Set.finite_iUnion fun i => Set.finite_iUnion fun j => ?_) hsub
    exact Filter.eventually_cofinite.mp (A i j).2
  refine bnd_of_local p n A S hS (fun Q hQ i j => ?_) (fun Q hQ i j => ?_)
  · have hpQ : (p : 𝓞 E) ∉ Q.asIdeal := by
      obtain ⟨i', j', h⟩ := hQ
      exact fun hm => h (hA Q hm i' j')
    exact exists_coprime_natCast_mul_v_le_one p hp Q hpQ _
  · by_contra h
    exact hQ ⟨i, j, h⟩

end GlobalTheory.StdAtPrime
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicMatrixBoundedDenominatorPrimeToOfIntegralStatement

section

@[expose] public section

open NumberField IsDedekindDomain


theorem _root_.GlobalTheory.T.adelicMatrix_boundedDenominator_primeTo_of_integral : ∀ {E : Type} [Field E] [NumberField E] (p : ℕ), p.Prime → ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)), (∀ Q : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ Q.asIdeal → ∀ i j, Valued.v ((A i j) Q) ≤ 1) → GlobalTheory.StdAtPrime.Bnd p A := by
  first | exact @GlobalTheory.StdAtPrime.bnd_of_integral_over_prime | exact GlobalTheory.StdAtPrime.bnd_of_integral_over_prime | (intros; apply GlobalTheory.StdAtPrime.bnd_of_integral_over_prime <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBoundedPrimeToDenomGLAndInvOfEqOneOffFiniteStatement

section

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum

open GlobalTheory.StdAtPrime


theorem _root_.GlobalTheory.T.isBoundedPrimeToDenom_GL_and_inv_of_eq_one_off_finite : ∀ {E : Type} [Field E] [NumberField E] (p : ℕ), p.Prime → ∀ (n : ℕ) (G : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (S : Set (HeightOneSpectrum (𝓞 E))), S.Finite → (∀ Q ∈ S, (p : 𝓞 E) ∉ Q.asIdeal) → (∀ Q ∉ S, ∀ i j, (G.1 i j) Q = ((1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) Q) → Bnd p G.1 ∧ Bnd p (G⁻¹).1 := by
  first | exact @GlobalTheory.StdAtPrime.bnd_and_bnd_inv_of_eq_one_off_finite | exact GlobalTheory.StdAtPrime.bnd_and_bnd_inv_of_eq_one_off_finite | (intros; apply GlobalTheory.StdAtPrime.bnd_and_bnd_inv_of_eq_one_off_finite <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatAtTrivAtOfSplit

section

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum


namespace GlobalTheory.StdAtPrime

theorem bnd_inv_of_hLat_std (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (h1 : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E _ x)
    (h2 : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1)
    (V : HSp D) (hL : Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank) (p : ℕ) (k : Bridge.Gf V)
    (hk : Bridge.hLat V k = Formalism.L2.Pj.stdLat D.host.E V.rank) :
    Bnd p (Matrix.GeneralLinearGroup.map ι.toRingHom k.1)⁻¹.1 := by
  refine ⟨1, Nat.coprime_one_left p, fun i j Q => ?_⟩
  have hx : (Pi.single j (1 : D.host.E) : Fin V.rank → D.host.E) ∈ Bridge.hLat V k := by
    rw [hk]
    refine Submodule.mem_pi.2 fun i' _ => ?_
    by_cases h : i' = j
    · subst h; rw [Pi.single_eq_same]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _
  have := (GlobalTheory.ClassScalarValue.mem_hLat ι h1 h2 V hL k _).1 hx i Q
  have e : (fun j' => algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E)
      ((Pi.single j (1 : D.host.E) : Fin V.rank → D.host.E) j')) = Pi.single j 1 := by
    funext j'
    by_cases h : j' = j
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  rw [e, Matrix.mulVec_single_one] at this
  rw [Nat.cast_one, one_mul]
  exact this


end GlobalTheory.StdAtPrime
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupportedAdelicPointEqOneWhereIdempotentVanishes

section

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum

open GlobalTheory.StdAtPrime

theorem GlobalTheory.SuppOneIdentity.finPt_entry_eq_one_of_idem_zero : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E) (V : HSp D) (e : AE D) (g : GA D V), SuppAt e V g → ∀ Q : HeightOneSpectrum (𝓞 D.host.E), ι (finPart D (e + cA D e)) Q = 0 → ∀ i j, ((Matrix.GeneralLinearGroup.map ι.toRingHom (finPt V g).1).1 i j) Q = ((1 : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.E) D.host.E)) i j) Q := by
  intro D ι V e g hS Q hQ i j
  have hent : ∀ i j, ((finPt V g).1 : Matrix (Fin V.rank) (Fin V.rank) _) i j
      = finPart D (Formalism.L2.Theta.mt V g i j) := fun i j => rfl
  have h1 := congrArg (fun x => ι (finPart D x) Q) (hS i j)
  simp only [map_mul] at h1
  have hm : (ι (finPart D (e + cA D e)) * ι (finPart D ((Formalism.L2.Theta.mt V g - 1) i j))) Q
      = ι (finPart D (e + cA D e)) Q * ι (finPart D ((Formalism.L2.Theta.mt V g - 1) i j)) Q := rfl
  rw [hm, hQ, zero_mul] at h1
  have h2 : ι (finPart D (Formalism.L2.Theta.mt V g i j)) Q
      = ι (finPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)) Q := by
    have hs : (Formalism.L2.Theta.mt V g - 1) i j = Formalism.L2.Theta.mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j := rfl
    rw [hs, map_sub, map_sub] at h1
    have hsub : (ι (finPart D (Formalism.L2.Theta.mt V g i j)) - ι (finPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j))) Q
        = ι (finPart D (Formalism.L2.Theta.mt V g i j)) Q - ι (finPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)) Q := rfl
    rw [hsub] at h1
    exact (sub_eq_zero.mp h1.symm)
  show ι (((finPt V g).1 : Matrix (Fin V.rank) (Fin V.rank) _) i j) Q = _
  rw [hent, h2]
  by_cases hij : i = j
  · subst hij; simp [Matrix.one_apply_eq]
  · simp [Matrix.one_apply_ne hij]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupportedAdelicPointEqOneWhereIdempotentVanishesStatement

section

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum

open GlobalTheory.StdAtPrime


theorem _root_.GlobalTheory.T.supported_adelic_point_eq_one_where_idempotent_vanishes : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E) (V : HSp D) (e : AE D) (g : GA D V), SuppAt e V g → ∀ Q : HeightOneSpectrum (𝓞 D.host.E), ι (finPart D (e + cA D e)) Q = 0 → ∀ i j, ((Matrix.GeneralLinearGroup.map ι.toRingHom (finPt V g).1).1 i j) Q = ((1 : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.E) D.host.E)) i j) Q := by
  first | exact @GlobalTheory.SuppOneIdentity.finPt_entry_eq_one_of_idem_zero | exact GlobalTheory.SuppOneIdentity.finPt_entry_eq_one_of_idem_zero | (intros; apply GlobalTheory.SuppOneIdentity.finPt_entry_eq_one_of_idem_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalPartDenominatorBoundedByPrimePower

section

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries

open GlobalTheory.StdAtPrime

namespace GlobalTheory.MoveDenom



theorem denomAt_of_move : ∀ (D : D7) (V : HSp D), Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∀ l : ℕ, l.Prime → ∀ s : GA D V, ∃ c : ℕ, ∀ z : GA D V, OneAt V l z → ∀ (γ h : GA D V) (γ' : GL (Fin V.rank) D.host.E) (k : Bridge.Gf V) (bad : ℕ), GlobalTheory.Member.IsRat V γ γ' → l ∣ bad → SplitOffBad V bad h → Bridge.hLat V k = Formalism.L2.Pj.stdLat D.host.E V.rank → Bridge.hLat V k⁻¹ = Formalism.L2.Pj.stdLat D.host.E V.rank → fin V (s * z) = fin V γ * fin V h * k → DenomAt l c γ' := by
  intro D V hstd l hl s
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  set M := Matrix.GeneralLinearGroup.map (n := Fin V.rank) ι.toRingHom with hM
  obtain ⟨c1, hc1⟩ := GlobalTheory.T.adelicMatrix_exists_prime_pow_clears_denominators_over l hl V.rank (M (fin V s).1).1
  obtain ⟨c2, hc2⟩ := GlobalTheory.T.adelicMatrix_exists_prime_pow_clears_denominators_over l hl V.rank (M (fin V s).1)⁻¹.1
  refine ⟨max c1 c2, ?_⟩
  intro z hz γ h γ' k bad hrat hlb hsob hk hk' heq
  set C : FiniteAdeleRing (𝓞 D.host.E) D.host.E := ((l ^ max c1 c2 : ℕ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E) with hC
  have bs : Bnd l (C • (M (fin V s).1).1) := GlobalTheory.T.adelicMatrix_boundedDenominator_primeTo_of_integral l hl _ _ fun Q hQ i j => by
    rw [Matrix.smul_apply, smul_eq_mul]; exact hc1 _ (le_max_left _ _) Q hQ i j
  have bs' : Bnd l (C • (M (fin V s).1)⁻¹.1) := GlobalTheory.T.adelicMatrix_boundedDenominator_primeTo_of_integral l hl _ _ fun Q hQ i j => by
    rw [Matrix.smul_apply, smul_eq_mul]; exact hc2 _ (le_max_right _ _) Q hQ i j
  have ez := GlobalTheory.T.finiteMatrix_apply_eq_one_at_places_over_of_oneAt D ι h1 h2 h3 V l z hz
  have bz : Bnd l (M (fin V z).1).1 := GlobalTheory.T.adelicMatrix_boundedDenominator_primeTo_of_integral l hl _ _ fun Q hQ i j => by
    rw [ez Q hQ i j]; exact one_entry_v_le_one _ Q i j
  have bz' : Bnd l (M (fin V z).1)⁻¹.1 := GlobalTheory.T.adelicMatrix_boundedDenominator_primeTo_of_integral l hl _ _ fun Q hQ i j => by
    rw [inv_eq_one_off _ _ Q (ez Q hQ) i j]; exact one_entry_v_le_one _ Q i j
  have bk' : Bnd l (M k.1)⁻¹.1 := bnd_inv_of_hLat_std D ι h1 h2 V hstd l k hk
  have bk : Bnd l (M k.1).1 := by
    have := bnd_inv_of_hLat_std D ι h1 h2 V hstd l k⁻¹ hk'
    rwa [Subgroup.coe_inv, map_inv, inv_inv] at this
  have h4 := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3
  obtain ⟨hid, hcj⟩ := GlobalTheory.T.placeIdempotent_components_conj_valuation D ι h1 h2 h4
  obtain ⟨-, e', P', he', hb', hs'⟩ := hsob
  have hp' : ∀ PP ∈ P', (l : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro PP hPP hpP
    obtain ⟨c, rfl⟩ := hlb
    exact hb' PP hPP (by rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hpP)
  obtain ⟨S, hSf, hSp, hS0⟩ := GlobalTheory.T.idempotent_add_conj_support_finite_prime_to_p D ι hid hcj l e' P' he' hp'
  obtain ⟨bh, bh'⟩ := GlobalTheory.T.isBoundedPrimeToDenom_GL_and_inv_of_eq_one_off_finite l hl _ (M (fin V h).1) S hSf hSp fun Q hQ i j =>
    GlobalTheory.T.supported_adelic_point_eq_one_where_idempotent_vanishes D ι V e' h hs' Q (hS0 Q hQ) i j
  have eγ : fin V γ = fin V s * fin V z * k⁻¹ * (fin V h)⁻¹ := by
    have e1 : fin V (s * z) = fin V s * fin V z := map_mul _ _ _
    rw [e1] at heq
    rw [heq]; group
  have eMγ : M (fin V γ).1 = M (fin V s).1 * M (fin V z).1 * (M k.1)⁻¹ * (M (fin V h).1)⁻¹ := by
    rw [eγ, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv,
      map_mul, map_mul, map_mul, map_inv, map_inv]
  apply GlobalTheory.T.boundedDenom_rationalMatrix_of_finitePart D ι h1 V l (max c1 c2) γ γ' hrat
  · rw [eMγ, Units.val_mul, Units.val_mul, Units.val_mul, ← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.smul_mul]
    exact bnd_mul l _ _ _ (bnd_mul l _ _ _ (bnd_mul l _ _ _ bs bz) bk') bh'
  · rw [eMγ, _root_.mul_inv_rev, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, inv_inv,
      Units.val_mul, Units.val_mul, Units.val_mul, ← Matrix.mul_smul, ← Matrix.mul_smul, ← Matrix.mul_smul]
    exact bnd_mul l _ _ _ bh (bnd_mul l _ _ _ bk (bnd_mul l _ _ _ bz' bs'))

end GlobalTheory.MoveDenom
end
end
