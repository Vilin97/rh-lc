module

public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateDatumStatement
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExistsPosOfFamilyExists
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesHodgeTate
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ShortExactStandardLatticeStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyHodgePrimeBoundStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLatFlagPair
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyHodgePrimeCount
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyHodgePrimeDegreeStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyHodgePrimeHeightStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyHodgePrimeTotal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyModelPrimeBoundStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyModelPrimeDegreeStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyModelPrimeHeightStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrdinaryCurveHodgePrime
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyHodgePrimeCountStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT


theorem _root_.GlobalTheory.T.arith_variety_hodge_prime_count : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), LocFree (CR O y c') (Fintype.card F ^ (D.p + D.q)) (chartD e b pq sc w P i).M ∧ (chartD e b pq sc w P i).M ≤ stdLat (CR O y c') _ ∧ (∃ m : ℕ, mulLat ((p : Ω) ^ m) (stdLat (CR O y c') _) ≤ (chartD e b pq sc w P i).M) ∧ (1 : (Fin (D.p + D.q) → F) → Ω) ∈ (chartD e b pq sc w P i).M ∧ ∀ τ, (∀ a ∈ CR O y c', ∀ v ∈ (chartD e b pq sc w P i).Th τ, a • v ∈ (chartD e b pq sc w P i).Th τ) ∧ (∀ g, (∃ m, (g, m) ∈ (chartD e b pq sc w P i).Th τ) ↔ g ∈ (chartD e b pq sc w P i).M ∧ g 0 = 0) ∧ (∀ m, (∃ g, (g, m) ∈ (chartD e b pq sc w P i).Th τ) ↔ m ∈ dotDual (CR O y c') ((chartD e b pq sc w P i).lie τ)) ∧ ∀ m, (0, m) ∈ (chartD e b pq sc w P i).Th τ ↔ m ∈ mulLat (p : Ω) (dotDual (CR O y c') ((chartD e b pq sc w P i).lie τ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.chartD_fun_clauses | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.chartD_fun_clauses | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.chartD_fun_clauses <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyHodgePrimeTotalStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT


theorem _root_.GlobalTheory.T.arith_variety_hodge_prime_total : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (P : ∀ c' : ∀ k, J k, mseg y c' ≠ 0 → ChartPack G O c') (i : ∀ (c' : ∀ k, J k) (τ), (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), IsLatFamily O y (fun c' => (famD e b pq sc w P i c').M) ∧ ∀ τ : Sg, IsLatFamily O y (fun c' => (famD e b pq sc w P i c').Th τ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.Over.funfam_holds | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.Over.funfam_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.Over.funfam_holds <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrdinaryCurveHodgePrimeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT


theorem _root_.GlobalTheory.T.ordinary_curve_hodge_prime : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → GlobalTheory.CompanionTheory.Ar.GR.QuotientByFiniteFlatStatement → GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement → GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement → GlobalTheory.CompanionTheory.Ar.GR.OrdinaryCurveStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ((chartD e b pq sc w P i).bc RC).Facts RC p (algebraMap O C w) (fun τ a => χ τ a) φ' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testFacts | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testFacts | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testFacts <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyPosOfHodgeTateInputs

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem gamDel_of_seqHyp {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (w : Ω) (hw : w ∈ R)
    (hw0 : w ≠ 0) {r s n : ℕ} (W : AddSubgroup (Fin r → Ω)) (om : AddSubgroup (Fin s → Ω))
    (hW : ∀ a ∈ R, ∀ v ∈ W, a • v ∈ W) (hom : ∀ a ∈ R, ∀ v ∈ om, a • v ∈ om)
    (i : (Fin r → Ω) →ₗ[Ω] (Fin n → Ω)) (q : (Fin n → Ω) →ₗ[Ω] (Fin s → Ω)) (h : SeqHyp R w W om i q) :
    (∀ a ∈ R, (∀ v ∈ gamLat R w W i, a • v ∈ gamLat R w W i) ∧ ∀ v ∈ delLat R w om q, a • v ∈ delLat R w om q) ∧
    ((∀ a, (∃ b, (a, b) ∈ gamLat R w W i) ↔ w • a ∈ W) ∧ (∀ b, (0, b) ∈ gamLat R w W i ↔ b ∈ stdLat R (Fin n)) ∧
      ∀ a, (a, 0) ∈ gamLat R w W i ↔ a ∈ W) ∧
    ((∀ b, (∃ c, (b, c) ∈ delLat R w om q) ↔ w • b ∈ stdLat R (Fin n)) ∧
      (∀ c, (∃ b, (b, c) ∈ delLat R w om q) ↔ w • c ∈ om) ∧ (∀ c, (0, c) ∈ delLat R w om q ↔ c ∈ om) ∧
      ∀ b, (b, 0) ∈ delLat R w om q ↔ ∃ a, (a, b) ∈ gamLat R w W i) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  obtain ⟨Gam, Del, hG, hD, hst, hg, hd⟩ := GlobalTheory.T.short_exact_standard_lattice o Ω R w hw hw0 r s n W om hW hom i q h1 h2 h3 h4 h5
  have eG : Gam = gamLat R w W i := by
    ext ⟨a, b⟩
    exact hG a b
  have eD : Del = delLat R w om q := by
    ext ⟨a, b⟩
    exact hD a b
  subst eG eD
  exact ⟨hst, hg, hd⟩

end GlobalTheory.CompanionTheory.Ar.Num.FamEx

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx
open GlobalTheory.CompanionTheory.Ar.BT


theorem familyExistsPos_holds : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → GlobalTheory.CompanionTheory.Ar.GR.QuotientByFiniteFlatStatement → GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement → GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement → GlobalTheory.CompanionTheory.Ar.GR.OrdinaryCurveStatement → GlobalTheory.CompanionTheory.Ar.Num.FamilyExistsPos := by
  intro hF hQ hZ hH hOrd E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d ha hpq b hb p hpS hfree h2 hdisc φ hφ A _ _ _ m _ hm O _ _ _ _ _ _ _ t₀
  haveI : Fact p.Prime := ⟨𝔐.S_prime p hpS⟩
  obtain ⟨Sg, _, e, φ', F, _, _, _, pq, sc, w, σ, hO, hS⟩ :=
    GlobalTheory.T.arith_variety_hodge_prime_bound E H D l Xo c O₀ β Y S Ω K J y 𝔐 d ha hpq p hpS hfree h2 hdisc φ hφ A m hm O t₀
  obtain ⟨G⟩ := GlobalTheory.T.arith_variety_hodge_prime_degree E H D l Xo c O₀ β Y S Ω K J y 𝔐 d ha hpq p hpS hfree h2 hdisc
  have hP := GlobalTheory.T.arith_variety_hodge_prime_height E H D l Xo c O₀ β Y S Ω K J y 𝔐 d ha hpq p hpS hfree h2 hdisc A m hm O G
  let P : ∀ c' : ∀ k, J k, mseg y c' ≠ 0 → ChartPack G O c' := fun c' h => (hP c' h).some
  have hcp : HT.IsCp p (algebraMap O Ω w) := hO.2.2.2.2.2.2.2
  have hL := GlobalTheory.T.arith_variety_model_prime_bound hF E H D l Xo c O₀ β Y S Ω K J y 𝔐 d ha hpq p hpS hfree h2 hdisc b hb A m hm O w hcp
  have hQs := fun (c' : ∀ k, J k) (h : mseg y c' ≠ 0) (τ : Sg) =>
    GlobalTheory.T.arith_variety_model_prime_degree hF E H D l Xo c O₀ β Y S Ω K J y 𝔐 d ha hpq p hpS hfree h2 hdisc b hb A m hm O w hcp G c' h (P c' h) (e τ)
  classical
  let i : ∀ (c' : ∀ k, J k) (τ : Sg), (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω) :=
    fun c' τ => if h : mseg y c' ≠ 0 then (hQs c' h τ).choose else 0
  have hi : ∀ (c' : ∀ k, J k) (h : mseg y c' ≠ 0) (τ : Sg), SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i c' τ) (qMap (P c' h) (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq (P c' h) σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i c' τ) := fun c' h τ => by
    have heq : i c' τ = (hQs c' h τ).choose := dif_pos h
    rw [heq]
    exact (hQs c' h τ).choose_spec
  have hw0 : algebraMap O Ω w ≠ 0 := by
    have h3 := hcp
    unfold HT.IsCp at h3
    rw [if_neg h2] at h3
    obtain ⟨ζ, hζ, e1⟩ := h3
    rw [e1]
    exact hζ.sub_one_ne_zero (Fact.out : p.Prime).one_lt
  have hwR : ∀ c' : ∀ k, J k, algebraMap O Ω w ∈ CR O y c' := fun c' => Subalgebra.algebraMap_mem _ w
  have hBase : ∀ (c' : ∀ k, J k) (h : mseg y c' ≠ 0),
      (chartD e b pq sc w (P c' h) (i c')).Base (CR O y c') p (algebraMap O Ω w) := by
    intro c' h
    obtain ⟨hf1, hf2, hf3, hf4, hf5⟩ := GlobalTheory.T.arith_variety_hodge_prime_count E H D l Xo c O₀ β Y S Ω K J y 𝔐 d ha hpq p hpS hfree h2 hdisc b hb φ hφ A m hm O t₀ Sg e φ' F pq sc w σ hO hS G c' h (P c' h) (i c')
    have hG := fun τ : Sg => gamDel_of_seqHyp (CR O y c') (algebraMap O Ω w) (hwR c') hw0
      (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c')
      (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c'))
      ((hL (e τ)).2.2.2.2 c' h).2.1.1 ((hL (e τ).swap).2.2.2.2 c' h).2.2.2.1.1 (i c' τ) (qMap (P c' h) (b (e τ).swap)) (hi c' h τ).1
    exact
      { freeM := hf1
        M_le := hf2
        le_M := hf3
        one_mem := hf4
        free := fun τ => ⟨((hL (e τ)).2.2.2.2 c' h).1, ((hL (e τ)).2.2.2.2 c' h).2.1,
          ((hL (e τ).swap).2.2.2.2 c' h).2.2.1, ((hL (e τ).swap).2.2.2.2 c' h).2.2.2.1⟩
        incl := fun τ => ⟨((hL (e τ)).2.2.2.2 c' h).2.2.2.2.1, ((hL (e τ)).2.2.2.2 c' h).2.2.2.2.2.1,
          ((hL (e τ).swap).2.2.2.2 c' h).2.2.2.2.2.2.1, ((hL (e τ).swap).2.2.2.2 c' h).2.2.2.2.2.2.2⟩
        stable := fun τ a ha => ⟨((hG τ).1 a ha).1, ((hG τ).1 a ha).2, (hf5 τ).1 a ha⟩
        gam := fun τ => (hG τ).2.1
        del := fun τ => (hG τ).2.2
        th := fun τ => (hf5 τ).2 }
  have hFun := GlobalTheory.T.arith_variety_hodge_prime_total E H D l Xo c O₀ β Y S Ω K J y 𝔐 d ha hpq p hpS hfree h2 hdisc b hb φ hφ A m hm O t₀ Sg e φ' F pq sc w σ hO hS G P i
  have hSf := GlobalTheory.T.arith_variety_model_prime_height hF E H D l Xo c O₀ β Y S Ω K J y 𝔐 d ha hpq p hpS hfree h2 hdisc b hb φ hφ A m hm O t₀ Sg e φ' F pq sc w σ hO hS G P i hi
  have hpos := fun c' h => famD_pos (O := O) e b pq sc w P i c' h
  refine ⟨Sg, inferInstance, e, φ', F, inferInstance, inferInstance, inferInstance, w, σ, famD e b pq sc w P i, hO.1, hO.2.2.1, ?_, ?_⟩
  · refine ⟨hFun.1, fun τ => ⟨?_, ?_, ?_, ?_, (hSf τ).1, (hSf τ).2, hFun.2 τ⟩, hO.2.2.2.2.2.2.1, ?_, ?_⟩
    · exact isLatFamily_congr (fun c' h => by rw [hpos c' h]; rfl) (hL (e τ)).1
    · exact isLatFamily_congr (fun c' h => by rw [hpos c' h]; rfl) (hL (e τ)).2.1
    · exact isLatFamily_congr (fun c' h => by rw [hpos c' h]; rfl) (hL (e τ).swap).2.2.1
    · exact isLatFamily_congr (fun c' h => by rw [hpos c' h]; rfl) (hL (e τ).swap).2.2.2.1
    · intro c' h
      rw [hpos c' h]
      exact hBase c' h
    · intro c' h C _ _ _ _ RC hRC χ hχ
      rw [hpos c' h]
      exact GlobalTheory.T.ordinary_curve_hodge_prime hF hQ hZ hH hOrd E H D l Xo c O₀ β Y S Ω K J y 𝔐 d ha hpq p hpS hfree h2 hdisc b hb φ hφ A m hm O t₀ Sg e φ' F pq sc w σ hO hS G c' h (P c' h) (i c') (hi c' h) (hBase c' h) C RC hRC χ hχ
  · intro c' h τ
    rw [hpos c' h]
    exact ⟨rfl, rfl, rfl, rfl⟩
end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyPosOfHodgeTateInputsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)


theorem _root_.GlobalTheory.T.family_pos_of_hodge_tate_inputs : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → GlobalTheory.CompanionTheory.Ar.GR.QuotientByFiniteFlatStatement → GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement → GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement → GlobalTheory.CompanionTheory.Ar.GR.OrdinaryCurveStatement → GlobalTheory.CompanionTheory.Ar.Num.FamilyExistsPos := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.familyExistsPos_holds | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.familyExistsPos_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.familyExistsPos_holds <;> assumption)
end
end
