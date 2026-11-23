module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Formalism.LocalToGlobal.ProjectiveLattices.JFDFree
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.JetIndepStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRowHighestHarmonicPolyDerivUnitaryAction
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructurePropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariant
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalSchwartzBruhatAlgebraIntegralLinear
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticeDiagonalUnitaryPatchedStandardStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SumMovedVacuumTranslatesEqFreeRowTestFunction
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaHeisenbergUnitaryColumnChange
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesTestFunctionHolomorphicWeight
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaVacuumUnitaryColumnChangeUnitFactor
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionPreservesThetaAndInnerProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.L2NormFundamentalDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PolyDerivMonomialOne

-- Source module: Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCmFieldGeneratorAtPrimesDividing

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem exists_span_eq_mul_coprime {R : Type*} [CommRing R] [IsDedekindDomain R]
    (J K : Ideal R) (hJ : J ≠ ⊥) (hK : K ≠ ⊥) :
    ∃ (a : R) (A : Ideal R), a ≠ 0 ∧ Ideal.span {a} = J * A ∧ IsCoprime A K := by
  classical
  have hJK : J * K ≠ ⊥ := mul_ne_zero hJ hK

  obtain ⟨a₀, ha₀⟩ := IsDedekindDomain.exists_sup_span_eq (Ideal.mul_le_inf.trans inf_le_left : J * K ≤ J) hJK
  obtain ⟨b, hbJK, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJK

  have key : ∃ a : R, a ≠ 0 ∧ J * K ⊔ Ideal.span {a} = J := by
    by_cases h0 : a₀ = 0
    · refine ⟨b, hb0, ?_⟩
      have hJKJ : J * K = J := by simpa [h0] using ha₀
      rw [sup_eq_left.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hbJK)), hJKJ]
    · exact ⟨a₀, h0, ha₀⟩
  obtain ⟨a, ha0, ha⟩ := key
  have haJ : Ideal.span {a} ≤ J := ha ▸ le_sup_right
  obtain ⟨A, hA⟩ := Ideal.dvd_iff_le.mpr haJ
  refine ⟨a, A, ha0, hA, ?_⟩
  rw [Ideal.isCoprime_iff_sup_eq]

  have h1 : J * (K ⊔ A) = J * ⊤ := by
    rw [Ideal.mul_sup, ← hA, ha, Ideal.mul_top]
  rw [sup_comm]
  exact mul_left_cancel₀ hJ h1

theorem exists_generator_at_primes_dividing :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔍 : Ideal (𝓞 E)) (M : ℕ), 𝔍 ≠ ⊥ → 0 < M → ∃ (α : 𝓞 E) (𝔞 : Ideal (𝓞 E)), α ≠ 0 ∧ Ideal.span {α} = 𝔍 * 𝔞 ∧ IsCoprime 𝔞 (Ideal.span {(M : 𝓞 E)}) := by
  intro E _ _ _ 𝔍 M h𝔍 hM
  have hK : Ideal.span {(M : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hM.ne'
  exact exists_span_eq_mul_coprime 𝔍 _ h𝔍 hK

end GlobalTheory.Dict
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCmFieldGeneratorAtPrimesDividingStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem _root_.GlobalTheory.T.exists_cmField_generator_at_primes_dividing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔍 : Ideal (𝓞 E)) (M : ℕ), 𝔍 ≠ ⊥ → 0 < M → ∃ (α : 𝓞 E) (𝔞 : Ideal (𝓞 E)), α ≠ 0 ∧ Ideal.span {α} = 𝔍 * 𝔞 ∧ IsCoprime 𝔞 (Ideal.span {(M : 𝓞 E)}) := by
  first | exact @GlobalTheory.Dict.exists_generator_at_primes_dividing | exact GlobalTheory.Dict.exists_generator_at_primes_dividing | (intros; apply GlobalTheory.Dict.exists_generator_at_primes_dividing <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRowHighestHarmonicPolyDerivUnitaryActionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem _root_.GlobalTheory.T.exists_rowHighest_harmonic_polyDeriv_unitaryAction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∀ (k : X.Ψ → Fin q0 → ℕ) (k' : X.Ψ → Fin X.p0 → ℕ), ∀ P ∈ Harm.rowHighest ℂ k k', ∃ P' ∈ Harm.rowHighest ℂ k k', ∀ F : (Fin n → Fin g → ℂ) → ℂ, AnalyticOnNhd ℂ F Set.univ → I2.polyDeriv P (letterDir X hr idx) (fun z => F (hAct X idx h z)) 0 = I2.polyDeriv P' (letterDir X hr idx) F 0 := by
  first | exact @GlobalTheory.Dict.exists_rowHighest_polyDeriv_hAct | exact GlobalTheory.Dict.exists_rowHighest_polyDeriv_hAct | (intros; apply GlobalTheory.Dict.exists_rowHighest_polyDeriv_hAct <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SumMovedVacuumTranslatesEqFreeRowTestFunctionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem _root_.GlobalTheory.T.sum_moved_vacuum_translates_eq_freeRow_testFunction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : SW.Level X) (hn : r ≤ n) (M : ℕ) (𝔐 𝔍 𝔞 : Ideal (𝓞 E)) (α : 𝓞 E), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → D.𝔪 = 𝔐 * 𝔍 → IsCoprime 𝔐 𝔍 → α ≠ 0 → Ideal.span {α} = 𝔍 * 𝔞 → IsCoprime 𝔞 (Ideal.span {(M : 𝓞 E)}) → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ h : Matrix (Fin n) (Fin n) E, h = Matrix.diagonal (fun k : Fin n => if (k : ℕ) < r then 1 else cc (α : E) / (α : E)) → ∀ Λ ∈ Vset E n M, ∀ Λ' ∈ Vset E n M, ∀ Λ'' ∈ Vset E n 1, Moves h Λ Λ'' → (𝔍 * conjI 𝔍) • Λ'' ≤ Λ' → (𝔍 * conjI 𝔍) • Λ' ≤ Λ'' → ∃ t : ℂ, t ≠ 0 ∧ ∀ L ∈ D.lats, ∃ s : Finset (Matrix (Fin n) (Fin r) E), D.phi bas hn v₀ L Λ = ∑ y ∈ s, D.dat hn y • heisG X bas y (unitv (projA X bas D.w (tens Λ (D.sh L)) (v₀ L))) ∧ ∑ y ∈ s, D.dat hn y • heisG X bas (h * y) (unitv (projA X bas D.w (tens Λ'' (D.sh L)) (v₀ L))) = t • phiF bas D 𝔐 hn v₀ L Λ' := by
  first | exact @GlobalTheory.Dict.SumFree.sum_free | exact GlobalTheory.Dict.SumFree.sum_free | (intros; apply GlobalTheory.Dict.SumFree.sum_free <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaHeisenbergUnitaryColumnChangeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem _root_.GlobalTheory.T.theta_heisenberg_unitary_column_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∀ φ φ' : TF n g, IsSB φ → IsSB φ' → ∀ t : ℂ, ∀ x ∈ X.dom, (∀ z, thA X bas idx φ' x (hAct X idx h z) = t * thA X bas idx φ x z) → ∀ (y : Matrix (Fin n) (Fin r) E) z, thA X bas idx (heisG X bas (h * y) φ') x (hAct X idx h z) = t * thA X bas idx (heisG X bas y φ) x z := by
  first | exact @GlobalTheory.Dict.thA_heisG_hAct | exact GlobalTheory.Dict.thA_heisG_hAct | (intros; apply GlobalTheory.Dict.thA_heisG_hAct <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaVacuumUnitaryColumnChangeUnitFactorStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem _root_.GlobalTheory.T.thetaVacuum_unitary_column_change_unit_factor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∀ Λ ∈ Vset E n 1, ∀ Λ' ∈ Vset E n 1, Moves h Λ Λ' → ∃ t : ℂ, ‖t‖ = 1 ∧ ∀ L : Lt E r, SelfD X L → ∀ v : TF n g, IsVac X bas w (tens (stdL E n) L) v → ∀ x ∈ X.dom, ∀ z : Fin n → Fin g → ℂ, thA X bas idx (unitv (projA X bas w (tens Λ' L) v)) x (hAct X idx h z) = t * thA X bas idx (unitv (projA X bas w (tens Λ L) v)) x z := by
  first | exact @GlobalTheory.Dict.thA_vacuum_hAct | exact GlobalTheory.Dict.thA_vacuum_hAct | (intros; apply GlobalTheory.Dict.thA_vacuum_hAct <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesLowerRowsZeroEqFreeLowerRows

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.DiagFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem vset_one {M : ℕ} {Λ : Lt E n} (h : Λ ∈ Vset E n M) : Λ ∈ Vset E n 1 := by
  obtain ⟨hfg, hdual, s, hs, -, h1, h2⟩ := h
  exact ⟨hfg, hdual, s, hs, Nat.coprime_one_right s, h1, h2⟩

theorem conjI_mono {P Q : Ideal (𝓞 E)} (h : P ≤ Q) : conjI P ≤ conjI Q := by
  unfold conjI
  exact Ideal.span_mono fun _ ⟨b, hb, e⟩ => ⟨b, h hb, e⟩

theorem isSB_smul (c : ℂ) {φ : TF n g} (h : IsSB φ) : IsSB (c • φ) := by
  obtain ⟨R, hR, h1, h2⟩ := h
  refine ⟨R, hR, fun x hx => h1 x fun h0 => hx ?_, fun x y hy => ?_⟩
  · simp [h0]
  · simp [h2 x y hy]

theorem thA_sum (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) {T : Type} (s : Finset T) (f : T → TF n g) (hf : ∀ i, IsSB (f i)) :
    thA X bas idx (∑ i ∈ s, f i) x = ∑ i ∈ s, thA X bas idx (f i) x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · have h0 := GlobalTheory.SW.UnAct.thA_smul (bas := bas) idx x (0 : ℂ) (0 : TF n g)
    simpa using h0
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      GlobalTheory.SW.UnAct.thA_add idx hs hx (hf a) (GlobalTheory.SW.RecSum.isSB_sum s f hf), ih]

theorem isSB_unitv_projA (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n) {w : E}
    (hw : IsIntegral ℤ w) (hw' : w + cc w = 1) {L : Lt E r} (hL : SelfD X L) {Λ : Lt E n}
    (hΛ : Λ ∈ Vset E n 1) {φ : TF n g} (hφ : IsSB φ) :
    IsSB (unitv (projA X bas w (tens Λ L) φ)) := by
  unfold unitv projA
  refine isSB_smul _ (isSB_smul _ ?_)
  refine finsum_mem_induction (fun ψ => IsSB ψ) isSB_zero
    (fun a b ha hb => (isSB_algebra_haar_linear ℚ (Fin n) (Fin g) a b ha hb).1) ?_
  rintro _ ⟨y, -, rfl⟩
  exact isSB_smul _ ((heisG_laws E r X g bas idx n hs hn).2.2.2 y φ hφ).1

private theorem thA_finset_sum_smul (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) {T : Type} (s : Finset T) (a : T → ℂ) (ψ : T → TF n g)
    (hψ : ∀ i, IsSB (ψ i)) (z : Fin n → Fin g → ℂ) :
    thA X bas idx (∑ i ∈ s, a i • ψ i) x z = ∑ i ∈ s, a i * thA X bas idx (ψ i) x z := by
  rw [thA_sum idx hs hx s _ (fun i => isSB_smul (a i) (hψ i)), Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GlobalTheory.SW.UnAct.thA_smul (bas := bas) idx x (a i) (ψ i)]
  rfl

theorem thP_phi_eq_thP_phiF : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : SW.Level X) (hn : r ≤ n) (M : ℕ) (𝔐 𝔍 : Ideal (𝓞 E)), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → D.𝔪 = 𝔐 * 𝔍 → IsCoprime 𝔐 𝔍 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ (k : X.Ψ → Fin q0 → ℕ) (k' : X.Ψ → Fin X.p0 → ℕ), ∀ Λ ∈ Vset E n M, ∀ P ∈ Harm.rowHighest ℂ k k', ∃ Λ' ∈ Vset E n M, ∃ P' ∈ Harm.rowHighest ℂ k k', ∀ L ∈ D.lats, ∀ x ∈ X.dom, thP X hr bas idx (D.phi bas hn v₀ L Λ) P x = thP X hr bas idx (phiF bas D 𝔐 hn v₀ L Λ') P' x := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn D hrn M 𝔐 𝔍 hM hMm hsplit hcop v₀ hv₀ k k' Λ hΛ P hP
  have hle : D.𝔪 ≤ 𝔍 := by
    rw [hsplit]
    exact Ideal.mul_le_inf.trans inf_le_right
  have h𝔍 : 𝔍 ≠ ⊥ := by
    intro h0
    apply D.ne_bot
    rw [hsplit, h0, Ideal.mul_bot]
  have hMJ : ((M : ℕ) : 𝓞 E) ∈ 𝔍 := hle hMm
  have hcopJ : IsCoprime 𝔍 (conjI 𝔍) := by
    have h1 := D.cop
    rw [Ideal.isCoprime_iff_sup_eq] at h1 ⊢
    exact top_unique (h1.symm.le.trans (sup_le_sup hle (conjI_mono hle)))
  obtain ⟨α, 𝔞, hα, hspan, hcopa⟩ := GlobalTheory.T.exists_cmField_generator_at_primes_dividing E 𝔍 M h𝔍 hM
  set H : Matrix (Fin n) (Fin n) E :=
    Matrix.diagonal (fun k : Fin n => if (k : ℕ) < r then 1 else cc (α : E) / (α : E)) with hHdef
  obtain ⟨hunit, hmove⟩ := GlobalTheory.T.selfDual_lattice_diagonal_unitary_patched_standard E n r M 𝔍 𝔞 α hM hMJ hcopJ hα hspan hcopa H hHdef
  obtain ⟨Λ', hΛ', Λ'', hΛ'', hmv, hle1, hle2⟩ := hmove Λ hΛ
  obtain ⟨t, ht0, ht⟩ := GlobalTheory.T.sum_moved_vacuum_translates_eq_freeRow_testFunction E r X g bas idx n hs hn D hrn M 𝔐 𝔍 𝔞 α hM hMm hsplit hcop hα
    hspan hcopa v₀ hv₀ H hHdef Λ hΛ Λ' hΛ' Λ'' hΛ'' hmv hle1 hle2
  obtain ⟨t', ht'1, ht'⟩ := GlobalTheory.T.thetaVacuum_unitary_column_change_unit_factor E r X g bas idx n hs hn D.w D.w_int D.w_tr H hunit Λ
    (vset_one hΛ) Λ'' hΛ'' hmv
  obtain ⟨P', hP', hPd⟩ := GlobalTheory.T.exists_rowHighest_harmonic_polyDeriv_unitaryAction E r X g q0 hr bas idx n hs hn H hunit k k' P hP
  have ht'0 : t' ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at ht'1
    exact zero_ne_one ht'1
  refine ⟨Λ', hΛ', (t / t') • P', Submodule.smul_mem _ _ hP', fun L hL x hx => ?_⟩
  have hSh : SelfD X (D.sh L) := ((GlobalTheory.T.level_structure_properties E r X g bas idx n hs hn D hrn).2.2.2.1 L hL).1
  have hv := hv₀ L hL
  have hφ := isSB_unitv_projA idx hs hn D.w_int D.w_tr hSh (vset_one hΛ) hv.1
  have hφ'' := isSB_unitv_projA idx hs hn D.w_int D.w_tr hSh hΛ'' hv.1
  have hheis : ∀ (y : Matrix (Fin n) (Fin r) E) (ψ : TF n g), IsSB ψ → IsSB (heisG X bas y ψ) :=
    fun y ψ hψ => ((heisG_laws E r X g bas idx n hs hn).2.2.2 y ψ hψ).1
  obtain ⟨s, hs1, hs2⟩ := ht L hL
  have hphiF : IsSB (phiF bas D 𝔐 hrn v₀ L Λ') := by
    have h2 : phiF bas D 𝔐 hrn v₀ L Λ' = t⁻¹ • (t • phiF bas D 𝔐 hrn v₀ L Λ') := by
      rw [smul_smul, inv_mul_cancel₀ ht0, one_smul]
    rw [h2, ← hs2]
    exact isSB_smul _ (GlobalTheory.SW.RecSum.isSB_sum s _ fun y => isSB_smul _ (hheis _ _ hφ''))
  have hDphi : IsSB (D.phi bas hrn v₀ L Λ) := by
    rw [hs1]
    exact GlobalTheory.SW.RecSum.isSB_sum s _ fun y => isSB_smul _ (hheis _ _ hφ)
  have key : ∀ z, t * thA X bas idx (phiF bas D 𝔐 hrn v₀ L Λ') x (GlobalTheory.Dict.hAct X idx H z) =
      t' * thA X bas idx (D.phi bas hrn v₀ L Λ) x z := by
    intro z
    have e1 := congrFun (GlobalTheory.SW.UnAct.thA_smul (bas := bas) idx x t (phiF bas D 𝔐 hrn v₀ L Λ'))
      (GlobalTheory.Dict.hAct X idx H z)
    rw [Pi.smul_apply, smul_eq_mul] at e1
    rw [← e1, ← hs2, thA_finset_sum_smul idx hs hx s _ _ (fun y => hheis _ _ hφ''), hs1,
      thA_finset_sum_smul idx hs hx s _ _ (fun y => hheis _ _ hφ), Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [GlobalTheory.T.theta_heisenberg_unitary_column_change E r X g bas idx n hs hn H hunit _ _ hφ hφ'' t' x hx
      (fun z => ht' (D.sh L) hSh (v₀ L) hv x hx z) y z]
    ring
  have hana := (theta_holomorphic_weight E r X g q0 hr bas idx n hs hn k k' _ hphiF P' hP').2.2.2 x hx
  have hdiff := ReciprocityTheory.ChartRestriction.G.I2.contDiff_of_diff (GlobalTheory.SW.ThetaHol.differentiable_thA idx hs hDphi hx)
  have hfun : (fun z => thA X bas idx (phiF bas D 𝔐 hrn v₀ L Λ') x (GlobalTheory.Dict.hAct X idx H z)) =
      (t' / t) • thA X bas idx (D.phi bas hrn v₀ L Λ) x := by
    funext z
    rw [Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination key z
  unfold GlobalTheory.SW.thP
  rw [ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_smul, ← hPd _ hana, hfun,
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_smul_fun _ _ hdiff]
  field_simp

end GlobalTheory.Dict.DiagFree
end
end
