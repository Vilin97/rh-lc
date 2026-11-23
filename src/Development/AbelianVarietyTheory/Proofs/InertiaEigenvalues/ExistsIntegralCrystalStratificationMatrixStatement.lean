module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCrystalCoordinates
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystalCoordinatesConstantCoeffEqStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsGenIsUnitSub
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystalFrobeniusBreuilKisinCoordinates
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallinePhiModuleMapExists
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystalCoordinatesOverBreuilKisin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallinePrismsStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesVecReduceModUMulVec
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCrystalCoordinatesStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.breuilKisinPrism_crystal_coordinates : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : GlobalTheory.BKReal.Lat a O K ϖ) (I : Ident t ϖ P T), GlobalTheory.Published.BhattScholzeCrystallineLattices → IsBK I → ∃ (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), Function.Injective c ∧ (∀ x, c x ∈ P.M) ∧ (∀ m ∈ P.M, ∃ x, c x = m) ∧ (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) ∧ (∀ o : O, ∃ U : FHom EE EE, ∀ x, c (U.u (ϖ.prism a) x) = fun τ i => PowerSeries.C (algebraMap O K o) * c x τ i) ∧ (∀ (x m : EE.M (ϖ.prism a)) (k : ℕ), IsFrac (A := (ϖ.prism a).A) (eis l a e) (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ x) m k → c m = fun τ i => E K l e ^ k * P.phi (c x) τ i) := by
  first | exact @GlobalTheory.BKCoord.main | exact GlobalTheory.BKCoord.main | (intros; apply GlobalTheory.BKCoord.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystalFrobeniusBreuilKisinCoordinatesStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.crystal_frobenius_breuilKisin_coordinates : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → (∀ (x m : EE.M (ϖ.prism a)) (k : ℕ), IsFrac (A := (ϖ.prism a).A) (eis l a e) (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ x) m k → c m = fun τ i => E K l e ^ k * P.phi (c x) τ i) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (hl : (l : PP.A) ∈ PP.I) (p : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (J : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (g : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ τ (w : (Wq l a)⟦X⟧), J τ (p.f w) = g (toAc t K (frobS l a w) τ : K⟦X⟧)) → (∀ τ y, J τ (PP.D.φ y) = φ₂ (J (τ - 1) y)) → (∀ f, φ₂ (g f) = g (frob K l f)) → Function.Injective g → ∀ lam : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧), (∀ (r : PP.A) (y : EE.M PP) τ i, lam (r • y) τ i = J τ r * lam y τ i) → (∀ x τ i, lam (EE.tr p x) τ i = g (frob K l (c x (τ - 1) i))) → ∀ (y n : EE.M PP) (k : ℕ), IsFrac (l : PP.A) (EE.Φ PP ⟨l, hl⟩ y) n k → ∀ τ i, lam n τ i = (l : K⟦X⟧⟦X⟧) ^ k * (((P.mx (τ - 1)).map (frob K l)).map g *ᵥ fun j => φ₂ (lam y (τ - 1) j)) i := by
  first | exact @GlobalTheory.CrysFrobCoord.frob_in_coordinates | exact GlobalTheory.CrysFrobCoord.frob_in_coordinates | (intros; apply GlobalTheory.CrysFrobCoord.frob_in_coordinates <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallinePhiModuleMapExistsStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.crystalline_phi_module_map_exists : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), Function.Injective c → (∀ x, c x ∈ P.M) → (∀ m ∈ P.M, ∃ x, c x = m) → (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → (∀ o : O, ∃ U : FHom EE EE, ∀ x, c (U.u (ϖ.prism a) x) = fun τ i => PowerSeries.C (algebraMap O K o) * c x τ i) → ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (j : ZMod a → PP.A →+* K⟦X⟧⟦X⟧), (∀ τ (x : (Wq l a)⟦X⟧), j τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧) ∧ j τ (p₁.f x) = sh (toAc t K (frobS l a x) τ : K⟦X⟧)) → ∀ (lam₀ lam₁ : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧)), (∀ (r : PP.A) (y : EE.M PP) τ i, lam₀ (r • y) τ i = j τ r * lam₀ y τ i) → (∀ (r : PP.A) (y : EE.M PP) τ i, lam₁ (r • y) τ i = j τ r * lam₁ y τ i) → (∀ x τ i, lam₀ (EE.tr p₀ x) τ i = PowerSeries.C (frob K l (c x (τ - 1) i))) → (∀ x τ i, lam₁ (EE.tr p₁ x) τ i = sh (frob K l (c x (τ - 1) i))) → ∃ ε : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧, ∀ y τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ := by
  first | exact @GlobalTheory.BKGal.CrysEps.exists_eps | exact GlobalTheory.BKGal.CrysEps.exists_eps | (intros; apply GlobalTheory.BKGal.CrysEps.exists_eps <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystalCoordinatesOverBreuilKisinStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_crystal_coordinates_over_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (J : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (g : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ τ (w : (Wq l a)⟦X⟧), J τ (p.f w) = g (toAc t K (frobS l a w) τ : K⟦X⟧)) → ∃ lam : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧), (∀ (r : PP.A) (y : EE.M PP) τ i, lam (r • y) τ i = J τ r * lam y τ i) ∧ ∀ x τ i, lam (EE.tr p x) τ i = g (frob K l (c x (τ - 1) i)) := by
  first | exact @GlobalTheory.CrysExt.exists_coord | exact GlobalTheory.CrysExt.exists_coord | (intros; apply GlobalTheory.CrysExt.exists_coord <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorialMulCrystalCoordCoeffMem

section

@[expose] public section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.CrysInteg

theorem mem_of_semiBC {A B M N Q : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] [AddCommGroup Q] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u)
    (g : N →+ Q) (H : AddSubgroup Q) (hg : ∀ (r : B) (x : M), g (r • u x) ∈ H) (y : N) : g y ∈ H := by
  have hspan : y ∈ Submodule.span B (Set.range u) := by
    have h1 : (Submodule.span B (Set.range u)).mkQ = 0 := h.hom_ext fun x => by
      rw [LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.subset_span ⟨x, rfl⟩
    have := LinearMap.congr_fun h1 y
    rwa [LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  have key : ∀ z ∈ Submodule.span B (Set.range u), ∀ r : B, g (r • z) ∈ H := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, rfl⟩ := hz
      exact fun r => hg r x
    | zero =>
      intro r
      rw [smul_zero, map_zero]
      exact H.zero_mem
    | add z w _ _ hz hw =>
      intro r
      rw [smul_add, map_add (f := _)]
      exact add_mem (hz r) (hw r)
    | smul s z _ hz =>
      intro r
      rw [smul_smul]
      exact hz _
  have := key y hspan 1
  rwa [one_smul] at this

def divSub {R σ ι : Type} [CommRing R] (S : Subring R) (τ : σ) (i : ι) (k : ℕ) :
    AddSubgroup (σ → ι → R⟦X⟧) where
  carrier := {v | (k.factorial : R) * coeff k (v τ i) ∈ S}
  add_mem' {v w} hv hw := by
    change (k.factorial : R) * coeff k (v τ i + w τ i) ∈ S
    rw [map_add (f := _), mul_add]
    exact add_mem hv hw
  zero_mem' := by
    change (k.factorial : R) * coeff k (0 : R⟦X⟧) ∈ S
    rw [map_zero, mul_zero]
    exact zero_mem _
  neg_mem' {v} hv := by
    change (k.factorial : R) * coeff k (-(v τ i)) ∈ S
    rw [map_neg, mul_neg]
    exact neg_mem hv

theorem factorial_mul_coeff_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ x, c x ∈ P.M) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (J : ZMod a → PP.A →+* K⟦X⟧⟦X⟧), (∀ τ y (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (J τ y) ∈ S O K e) → ∀ lam : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧), (∀ (r : PP.A) (y : EE.M PP) τ i, lam (r • y) τ i = J τ r * lam y τ i) → (∀ x τ i, lam (EE.tr p x) τ i = PowerSeries.C (frob K l (c x (τ - 1) i))) → ∀ y τ i (k : ℕ), (k.factorial : K⟦X⟧) * coeff k (lam y τ i) ∈ S O K e := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P EE c hc PP p J hJ lam hsm htr y τ i k
  refine mem_of_semiBC (EE.tr_bc p) lam (divSub (S O K e).toSubring τ i k) (fun r x => ?_) y
  change (k.factorial : K⟦X⟧) * coeff k (lam (r • EE.tr p x) τ i) ∈ S O K e
  rw [hsm, htr, PowerSeries.coeff_mul_C, ← mul_assoc]
  exact mul_mem (hJ τ r k) (A_le_S l e (frob_mem_A l (mem_tot.1 (hc x) (τ - 1) i)))

end GlobalTheory.BKGal.CrysInteg
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorialMulCrystalCoordCoeffMemStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.factorial_mul_crystalCoord_coeff_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ x, c x ∈ P.M) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (J : ZMod a → PP.A →+* K⟦X⟧⟦X⟧), (∀ τ y (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (J τ y) ∈ S O K e) → ∀ lam : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧), (∀ (r : PP.A) (y : EE.M PP) τ i, lam (r • y) τ i = J τ r * lam y τ i) → (∀ x τ i, lam (EE.tr p x) τ i = PowerSeries.C (frob K l (c x (τ - 1) i))) → ∀ y τ i (k : ℕ), (k.factorial : K⟦X⟧) * coeff k (lam y τ i) ∈ S O K e := by
  first | exact @GlobalTheory.BKGal.CrysInteg.factorial_mul_coeff_mem | exact GlobalTheory.BKGal.CrysInteg.factorial_mul_coeff_mem | (intros; apply GlobalTheory.BKGal.CrysInteg.factorial_mul_coeff_mem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCrystalStratificationMatrix

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CrysStrat

theorem single_mem_M {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (σ : ZMod a) (j : ι) :
    (Pi.single σ (Pi.single j (1 : K⟦X⟧)) : Vec K a ι) ∈ P.M := by
  refine mem_tot.2 fun τ => mem_vecs.2 fun i => ?_
  by_cases h : τ = σ
  · subst h; rw [Pi.single_eq_same]
    by_cases h' : i = j
    · subst h'; rw [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne h']; exact zero_mem _
  · rw [Pi.single_eq_of_ne h]; exact zero_mem _

theorem mulVec_single_one' {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R) (j i : ι) :
    (M *ᵥ Pi.single j 1) i = M i j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem exists_stratification : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∀ (sh : (↥LL.1)⟦X⟧ →+* (↥LL.1)⟦X⟧⟦X⟧) (φ₂ : (↥LL.1)⟦X⟧⟦X⟧ →+* (↥LL.1)⟦X⟧⟦X⟧), (∀ (f : (↥LL.1)⟦X⟧) (i : ℕ), (i.factorial : (↥LL.1)⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := ↥LL.1))^[i] f) → (∀ f : (↥LL.1)⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob (↥LL.1) l f)) → (∀ f : (↥LL.1)⟦X⟧, φ₂ (sh f) = sh (frob (↥LL.1) l f)) → ∃ ε : ZMod a → Matrix ι ι (↥LL.1)⟦X⟧⟦X⟧, (∀ τ, (ε τ).map PowerSeries.constantCoeff = 1) ∧ (∀ τ, ε τ * ((P.mx (τ - 1)).map (frob (↥LL.1) l)).map sh = ((P.mx (τ - 1)).map (frob (↥LL.1) l)).map PowerSeries.C * (ε (τ - 1)).map φ₂) ∧ ∀ (τ : ZMod a) (i j : ι) (k : ℕ), (k.factorial : (↥LL.1)⟦X⟧) * coeff k (ε τ i j) ∈ S (↥(OL LL)) (↥LL.1) e := by
  intro hBS l _ a e _ _ ϖ LL _ _ hl ι _ _ P T I hBK sh φ₂ hsh hφC hφsh
  obtain ⟨EE, c, hinj, hcM, hsurj, hsemi, hO, hfr⟩ := GlobalTheory.T.breuilKisinPrism_crystal_coordinates l a e _ _ (thetaW a LL) ϖ ι P _ _ hBS hBK
  obtain ⟨PP, S₀, p₀, p₁, δ, j, j₀, hI, hδ, hj₀, hjp, hjφ, hS, hS', -⟩ :=
    GlobalTheory.T.exists_crystalline_prisms l a e (↥(OL LL)) (↥LL.1) (thetaW a LL) ϖ hl sh φ₂ hsh hφC hφsh
  obtain ⟨lam₀, hl₀, hv₀⟩ := GlobalTheory.T.exists_crystal_coordinates_over_breuilKisin l a e _ _ (thetaW a LL) ϖ ι EE c hsemi PP p₀ j PowerSeries.C
    (fun τ w => (hjp τ w).1)
  obtain ⟨lam₁, hl₁, hv₁⟩ := GlobalTheory.T.exists_crystal_coordinates_over_breuilKisin l a e _ _ (thetaW a LL) ϖ ι EE c hsemi PP p₁ j sh
    (fun τ w => (hjp τ w).2)
  obtain ⟨ε, hε⟩ := GlobalTheory.T.crystalline_phi_module_map_exists l a e _ _ (thetaW a LL) ϖ ι P EE c hinj hcM hsurj hsemi hO sh hsh PP p₀ p₁ j hjp
    lam₀ lam₁ hl₀ hl₁ hv₀ hv₁
  have hsh0 : ∀ f, PowerSeries.constantCoeff (sh f) = f := fun f => by
    simpa using hsh f 0

  have hcol : ∀ (τ : ZMod a) (jj : ι), ∃ x, c x = Pi.single (τ - 1) (Pi.single jj 1) :=
    fun τ jj => hsurj _ (single_mem_M P _ jj)
  have hv1 : ∀ (τ : ZMod a) (jj : ι) (x : EE.M (ϖ.prism a)), c x = Pi.single (τ - 1) (Pi.single jj 1) →
      lam₁ (EE.tr p₁ x) τ = Pi.single jj 1 := fun τ jj x hx => funext fun i => by
    rw [hv₁, hx, Pi.single_eq_same]
    by_cases h : i = jj
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  have hv0 : ∀ (τ : ZMod a) (jj : ι) (x : EE.M (ϖ.prism a)), c x = Pi.single (τ - 1) (Pi.single jj 1) →
      ∀ i, lam₀ (EE.tr p₁ x) τ i = ε τ i jj := fun τ jj x hx i => by
    rw [hε, hv1 τ jj x hx, mulVec_single_one']
  have hlK : (l : ↥LL.1) ≠ 0 := by
    have h := (map_ne_zero (algebraMap ℚ_[l] ↥LL.1)).2
      (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero : (l : ℚ_[l]) ≠ 0)
    rwa [map_natCast] at h
  have hl0 : ((l : ℕ) : (↥LL.1)⟦X⟧⟦X⟧) ≠ 0 := fun h => hlK (by
    have := congrArg (fun f => PowerSeries.constantCoeff (PowerSeries.constantCoeff f)) h
    simpa using this)
  refine ⟨ε, fun τ => ?_, fun τ => ?_, fun τ i jj k => ?_⟩
  · refine Matrix.ext fun i jj => ?_
    obtain ⟨x, hx⟩ := hcol τ jj
    rw [Matrix.map_apply, ← hv0 τ jj x hx i,
      GlobalTheory.T.crystal_coordinates_constantCoeff_eq l a e _ _ (thetaW a LL) ϖ ι EE c hsemi sh hsh PP S₀ p₀ p₁ δ j j₀ hδ hj₀ hjp lam₀ lam₁ hl₀ hl₁ hv₀ hv₁,
      hv1 τ jj x hx, Matrix.one_apply, Pi.single_apply]
    split_ifs <;> simp
  · refine Matrix.ext fun i jj => ?_
    obtain ⟨x, hx⟩ := hcol (τ - 1) jj
    have hlI : ((l : ℕ) : PP.A) ∈ PP.I := by rw [hI]; exact Ideal.mem_span_singleton_self _
    obtain ⟨n, k, hn⟩ := exists_isFrac ((l : ℕ) : PP.A) (EE.Φ PP ⟨_, hlI⟩ (EE.tr p₁ x))
    have G₀ := GlobalTheory.T.crystal_frobenius_breuilKisin_coordinates l a e _ _ (thetaW a LL) ϖ ι P EE c hsemi hfr PP hlI p₀ j PowerSeries.C φ₂
      (fun τ w => (hjp τ w).1) hjφ hφC (PowerSeries.C_injective) lam₀ hl₀ hv₀ _ n k hn τ i
    have G₁ := GlobalTheory.T.crystal_frobenius_breuilKisin_coordinates l a e _ _ (thetaW a LL) ϖ ι P EE c hsemi hfr PP hlI p₁ j sh φ₂
      (fun τ w => (hjp τ w).2) hjφ hφsh (fun f g h => by rw [← hsh0 f, ← hsh0 g, h]) lam₁ hl₁ hv₁ _ n k hn
    have hy1 := hv1 (τ - 1) jj x hx
    have hy0 : ∀ m, lam₀ (EE.tr p₁ x) (τ - 1) m = ε (τ - 1) m jj := hv0 (τ - 1) jj x hx
    have hE := congrFun (hε n τ) i
    rw [G₀] at hE
    simp only [Matrix.mulVec, dotProduct, G₁, hy1, hy0] at hE
    have key : ((l : ℕ) : (↥LL.1)⟦X⟧⟦X⟧) ^ k *
        (((P.mx (τ - 1)).map (frob (↥LL.1) l)).map PowerSeries.C * (ε (τ - 1)).map φ₂) i jj =
        ((l : ℕ) : (↥LL.1)⟦X⟧⟦X⟧) ^ k * (ε τ * ((P.mx (τ - 1)).map (frob (↥LL.1) l)).map sh) i jj := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      have h1 : ∀ q, φ₂ ((Pi.single jj (1 : (↥LL.1)⟦X⟧⟦X⟧) : ι → (↥LL.1)⟦X⟧⟦X⟧) q) =
          (Pi.single jj 1 : ι → (↥LL.1)⟦X⟧⟦X⟧) q := fun q => by
        by_cases h : q = jj
        · subst h; simp
        · simp [Pi.single_eq_of_ne h]
      simp only [h1] at hE
      simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
        Finset.mem_univ, if_true] at hE
      simp only [Matrix.map_apply] at hE ⊢
      rw [hE, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    exact (mul_left_cancel₀ (pow_ne_zero k hl0) key).symm
  · obtain ⟨x, hx⟩ := hcol τ jj
    rw [← hv0 τ jj x hx i]
    exact GlobalTheory.T.factorial_mul_crystalCoord_coeff_mem l a e _ _ (thetaW a LL) ϖ ι P EE c hcM PP p₀ j hS' lam₀ hl₀ hv₀ _ τ i k

end GlobalTheory.CrysStrat
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCrystalStratificationMatrixStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_integral_crystal_stratification_matrix : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∀ (sh : (↥LL.1)⟦X⟧ →+* (↥LL.1)⟦X⟧⟦X⟧) (φ₂ : (↥LL.1)⟦X⟧⟦X⟧ →+* (↥LL.1)⟦X⟧⟦X⟧), (∀ (f : (↥LL.1)⟦X⟧) (i : ℕ), (i.factorial : (↥LL.1)⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := ↥LL.1))^[i] f) → (∀ f : (↥LL.1)⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob (↥LL.1) l f)) → (∀ f : (↥LL.1)⟦X⟧, φ₂ (sh f) = sh (frob (↥LL.1) l f)) → ∃ ε : ZMod a → Matrix ι ι (↥LL.1)⟦X⟧⟦X⟧, (∀ τ, (ε τ).map PowerSeries.constantCoeff = 1) ∧ (∀ τ, ε τ * ((P.mx (τ - 1)).map (frob (↥LL.1) l)).map sh = ((P.mx (τ - 1)).map (frob (↥LL.1) l)).map PowerSeries.C * (ε (τ - 1)).map φ₂) ∧ ∀ (τ : ZMod a) (i j : ι) (k : ℕ), (k.factorial : (↥LL.1)⟦X⟧) * coeff k (ε τ i j) ∈ S (↥(OL LL)) (↥LL.1) e := by
  first | exact @GlobalTheory.CrysStrat.exists_stratification | exact GlobalTheory.CrysStrat.exists_stratification | (intros; apply GlobalTheory.CrysStrat.exists_stratification <;> assumption)
end
end
