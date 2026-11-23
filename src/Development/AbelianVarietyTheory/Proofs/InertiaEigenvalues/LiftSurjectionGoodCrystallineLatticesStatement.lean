module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.AdmissibleSignatures
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineClassFromMonodromyKernelElement
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleTameDescentGoodLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusPotentialCocycleClassStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisClassOfMonodromyEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsExactTripleBreuilKisinOfShortExactLatticesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodCoefficientRingPadicIntegersFinExt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsJumpVOfInjective
public import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CrystallineSubrepresentation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeHomLiftsBreuilKisinDescentHomStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftingTheoremPhiModulesExactTriple
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowDivisibilityOfDescentDatumStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameBreuilKisinDatumExists
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZetaMemPowInvPhiModuleLatticeStatement
import Mathlib.Algebra.Order.Star.Int

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineClassFromMonodromyKernelElementStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.crystalline_class_from_monodromy_kernel_element : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (N η H : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ), GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.Numerics l e N η H Sig U → ∀ T : QLat LL, IsGood a ϖ Pl T Sig U → ∀ Pk : Pack a ϖ η H T, ∀ c ∈ latticeFiniteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.L, ∃ y ∈ Pk.D.Y, Pk.D.Mon y = 0 ∧ Pk.R.ClassOf y ((l : ↥LL.1) ^ GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eW N (maxPeriod l Sig) • c) := by
  first | exact @GlobalTheory.BKGal.ExtClass.main | exact GlobalTheory.BKGal.ExtClass.main | (intros; apply GlobalTheory.BKGal.ExtClass.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGoodLatticeKernelOfSurjectionGoodLattice

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.KerGood

theorem map_aeval {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (F : M →ₗ[R] N) (A : Module.End R M) (A' : Module.End R N) (hA : ∀ y, F (A y) = A' (F y))
    (p : Polynomial R) (y : M) : F (Polynomial.aeval A p y) = Polynomial.aeval A' p (F y) := by
  induction p using Polynomial.induction_on generalizing y with
  | C c => simp [Module.algebraMap_end_apply]
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial n c h =>
    simp only [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply] at h ⊢
    rw [h (A y), hA]

theorem isGood_of_injective (hF : GlobalTheory.Published.FontaineBcris) {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a]
    {ϖ : PiSys l e} {LL : FinExt l} {Pl : LocPrime l} {AI : LocAinf l Pl} (hs : IsStd Pl AI)
    {Sig : Finset (ZMod e)} {U : Finset ℤ} {T₀ T₁ : QLat LL} (f : T₀.V →ₗ[↥LL.1] T₁.V)
    (hf : Function.Injective f) (he : ∀ g x, f (T₀.ρ g x) = T₁.ρ g (f x))
    (hT : IsGood a ϖ Pl T₁ Sig U) : IsGood a ϖ Pl T₀ Sig U := by
  refine ⟨?_, ?_, ?_⟩
  · have hS := (GlobalTheory.RegularRing.fontaineFormalism hF l Pl AI hs).2.2.2.1 (ϖ.field a) LL
    exact hS _ (resF T₁ (ϖ.field a)).ρ _ (resF T₀ (ϖ.field a)).ρ f (fun g x => he _ x) hf hT.crys
  · intro γ hγ w hw x hx
    obtain ⟨r, hr⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hf)
    have hrf : ∀ v, r (f v) = v := fun v => LinearMap.congr_fun hr v
    have hRF : ∀ y, GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB (Qp := ℚ_[l]) (B := Pl.R.B) r
        (GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB (Qp := ℚ_[l]) (B := Pl.R.B) f y) = y := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB, hrf]
      | add y z hy hz => simp only [map_add (f := _), hy, hz]
    have hFi : Function.Injective (GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB (Qp := ℚ_[l]) (B := Pl.R.B) f) :=
      Function.LeftInverse.injective hRF
    have hFx := GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB_mem (Pl.PD (ϖ.field a)) (ρ := (resF T₀ (ϖ.field a)).ρ)
      (ρ' := (resF T₁ (ϖ.field a)).ρ) (f := f) (fun g x => he _ x) x hx
    have h1 := hT.type γ hγ w hw _ hFx
    have hc : ∀ y, GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB (Qp := ℚ_[l]) (B := Pl.R.B) f
        (actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T₀.ρ γ y) =
        actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T₁.ρ γ (GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB (Qp := ℚ_[l]) (B := Pl.R.B) f y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB, actVB, he]
      | add y z hy hz => simp only [map_add (f := _), hy, hz]
    apply hFi
    exact (map_aeval _ _ _ hc _ x).trans (h1.trans (map_zero _).symm)
  · intro τ b hb
    exact hT.jumps τ b (GlobalTheory.HTW.isJumpV_of_injective _ _ T₁.ρ f hf he τ b hb)

theorem main : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (Sig : Finset (ZMod e)) (U : Finset ℤ) (T₁ T₂ : QLat LL) (g : LatHom T₁.L T₂.L), g.Onto → IsGood a ϖ Pl T₁ Sig U → ∃ (T₀ : QLat LL) (f : LatHom T₀.L T₁.L), IsSESLat (Qp := ℚ_[l]) f g ∧ IsGood a ϖ Pl T₀ Sig U := by
  intro hF l _ a e _ _ ϖ LL _ _ Pl AI hs Sig U T₁ T₂ g hg hT
  obtain ⟨⟨_, hD, hFr⟩, -⟩ := GlobalTheory.LocalIntegers.goodO_integers l LL
  have hden : Formalism.MainNotions.LiftingTheory.lker_Den ↥LL.1 ↥(OL LL) := by
    intro c
    obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.surj (nonZeroDivisors ↥(OL LL)) c
    refine ⟨s, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2, x, ?_⟩
    rw [mul_comm]
    exact hxs
  have hinj : Function.Injective (Formalism.MainNotions.LiftingTheory.lker_ι g hg hden).f := fun x y h => Subtype.ext h
  refine ⟨Formalism.MainNotions.LiftingTheory.lker_T₀ g hg hden, Formalism.MainNotions.LiftingTheory.lker_ι g hg hden, ?_,
    isGood_of_injective hF hs _ hinj (Formalism.MainNotions.LiftingTheory.lker_ι g hg hden).equiv hT⟩
  exact ⟨hinj, Formalism.MainNotions.LiftingTheory.lker_surj g hg, hg,
    fun x => ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩, fun y hy => hy⟩

end GlobalTheory.KerGood
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGoodLatticeKernelOfSurjectionGoodLatticeStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.isGoodLattice_kernel_of_surjection_goodLattice : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (Sig : Finset (ZMod e)) (U : Finset ℤ) (T₁ T₂ : QLat LL) (g : LatHom T₁.L T₂.L), g.Onto → IsGood a ϖ Pl T₁ Sig U → ∃ (T₀ : QLat LL) (f : LatHom T₀.L T₁.L), IsSESLat (Qp := ℚ_[l]) f g ∧ IsGood a ϖ Pl T₀ Sig U := by
  first | exact @GlobalTheory.KerGood.main | exact GlobalTheory.KerGood.main | (intros; apply GlobalTheory.KerGood.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftingTheoremPhiModulesExactTripleStatement

section

@[expose] public section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.liftingTheorem_phiModules_exact_triple : GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.Lifting := by
  first | exact @GlobalTheory.InertiaEigenvalues.lifting_along_exact_triple | exact GlobalTheory.InertiaEigenvalues.lifting_along_exact_triple | (intros; apply GlobalTheory.InertiaEigenvalues.lifting_along_exact_triple <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameBreuilKisinDatumExistsStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.tame_breuil_kisin_datum_exists : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (T₁ T₂ : LocLat (Gl l) ℚ_[l] K O) (R₁ : GalDat t ϖ (sQ l) D₁ T₁) (R₂ : GalDat t ϖ (sQ l) D₂ T₂) (f : LatHom T₁.L T₂.L) (F : BKHom D₁ D₂), IsMapOf R₁.I R₂.I f F.toHom → ∀ y c, R₁.ClassOf y c → R₂.ClassOf (F.app y) (f.post c) := by
  first | exact @GlobalTheory.CocycleNat.main | exact GlobalTheory.CocycleNat.main | (intros; apply GlobalTheory.CocycleNat.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftSurjectionGoodCrystallineLattices

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.TheoremT




theorem liftF_of_isGood : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (N η H : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ), GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.Numerics l e N η H Sig U → ∀ (T₁ T₂ : QLat LL) (g : LatHom T₁.L T₂.L), g.Onto → IsGood a ϖ Pl T₁ Sig U → IsGood a ϖ Pl T₂ Sig U → g.LiftF (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (7 * (N * maxPeriod l Sig + η * (N + maxPeriod l Sig))) := by
  intro hBS hFon l _ a e _ _ ϖ LL _ _ Pl AI hStd N η H Sig U hNum T₁ T₂ g hg hG₁ hG₂
  have hN2 := hNum.two_le
  have hlarge := hNum.large
  have hHN : 4 * H ≤ H * N ^ 2 := by
    have h4 : 4 ≤ N ^ 2 := by nlinarith
    calc 4 * H = H * 4 := by ring
      _ ≤ H * N ^ 2 := Nat.mul_le_mul_left H h4
  have hl2 : l ≠ 2 := by intro h; subst h; nlinarith
  have h8 : 8 * H + 1 < l := by nlinarith
  obtain ⟨T₀, f, hSES, hG₀⟩ := GlobalTheory.T.isGoodLattice_kernel_of_surjection_goodLattice hFon l a e ϖ LL Pl AI hStd Sig U T₁ T₂ g hg hG₁
  obtain ⟨P₀, -⟩ := GlobalTheory.T.exists_breuilKisinModule_tameDescent_goodLattice hBS hFon l a e ϖ LL hl2 Pl AI hStd η H Sig U hNum.range_U T₀ hG₀
  obtain ⟨P₁, hP₁⟩ := GlobalTheory.T.exists_breuilKisinModule_tameDescent_goodLattice hBS hFon l a e ϖ LL hl2 Pl AI hStd η H Sig U hNum.range_U T₁ hG₁
  obtain ⟨P₂, hP₂⟩ := GlobalTheory.T.exists_breuilKisinModule_tameDescent_goodLattice hBS hFon l a e ϖ LL hl2 Pl AI hStd η H Sig U hNum.range_U T₂ hG₂
  obtain ⟨F, hF⟩ := GlobalTheory.T.latticeHom_lifts_breuilKisinDescentHom hBS l a e ϖ LL η H T₀ T₁ P₀ P₁ f
  obtain ⟨G, hG⟩ := GlobalTheory.T.latticeHom_lifts_breuilKisinDescentHom hBS l a e ϖ LL η H T₁ T₂ P₁ P₂ g
  have hEx := GlobalTheory.T.isExactTriple_breuilKisin_of_shortExactLattices l a e ϖ LL (Fin P₀.n) (Fin P₁.n) (Fin P₂.n) P₀.D.toPhiMod P₁.D.toPhiMod
    P₂.D.toPhiMod T₀ T₁ T₂ P₀.R.I P₁.R.I P₂.R.I f g F.toHom G.toHom hSES hF hG
  have hAdm : GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.Admissible l e N η H Sig U :=
    ⟨hNum.frob_mem, hNum.zero_mem_Sig, hNum.card_Sig, hNum.two_le, hNum.range_U, hNum.zero_mem_U,
      hNum.card_U, hNum.one_le, hNum.lt, hNum.large⟩
  have hpot₂ := GlobalTheory.T.exists_frobeniusPotential_cocycle_class l a e _ _ (thetaW a LL) ϖ (Fin P₂.n) η H P₂.D T₂ P₂.R
  unfold LatHom.LiftF
  intro c hc

  obtain ⟨y₂, hy₂, hMon₂, hCl₂⟩ :=
    GlobalTheory.T.crystalline_class_from_monodromy_kernel_element hBS hFon l a e ϖ LL Pl AI hStd N η H Sig U hNum T₂ hG₂ P₂ c hc

  obtain ⟨y₂', hy₂', m₂, hm₂, hsum⟩ :=
    Submodule.mem_sup.1 ((GlobalTheory.T.prime_pow_divisibility_of_descentDatum _ _ l e a _ η H P₂.D).2 y₂ hy₂)
  have hrew : y₂' + P₂.D.phi m₂ = (l : ↥LL.1) ^ η • y₂ + (P₂.D.phi m₂ - m₂) := by
    rw [← hsum]; abel
  have hMon₂' : P₂.D.Mon (y₂' + P₂.D.phi m₂) = 0 := by
    rw [hrew, P₂.D.Mon_add_phi_sub _ (PhiMod.M_le_Man _ hm₂.1), LinearMap.map_smul, hMon₂, smul_zero]
  have hCl₂' : P₂.R.ClassOf (y₂' + P₂.D.phi m₂)
      ((l : ↥LL.1) ^ η • (l : ↥LL.1) ^ GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eW N (maxPeriod l Sig) • c) := by
    rw [hrew]
    exact hpot₂.2.2.2 _ _ m₂ hm₂ (hpot₂.2.2.1 _ _ η hCl₂)

  obtain ⟨y', hy', m, hm, hMon, hGy⟩ :=
    GlobalTheory.T.liftingTheorem_phiModules_exact_triple _ _ l e a _ _ _ η H P₀.D P₁.D P₂.D F G N Sig U
      ⟨hEx, hNum, hP₁, hP₂.chars_subset⟩ y₂' hy₂' m₂ hm₂ hMon₂'

  have hζ := GlobalTheory.T.zeta_mem_pow_inv_phiModule_lattice _ _ l e a _ N η H Sig U hAdm P₁.D hP₁ y' hy' m hm hMon
  obtain ⟨κ₁, hκ₁, hCl₁⟩ := GlobalTheory.T.galoisClass_of_monodromy_eq_zero hFon l a e ϖ LL (Fin P₁.n) η H P₁.D T₁ P₁.R Pl AI hStd hNum.lt h8
    _ (GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.add_phi_mem_Y hy' hm) hMon _ hζ

  have hnat := GlobalTheory.T.tame_breuil_kisin_datum_exists l a e _ _ (thetaW a LL) ϖ (Fin P₁.n) (Fin P₂.n) η H P₁.D P₂.D T₁ T₂ P₁.R P₂.R g G hG
    _ _ hCl₁
  have happ : G.app ((l : ↥LL.1) ^ GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.cOne l η Sig • (y' + P₁.D.phi m)) =
      (l : ↥LL.1) ^ (GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.cOne l η Sig + GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.kExp N η (maxPeriod l Sig)) •
        (y₂' + P₂.D.phi m₂) := by
    have happ0 : ∀ (k : ↥LL.1) (v : Vec (↥LL.1) a (Fin P₁.n)), G.app (k • v) = k • G.app v := by
      intro k v
      ext1 τ
      simp only [Hom.app_apply, Pi.smul_apply, Matrix.mulVec_smul]
    rw [happ0, hGy, smul_smul, ← pow_add]
  rw [happ] at hnat
  have hCl := hpot₂.2.2.1 _ _ (GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.cOne l η Sig + GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.kExp N η (maxPeriod l Sig)) hCl₂'
  rw [smul_smul, smul_smul, ← pow_add, ← pow_add] at hCl
  have hB := hpot₂.2.1 _ _ _ hnat hCl

  have hexp : GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.cOne l η Sig + GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.kExp N η (maxPeriod l Sig) + η +
      GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eW N (maxPeriod l Sig) ≤ 7 * (N * maxPeriod l Sig + η * (N + maxPeriod l Sig)) := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.cOne, GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.kExp, GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.c₂, GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.c₁,
      GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eL, GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eW]
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
    generalize maxPeriod l Sig = r
    have h1 : n + 2 - 1 = n + 1 := by omega
    rw [h1]
    nlinarith [Nat.zero_le (n * r), Nat.zero_le (η * n), Nat.zero_le (η * r)]
  rw [← algebraMap_smul (↥LL.1), map_pow, map_natCast, Pl.PD_p,
    ← Nat.sub_add_cancel hexp, pow_add, mul_smul]
  obtain ⟨β, hβ, hβeq⟩ : ∃ β ∈ latticeCoboundaries T₂.L, (l : ↥LL.1) ^ (GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.cOne l η Sig + GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.kExp N η (maxPeriod l Sig) + η +
      GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eW N (maxPeriod l Sig)) • c = LatHom.post g κ₁ - β := ⟨_, hB, by abel⟩
  rw [hβeq, smul_sub]
  refine sub_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
  · rw [← map_natCast (algebraMap ↥(OL LL) ↥LL.1) l, ← map_pow, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem hκ₁)
  · rw [← map_natCast (algebraMap ↥(OL LL) ↥LL.1) l, ← map_pow, algebraMap_smul]
    exact Submodule.smul_mem _ _ hβ

end GlobalTheory.TheoremT
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftSurjectionGoodCrystallineLatticesStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.lift_surjection_good_crystalline_lattices : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (N η H : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ), GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.Numerics l e N η H Sig U → ∀ (T₁ T₂ : QLat LL) (g : LatHom T₁.L T₂.L), g.Onto → IsGood a ϖ Pl T₁ Sig U → IsGood a ϖ Pl T₂ Sig U → g.LiftF (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (7 * (N * maxPeriod l Sig + η * (N + maxPeriod l Sig))) := by
  first | exact @GlobalTheory.TheoremT.liftF_of_isGood | exact GlobalTheory.TheoremT.liftF_of_isGood | (intros; apply GlobalTheory.TheoremT.liftF_of_isGood <;> assumption)
end
end
