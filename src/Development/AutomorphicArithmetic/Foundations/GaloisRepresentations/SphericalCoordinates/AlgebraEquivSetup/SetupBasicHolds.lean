module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ExistsClose
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HenselRoot
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCodiffGen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCodiffUnit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PDeltaEx
import Mathlib.RingTheory.Complex
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PDomSt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PFormCoord
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PFormOKSt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PFormPerfSt
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PIdemEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PKqEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.POrient
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PPerfCof
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PPerfOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PPosGen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PQuadEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRealGen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRealIso
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRepAdj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRepEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRepLaws
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSetupBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSetupEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSigSt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTraceType
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PUnitMod

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PAtPEx

section

section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pAtPEx :
    KqEx → UEx → OrbEx → LiftEx → AtPEx := by
  intro hK hU hO hL E _ _ _ A p _ hs
  obtain ⟨Kq, hω, hKq, hgen⟩ := hK E A
  obtain ⟨s, iotaC, hsC⟩ := hL E A.τ₀
  haveI : CharZero (PadicAlgCl p) := charZero_of_injective_algebraMap (algebraMap ℚ_[p] (PadicAlgCl p)).injective
  haveI hAlg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert (AlgebraicClosure.isAlgebraic ℚ)
  let iotaA : AlgebraicClosure ℚ →ₐ[ℚ] PadicAlgCl p := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let iotaP : AlgebraicClosure ℚ →+* PadicAlgCl p := iotaA.toRingHom
  let τ₁ : E →+* PadicAlgCl p := iotaP.comp s
  obtain ⟨u, ρ, hover, hρ⟩ := hU E A p hs Kq hω hgen τ₁
  obtain ⟨m, emb, w, hw, hov, hinj, hall⟩ := hO E p Kq u τ₁ hover
  exact ⟨{ Kq := Kq, hKq := hKq, u := u, m := m, emb := emb, emb_over := hov, emb_inj := hinj, emb_all := hall,
           iotaP := iotaP, iotaC := iotaC, ρp := ρ, ρp_eq := ⟨hω, hρ⟩, s := s, s_C := hsC, w := w,
           s_P := fun x => by rw [hw]; rfl }⟩
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PBarEx

section

@[expose] public section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pBarEx :
    BarEx := by
  intro E _ _ _
  refine ⟨(IsCMField.ringOfIntegersComplexConj E).toRingEquiv, fun a => ?_⟩
  exact IsCMField.coe_ringOfIntegersComplexConj E a
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PDiagTrace

section

section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pDiagTrace :
    DiagTrace := by
  intro I _ a M hM
  classical
  have hdec : M = ∑ k, (LinearMap.single ℝ (fun _ : I => ℂ) k) ∘ₗ
      ((Algebra.lmul ℝ ℂ (a k)) ∘ₗ LinearMap.proj k) := by
    refine LinearMap.ext fun z => funext fun j => ?_
    simp [hM, LinearMap.sum_apply, Finset.sum_apply, Pi.single_apply]
  have hk : ∀ k : I, LinearMap.trace ℝ (I → ℂ) ((LinearMap.single ℝ (fun _ : I => ℂ) k) ∘ₗ
      ((Algebra.lmul ℝ ℂ (a k)) ∘ₗ LinearMap.proj k)) = 2 * (a k).re := by
    intro k
    rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc, LinearMap.proj_comp_single_same,
      LinearMap.comp_id, ← Algebra.trace_complex_apply, Algebra.trace_apply]

  rw [hdec, map_sum, Finset.sum_congr rfl (fun k _ => hk k), Complex.re_sum, Finset.mul_sum]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PHdSign

section

@[expose] public section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pHdSign :
    HdSign := by
  intro E _ _ _ A n τ i
  have hcim : ∀ σ : E →+* ℂ, (σ (A.c : E)).im = 0 := by
    intro σ
    have h1 : σ ((A.bar A.c : 𝓞 E) : E) = (starRingEnd ℂ) (σ (A.c : E)) := by
      rw [A.bar_eq, IsCMField.complexEmbedding_complexConj]
    rw [A.c_real] at h1
    exact Complex.conj_eq_iff_im.mp h1.symm
  have hre : InfinitePlace.mk τ = InfinitePlace.mk A.τ₀ → (τ (A.c : E)).re < 0 := by
    intro h
    rcases InfinitePlace.mk_eq_iff.mp h with h' | h'
    · rw [h']
      exact A.c_neg
    · have h2 := A.c_neg
      rw [← h', NumberField.ComplexEmbedding.conjugate_coe_eq] at h2
      simpa using h2
  have hδ : (τ A.δ).re = 0 := by
    have h1 : τ ((IsCMField.complexConj E) A.δ) = (starRingEnd ℂ) (τ A.δ) :=
      IsCMField.complexEmbedding_complexConj E τ A.δ
    rw [A.δ_im, map_neg] at h1
    have h2 := congrArg Complex.re h1
    simp at h2
    linarith
  have hc := hcim τ
  refine ⟨?_, hδ, ?_, ?_⟩
  · simp only [Arith.hd, Arith.dg]
    split_ifs <;> simp [Complex.mul_im, hc]
  · rintro ⟨h, hi0⟩
    have hr := hre h
    simp only [Arith.hd, Arith.dg, if_pos hi0]
    simp
    linarith
  · intro hn
    by_cases hp : InfinitePlace.mk τ = InfinitePlace.mk A.τ₀
    · have hi : (i : ℕ) ≠ 0 := fun hi0 => hn ⟨hp, hi0⟩
      have hr := hre hp
      simp only [Arith.hd, Arith.dg, if_neg hi]
      simp [Complex.mul_re, hc]
      nlinarith
    · have hr : 0 < (τ (A.c : E)).re := A.c_pos τ hp
      simp only [Arith.hd, Arith.dg]
      split_ifs
      · simp
        linarith
      · simp [Complex.mul_re, hc]
        nlinarith
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PLiftEx

section

section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pLiftEx :
    LiftEx := by
  unfold UpperTheory.Gal.W2.Seed.LiftEx
  intro E _ _ τ₀
  let sA : E →ₐ[ℚ] AlgebraicClosure ℚ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra E (AlgebraicClosure ℚ) := sA.toRingHom.toAlgebra
  letI : Algebra E ℂ := τ₀.toAlgebra
  haveI : IsScalarTower ℚ E (AlgebraicClosure ℚ) :=
    IsScalarTower.of_algebraMap_eq (fun x => (sA.commutes x).symm)
  haveI hQ : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : Algebra.IsAlgebraic E (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) E
  let iA : AlgebraicClosure ℚ →ₐ[E] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨sA.toRingHom, iA.toRingHom, fun x => ?_⟩
  exact iA.commutes x
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.POrbEx

section

section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pOrbEx :
    OrbEx := by
  intro E _ _ p _ Kq u τ₁ h₁
  classical
  let S := {τ : E →+* PadicAlgCl p // LiesOver Kq u τ}
  let R : Setoid S :=
    { r := fun a b => ∃ σ : Gal(PadicAlgCl p/ℚ_[p]),
        b.1 = ((σ.toRingEquiv : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p).comp a.1
      iseqv := ⟨fun a => ⟨1, by ext x; simp⟩,
        fun {a b} ⟨σ, hσ⟩ => ⟨σ⁻¹, by rw [hσ]; ext x; simp⟩,
        fun {a b c} ⟨σ, hσ⟩ ⟨ρ, hρ⟩ => ⟨ρ * σ, by rw [hρ, hσ]; ext x; simp⟩⟩ }
  haveI : Finite (E →+* PadicAlgCl p) := inferInstance
  haveI : Finite S := Subtype.finite
  haveI : Finite (Quotient R) := Quotient.finite _
  let s₁ : S := ⟨τ₁, h₁⟩
  let rep : Quotient R → S := fun q => if q = Quotient.mk R s₁ then s₁ else q.out
  have hrep : ∀ q, Quotient.mk R (rep q) = q := by
    intro q
    by_cases hq : q = Quotient.mk R s₁
    · simp only [rep, if_pos hq]
      exact hq.symm
    · simp only [rep, if_neg hq]
      exact Quotient.out_eq q
  let eq := Finite.equivFin (Quotient R)
  refine ⟨Nat.card (Quotient R), fun i => (rep (eq.symm i)).1, eq (Quotient.mk R s₁), ?_, ?_, ?_, ?_⟩
  · simp [rep, s₁]
  · intro i
    exact (rep _).2
  · intro i j σ hij
    apply eq.symm.injective
    rw [← hrep (eq.symm i), ← hrep (eq.symm j)]
    exact Quotient.sound ⟨σ, hij.symm⟩
  · intro τ hτ
    obtain ⟨σ, hσ⟩ := Quotient.exact (hrep (Quotient.mk R ⟨τ, hτ⟩))
    exact ⟨eq (Quotient.mk R ⟨τ, hτ⟩), σ, by simpa using hσ⟩
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.SetupBasicHolds

section

@[expose] public section

namespace UpperTheory.Gal.W2.Seed

theorem BarEx_holds : BarEx := pBarEx
theorem CEx_holds : CEx := pCEx
theorem CodiffGen_holds : CodiffGen := pCodiffGen
theorem DeltaEx_holds : DeltaEx := pDeltaEx
theorem DiagTrace_holds : DiagTrace := pDiagTrace
theorem FormOKSt_holds : FormOKSt := pFormOKSt
theorem FormPerfSt_holds : FormPerfSt := pFormPerfSt
theorem HdSign_holds : HdSign := pHdSign
theorem IdemEx_holds : IdemEx := pIdemEx
theorem LiftEx_holds : LiftEx := pLiftEx
theorem OrbEx_holds : OrbEx := pOrbEx
theorem PerfCof_holds : PerfCof := pPerfCof
theorem PerfOf_holds : PerfOf := pPerfOf
theorem QuadEx_holds : QuadEx := pQuadEx
theorem RepAdj_holds : RepAdj := pRepAdj
theorem RepEx_holds : RepEx := pRepEx
theorem RepLaws_holds : RepLaws := pRepLaws
theorem SetupBasic_holds : SetupBasic := pSetupBasic
theorem TraceType_holds : TraceType := pTraceType
theorem UEx_holds : UEx := pUEx
theorem UnitMod_holds : UnitMod := pUnitMod
theorem CodiffUnit_holds : CodiffUnit := pCodiffUnit UnitMod_holds
theorem FormCoord_holds : FormCoord := pFormCoord TraceType_holds
theorem KqEx_holds : KqEx := pKqEx TraceType_holds
theorem Orient_holds : Orient := pOrient TraceType_holds HdSign_holds
theorem RealIso_holds : RealIso := pRealIso TraceType_holds
theorem SigSt_holds : SigSt := pSigSt HdSign_holds
theorem AtPEx_holds : AtPEx := pAtPEx KqEx_holds UEx_holds OrbEx_holds LiftEx_holds
theorem DomSt_holds : DomSt := pDomSt TraceType_holds RealIso_holds FormCoord_holds HdSign_holds DiagTrace_holds
theorem PosGen_holds : PosGen := pPosGen CodiffUnit_holds
theorem RealGen_holds : RealGen := pRealGen CodiffGen_holds CodiffUnit_holds
theorem SetupEx_holds : SetupEx := pSetupEx FormOKSt_holds FormPerfSt_holds SigSt_holds DomSt_holds AtPEx_holds RepEx_holds RepLaws_holds RepAdj_holds Orient_holds

end UpperTheory.Gal.W2.Seed
end
end
