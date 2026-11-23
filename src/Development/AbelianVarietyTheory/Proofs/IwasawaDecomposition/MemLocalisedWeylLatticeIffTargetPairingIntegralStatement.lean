module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.KerEntHyp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominantWeightPolynomialFunctionalMinorsStatement
public import Formalism.UnipotentAdelicQuotients.WeylLatDual
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemLocalizedWeylLatticeIffDetTwistedEval
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MainProof
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemLocalizedWeylLatticeIffDetTwistedEvalStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_localizedWeylLattice_iff_detTwisted_eval : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ i, i < (I.rec7 l Z).R.m → ∀ (c' : (I.stp u μ (i + 1)).Cl) (z : VV B.LL (lamT (B.hcW u) (i + 1))), (z ∈ locW B.places w (delAtr B.fields.emb (lamT (B.hcW u) (i + 1)) ((I.stp u μ (i + 1)).Lsh c'.1 ((I.stp u μ (i + 1)).rep c'))) ↔ (fun y => (∏ τ, (Bs u μ w (i + 1) c' τ).det ^ (-((I.rec7 l Z).chTw u μ).sDiv i τ)) * atBas Pl w (Bs u μ w (i + 1) c') (show MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL from z.1) y) ∈ WeylLatticeDuality.DelW ((I.rec7 l Z).what₂.places.resChar w) (I.rec7 l Z).what₂.Tau ((I.rec7 l Z).R.N (i + 1)) (extNu ((I.rec7 l Z).R.N (i + 1)) (nuT (I.rec7 l Z) u i))) := by
  first | exact @GlobalTheory.Mem.LocDictT.mem_locW_iff_delW | exact GlobalTheory.Mem.LocDictT.mem_locW_iff_delW | (intros; apply GlobalTheory.Mem.LocDictT.mem_locW_iff_delW <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionPolynomialEqOfFunctionEqCoefficient

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.PolyId

theorem shiftOf_lamT_succ {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc) (i : ℕ)
    (hi : i < R.m) (τ : ι) : shiftOf (Col2.lamT hc (i + 1)) τ = -C.sDiv i τ := by
  have hN : R.N (i + 1) = R.k + (i + 1) * (R.t + 1) := rfl
  have h1 : 1 ≤ (i + 1) * (R.t + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hpos : 0 < R.N (i + 1) := by rw [hN]; omega
  have hk : ¬ (R.N (i + 1) - 1 < R.k) := by rw [hN]; omega
  have hq : (R.N (i + 1) - 1 - R.k) / (R.t + 1) = i := by
    rw [hN]
    have hm : (i + 1) * (R.t + 1) = i * (R.t + 1) + R.t + 1 := by ring
    rw [hm, show R.k + (i * (R.t + 1) + R.t + 1) - 1 - R.k = R.t + i * (R.t + 1) by omega,
      Nat.add_mul_div_right _ _ (Nat.succ_pos _), Nat.div_eq_of_lt (Nat.lt_succ_self _), zero_add]
  have h2 := C.sDiv_eq i hi τ
  obtain ⟨c, hc'⟩ := R.t_odd
  have hcq : (R.t : ℚ) = 2 * c + 1 := by exact_mod_cast hc'
  have e2 : (R.t + 1) / 2 = c + 1 := by omega
  simp only [shiftOf, DomWeight.detShift, dif_pos hpos, Col2.lamT, Col2.shW, Examples₂.lamOf, dif_pos (show i + 1 ≤ R.m by omega), Examples₂.wtQ, dif_neg hk]
  simp only [hq, e2]
  have hw : -wG R ((hc τ).e ⟨i, hi⟩) (i + 1) = ((-C.sDiv i τ + ((i + 1) * (c + 1) : ℕ) : ℤ) : ℚ) := by
    push_cast
    rw [h2]
    simp only [wG, sExp, Ranks.N, Nat.add_sub_cancel]
    push_cast
    rw [hcq]
    ring
  rw [hw, Int.floor_intCast]
  push_cast
  ring

theorem secC_eq_of_evC_eq_evV : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Qp : I.ι → Finset ℕ) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)), I.StdO l Z Qp O → ∀ (u : B.Word) (μ : I.ι) (i : ℕ), i < (I.rec7 l Z).R.m → ∀ (z : VV B.LL (lamT (B.hcW u) (i + 1))) (v' : ValQ O u μ (i + 1)), evC O u μ (i + 1) v' = evV B.fields.emb (1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.fields.E) (lamT (B.hcW u) (i + 1)) B.embLL z → ((secC O u μ (i + 1) v' : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL)) = (show MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL from z.1) := by
  intro B X I hOk hP l Z Qp O hStd u μ i hi z v' h
  have hfun : fnOf (gramC (1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.fields.E) (embAt B.embLL B.fields.emb))
      (shiftOf (Col2.lamT (B.hcW u) (i + 1))) 1
      (MvPolynomial.map B.embLL ((secC O u μ (i + 1) v' : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL))) =
      fnOf (gramC (1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.fields.E) (embAt B.embLL B.fields.emb))
      (shiftOf (Col2.lamT (B.hcW u) (i + 1))) 1 (MvPolynomial.map B.embLL z.1) := by
    rw [← evV_apply]
    rw [← h]
    refine Eq.trans ?_ (evC_sec O u μ (i + 1) v').symm
    funext y
    have hfr := hStd.frm u μ (i + 1) y
    show _ = (∏ τ, (((I.rec7 l Z).chTw u μ).de (i + 1) y τ) ^ (-(((I.rec7 l Z).chTw u μ).sDiv i τ))) *
      GL3Theta.evFr (I.rec7 l Z) (MvPolynomial.map (I.rec7 l Z).what₂.embLL ((secC O u μ (i + 1) v' : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL))) ((O u μ).frm (i + 1) y)
    rw [hfr]
    simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, GL3Theta.evFr]
    congr 1
    · refine Finset.prod_congr rfl fun τ _ => ?_
      have hs : shiftOf (Col2.lamT (B.hcW u) (i + 1)) τ = -((I.rec7 l Z).chTw u μ).sDiv i τ :=
        shiftOf_lamT_succ ((I.rec7 l Z).chTw u μ) i hi τ
      rw [hs, Pi.one_apply, Matrix.one_mul]
      rfl
    · simp only [Pi.one_apply, Matrix.one_mul]
      rfl
  have h2 := fnOf_injective _ _ 1 (fun _ => by simp) (stdFrC (n := B.R.N (i + 1)) (embAt B.embLL B.fields.emb)) hfun
  exact MvPolynomial.map_injective _ B.embLL.injective h2

end GlobalTheory.Mem.Col2.PolyId
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionPolynomialEqOfFunctionEqCoefficientStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.sectionPolynomial_eq_of_function_eq_coefficient : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Qp : I.ι → Finset ℕ) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)), I.StdO l Z Qp O → ∀ (u : B.Word) (μ : I.ι) (i : ℕ), i < (I.rec7 l Z).R.m → ∀ (z : VV B.LL (lamT (B.hcW u) (i + 1))) (v' : ValQ O u μ (i + 1)), evC O u μ (i + 1) v' = evV B.fields.emb (1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.fields.E) (lamT (B.hcW u) (i + 1)) B.embLL z → ((secC O u μ (i + 1) v' : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL)) = (show MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL from z.1) := by
  first | exact @GlobalTheory.Mem.Col2.PolyId.secC_eq_of_evC_eq_evV | exact GlobalTheory.Mem.Col2.PolyId.secC_eq_of_evC_eq_evV | (intros; apply GlobalTheory.Mem.Col2.PolyId.secC_eq_of_evC_eq_evV <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylLatticeDualityPadicMinorsStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.weyl_lattice_duality_padic_minors : WeylLatticeDuality.Stmt :=
  GlobalTheory.WeylLatDualProof.mainProof
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemLocalisedWeylLatticeIffTargetPairingIntegral

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.IntDualT

theorem mem_locW_iff_prTC_le_one : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ i, i < (I.rec7 l Z).R.m → ∀ (c' : (I.stp u μ (i + 1)).Cl) (z : VV B.LL (lamT (B.hcW u) (i + 1))) (v' : ValQ O u μ (i + 1)), evC O u μ (i + 1) v' = evV B.fields.emb (1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.fields.E) (lamT (B.hcW u) (i + 1)) B.embLL z → (z ∈ locW B.places w (delAtr B.fields.emb (lamT (B.hcW u) (i + 1)) ((I.stp u μ (i + 1)).Lsh c'.1 ((I.stp u μ (i + 1)).rep c'))) ↔ ∀ J, ‖prTC Pl O Bs u μ w i c' v' J‖ ≤ 1) := by
  intro B X I hOk hPins l Z l0 Y O Pl Bs hQp hStd hBas hEnt hUnf hJets u μ w hLF i hi c' z v' hev
  have hfits := nuFits_tgt (I.rec7 l Z) u i hi
  have hF := canT_of Pl Bs (GlobalTheory.T.toy_entPl_canOnto _ Pl) u μ w i hi c' (secC O u μ (i + 1) v')
  have hspec := canInv_spec (I.rec7 l Z) w _ (nuD (I.rec7 l Z) u i) _ hF
  have hS := GlobalTheory.T.weyl_lattice_duality_padic_minors ((I.rec7 l Z).what₂.places.resChar w) _ (I.rec7 l Z).what₂.Tau (tauPl (I.rec7 l Z))
    (Formalism.L2.DIV.tauPl_bijective _) _ (nuD (I.rec7 l Z) u i) _ hfits.1 hfits.2
    (canInv (I.rec7 l Z) w _ (nuD (I.rec7 l Z) u i) (tgtFun Pl Bs u μ w i c' (secC O u μ (i + 1) v')))
  have hpol := GlobalTheory.T.sectionPolynomial_eq_of_function_eq_coefficient I hOk hPins l Z Y.Qp O hStd u μ i hi z v' hev
  rw [GlobalTheory.T.mem_localizedWeylLattice_iff_detTwisted_eval I hOk hPins l Z l0 Y O Pl Bs hQp hStd hBas hEnt hUnf hJets u μ w hLF i hi c' z]
  have hfun : (fun y => (∏ τ, (Bs u μ w (i + 1) c' τ).det ^ (-((I.rec7 l Z).chTw u μ).sDiv i τ)) *
      atBas Pl w (Bs u μ w (i + 1) c') (show MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL from z.1) y) =
      tgtFun Pl Bs u μ w i c' (secC O u μ (i + 1) v') := by
    funext y
    rw [← hpol]
    rfl
  rw [hfun, ← hspec]
  exact hS.symm

end GlobalTheory.Mem.IntDualT
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemLocalisedWeylLatticeIffTargetPairingIntegralStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_localisedWeylLattice_iff_targetPairing_integral : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ i, i < (I.rec7 l Z).R.m → ∀ (c' : (I.stp u μ (i + 1)).Cl) (z : VV B.LL (lamT (B.hcW u) (i + 1))) (v' : ValQ O u μ (i + 1)), evC O u μ (i + 1) v' = evV B.fields.emb (1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.fields.E) (lamT (B.hcW u) (i + 1)) B.embLL z → (z ∈ locW B.places w (delAtr B.fields.emb (lamT (B.hcW u) (i + 1)) ((I.stp u μ (i + 1)).Lsh c'.1 ((I.stp u μ (i + 1)).rep c'))) ↔ ∀ J, ‖prTC Pl O Bs u μ w i c' v' J‖ ≤ 1) := by
  first | exact @GlobalTheory.Mem.IntDualT.mem_locW_iff_prTC_le_one | exact GlobalTheory.Mem.IntDualT.mem_locW_iff_prTC_le_one | (intros; apply GlobalTheory.Mem.IntDualT.mem_locW_iff_prTC_le_one <;> assumption)
end
end
