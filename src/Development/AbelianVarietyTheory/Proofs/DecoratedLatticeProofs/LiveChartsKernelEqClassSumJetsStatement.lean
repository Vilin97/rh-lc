module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsRepsRepresentUnitaryDoubleCosetsStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueChainKernelEqClassSumJets

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf



namespace GlobalTheory.AdForm.KerVal

theorem eval_jetLin_jetC {ι : Type} [Fintype ι] {a b : ℕ} (c : ι → ℂ) (Θ : VCx ι a b → ℂ) (y : ι → Matrix (Fin b) (Fin b) ℂ)
    (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ) :
    MvPolynomial.eval (fun x : ι × Fin b × Fin b => y x.1 x.2.1 x.2.2) (jetLin (jetC c Θ) Q) =
      jetL c Θ (MvPolynomial.aeval (Sum.elim (fun x : ι × Fin b × Fin b => (MvPolynomial.C (y x.1 x.2.1 x.2.2) : FP ι a b))
        MvPolynomial.X) Q) := by
  induction Q using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | monomial m r =>
    have h1 : jetLin (jetC c Θ) (MvPolynomial.monomial m r) = r • MvPolynomial.monomial (Finsupp.comapDomain Sum.inl m Sum.inl_injective.injOn)
        (jetC c Θ (Finsupp.comapDomain Sum.inr m Sum.inr_injective.injOn)) := by
      have := (MvPolynomial.basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ).constr_basis ℂ (fun m =>
        (MvPolynomial.monomial (Finsupp.comapDomain Sum.inl m Sum.inl_injective.injOn)
          (jetC c Θ (Finsupp.comapDomain Sum.inr m Sum.inr_injective.injOn)) : MvPolynomial (ι × Fin b × Fin b) ℂ)) m
      rw [show (MvPolynomial.monomial m r : MvPolynomial _ ℂ) = r • MvPolynomial.monomial m 1 by simp [MvPolynomial.smul_monomial], map_smul]
      congr 1
    have h2 : MvPolynomial.aeval (Sum.elim (fun x : ι × Fin b × Fin b => (MvPolynomial.C (y x.1 x.2.1 x.2.2) : FP ι a b))
        MvPolynomial.X) (MvPolynomial.monomial m r) = (r * ∏ x : ι × Fin b × Fin b, y x.1 x.2.1 x.2.2 ^ m (Sum.inl x)) •
          MvPolynomial.monomial (Finsupp.comapDomain Sum.inr m Sum.inr_injective.injOn) 1 := by
      rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type, MvPolynomial.monomial_eq,
        Finsupp.prod_fintype _ _ (by simp)]
      simp [MvPolynomial.smul_eq_C_mul, mul_assoc]
    rw [h1, h2, MvPolynomial.smul_eval, LinearMap.map_smul, jetL_monomial, MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (by simp)]
    simp
    ring

theorem kmap_val {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
    {Ch : ℕ → Type} (A : TwDat I l Z u a Ch) (i : ℕ) (hab : B.R.N i ≤ B.R.N (i + 1)) (c : (I.chain l u a).cls i)
    (c' : (I.chain l u a).cls (i + 1)) (ψ : (I.chain l u a).Y i → ℂ) (Q : PY (I.rec7 l Z).what₂.Tau (B.R.N i))
    (hψ : ∀ y : (I.chain l u a).Y i, ψ y = evalAt y.1 Q * ∏ τ, (y.1 τ).det ^ (-(I.chain l u a).sSharp i τ))
    (y' : (I.chain l u a).Y (i + 1)) :
    (I.chain l u a).Kmap i c c' ψ y' =
      A.abelian₂ i c c' (subY hab y'.1 Q) * ∏ τ, (y'.1 τ).det ^ (-(I.chain l u a).sDiv i τ) := by
  have h1 : (I.chain l u a).sharp i ψ = fnOf (Gr B.fields.emb B.embLL (B.R.N i)) 0
      (fun τ => ((fr0 B.fields.emb B.embLL (B.R.N i)).1 τ)⁻¹) Q := by
    funext y
    have e := hψ y
    show (∏ τ, (y.1 τ).det ^ (I.chain l u a).sSharp i τ) * ψ y =
      (∏ τ, ((1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) ℂ)⁻¹ * y.1 τ).det ^ (0 : ℤ)) *
        MvPolynomial.eval (fun x => ((1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) ℂ)⁻¹ * y.1 x.1) x.2.1 x.2.2) Q
    rw [e]
    simp only [inv_one, Matrix.one_mul, zpow_zero, Finset.prod_const_one, one_mul]
    have : (∏ τ, (y.1 τ).det ^ (I.chain l u a).sSharp i τ) * ∏ τ, (y.1 τ).det ^ (-(I.chain l u a).sSharp i τ) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun τ _ => by rw [_root_.zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ (y.2 τ).ne_zero)]
    exact (mul_left_comm _ _ _).trans ((congrArg _ this).trans (mul_one _))
  have h2 : (I.chIn u a).unf B.fields.emb B.embLL i c c' ((I.chain l u a).sharp i ψ) y' =
      jetL I.J.cD (I.th u a i _ _ ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c')) (subY hab y'.1 Q) := by
    rw [h1]
    refine Eq.trans ?_ ((eval_jetLin_jetC (ι := B.fields.Tau) I.J.cD _ y'.1 (subD ℂ _ _ _ Q)).trans
      (congrArg _ (subY_eq_subD hab y'.1 Q).symm))
    have h3 := Formalism.L2.Col.polOf_fnOf (Gr B.fields.emb B.embLL (B.R.N i)) 0 (fr0 B.fields.emb B.embLL (B.R.N i)) Q
    refine (congrArg (fun P => fnOf (Gr B.fields.emb B.embLL (B.R.N (i + 1))) 0 1 ((I.chIn u a).jet i c c' P) y') h3).trans ?_
    simp [fnOf, jetMap]
    rfl
  show ((I.chIn u a).rho i c * (I.chIn u a).rho' i c') * ((∏ τ, (y'.1 τ).det ^ (I.chain l u a).sDiv i τ)⁻¹ *
    (I.chIn u a).unf B.fields.emb B.embLL i c c' ((I.chain l u a).sharp i ψ) y') =
    ((I.chIn u a).rho i c * (I.chIn u a).rho' i c') * jetL I.J.cD (I.th u a i _ _ ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c')) (subY hab y'.1 Q) *
      ∏ τ, (y'.1 τ).det ^ (-(I.chain l u a).sDiv i τ)
  rw [h2]
  simp only [_root_.zpow_neg, Finset.prod_inv_distrib]
  ring

theorem kernel_classSum : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) (hab : B.R.N i ≤ B.R.N (i + 1)) (φ : ColT I l u a i) (Fc : (I.chain l u a).cls i → PY (I.rec7 l Z).what₂.Tau (B.R.N i)), (∀ c y, φ c y = evalAt y.1 (Fc c) * ∏ τ, (y.1 τ).det ^ (-(I.chain l u a).sSharp i τ)) → ∀ c' y', (I.chain l u a).K i φ c' y' = ∑ᶠ c, ((Nat.card ((I.chain l u a).stab i c) : ℕ) : ℂ)⁻¹ * A.abelian₂ i c c' (subY hab y'.1 (Fc c)) * ∏ τ, (y'.1 τ).det ^ (-(I.chain l u a).sDiv i τ) := by
  intro B X I _ _ l Z u a Ch A _ i _ hab φ Fc hφ c' y'
  haveI : Fintype ((I.chain l u a).cls i) := (I.chain l u a).clsFin i
  unfold ColumnChain.K Formalism.ThetaLiftIndependence.kerOpM
  rw [finsum_eq_sum_of_fintype, Finset.sum_apply]
  refine Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) fun c _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, kmap_val A i hab c c' (φ c) (Fc c) (hφ c) y', ColumnChain.wt]
  ring

end GlobalTheory.AdForm.KerVal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueChainKernelEqClassSumJetsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

theorem _root_.GlobalTheory.T.trueChainKernel_eq_classSum_jets : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) (hab : B.R.N i ≤ B.R.N (i + 1)) (φ : ColT I l u a i) (Fc : (I.chain l u a).cls i → PY (I.rec7 l Z).what₂.Tau (B.R.N i)), (∀ c y, φ c y = evalAt y.1 (Fc c) * ∏ τ, (y.1 τ).det ^ (-(I.chain l u a).sSharp i τ)) → ∀ c' y', (I.chain l u a).K i φ c' y' = ∑ᶠ c, ((Nat.card ((I.chain l u a).stab i c) : ℕ) : ℂ)⁻¹ * A.abelian₂ i c c' (subY hab y'.1 (Fc c)) * ∏ τ, (y'.1 τ).det ^ (-(I.chain l u a).sDiv i τ) := by
  first | exact @GlobalTheory.AdForm.KerVal.kernel_classSum | exact GlobalTheory.AdForm.KerVal.kernel_classSum | (intros; apply GlobalTheory.AdForm.KerVal.kernel_classSum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiveChartsKernelEqClassSumJets

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.ClsKLive

theorem kval : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → JetS I l Z R.ψ R.θ s → (∀ j, j ≤ B.R.m → (g.x j).Is) → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → (clsKL R g P r k tl s J A ι).Kval := by
  intro B X I hOk hPins l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ s J hX hS hx P t r a k tl Ch₀ A ι w hP
  intro j hj hab φ hφ Fv hV hval γ a' y'
  have hj1 : j + 1 ≤ B.R.m := hj
  have hinj : Function.Injective (ι j) := hP.live.inj j
  have hram := ((hP.ram j hj.le φ).1 hφ).2
  let Fc : (I.chain l u a).cls j → PY (I.rec7 l Z).what₂.Tau (B.R.N j) := fun c =>
    if h : ∃ β, A.chOf j c = ι j β then Fv h.choose ⟨c, h.choose_spec⟩ else 0
  have hFcEq : ∀ β (c : {c // A.chOf j c = ι j β}), Fc c.1 = Fv β c := by
    intro β c
    have h : ∃ β, A.chOf j c.1 = ι j β := ⟨β, c.2⟩
    have hb : h.choose = β := hinj (h.choose_spec.symm.trans c.2)
    have gen : ∀ β' (hβ' : A.chOf j c.1 = ι j β'), β' = β → Fv β' ⟨c.1, hβ'⟩ = Fv β c := by
      rintro β' hβ' rfl; rfl
    simp only [Fc, dif_pos h]
    exact gen _ _ hb
  have hFc : ∀ c y, φ c y = evalAt y.1 (Fc c) * ∏ τ, (y.1 τ).det ^ (-(I.chain l u a).sSharp j τ) := by
    intro c y
    by_cases h : ∃ β, A.chOf j c = ι j β
    · obtain ⟨β, hβ⟩ := h
      rw [hFcEq β ⟨c, hβ⟩]
      exact hval β ⟨c, hβ⟩ ⟨y.1, y.2⟩
    · have h0 : Fc c = 0 := by simp only [Fc, dif_neg h]
      rw [h0, show φ c y = 0 by rw [hram c (fun ⟨β, hβ⟩ => h ⟨β, hβ.symm⟩)]; rfl]
      have hz : KJInf.evalAt y.1 (0 : PY (I.rec7 l Z).what₂.Tau (B.R.N j)) = 0 := map_zero (MvPolynomial.eval _)
      rw [hz, zero_mul]
  have key := GlobalTheory.T.trueChainKernel_eq_classSum_jets I hOk hPins l Z u a Ch₀ A hP.is j hj1 hab φ Fc hFc a'.1 ⟨y'.1, y'.2⟩
  have e0 : (clsKL R g P r k tl s J A ι).val (j + 1) γ ((tupOf R P u g t r k tl).K j φ) a' y' = (I.chain l u a).K j φ a'.1 ⟨y'.1, y'.2⟩ := rfl
  rw [e0, key]
  letI := (I.chain l u a).clsFin j
  letI : Fintype ((tupOf R P u g t r k tl).Ch j) := (tupOf R P u g t r k tl).fin j
  rw [finsum_eq_sum_of_fintype]
  symm
  refine (Fintype.sum_sigma (fun x : (Σ β : (tupOf R P u g t r k tl).Ch j, (clsKL R g P r k tl s J A ι).cl j β) =>
      ((stabOrd (A.U j (ι j x.1)) (A.h j (ι j x.1) x.2) : ℕ) : ℂ)⁻¹ * A.abelian₂ j x.2.1 a'.1 (subY hab y'.1 (Fv x.1 x.2)) *
        ∏ τ, (y'.1 τ).det ^ (-(I.chain l u I.mu0).sDiv j τ))).symm.trans ?_
  refine Fintype.sum_of_injective (fun x => x.2.1) ?_ _ _ ?_ ?_
  · rintro ⟨β, c, hc⟩ ⟨β', c', hc'⟩ h
    simp only at h
    subst h
    have hb : β = β' := hinj (hc.symm.trans hc')
    subst hb
    rfl
  · intro c hc
    have h : ¬ ∃ β, A.chOf j c = ι j β := fun ⟨β, hβ⟩ => hc ⟨⟨β, c, hβ⟩, rfl⟩
    have h0 : Fc c = 0 := by simp only [Fc, dif_neg h]
    rw [h0]
    erw [map_zero (subY hab _), map_zero, mul_zero, zero_mul]
  · rintro ⟨β, c⟩
    have hst := (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hOk hPins l Z u a Ch₀ A hP.is j hj.le (ι j β)).2.2 c
    simp only
    rw [hFcEq β c, hst]
    rfl

end GlobalTheory.AdForm.ClsKLive
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiveChartsKernelEqClassSumJetsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.liveCharts_kernel_eq_classSum_jets : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → JetS I l Z R.ψ R.θ s → (∀ j, j ≤ B.R.m → (g.x j).Is) → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → (clsKL R g P r k tl s J A ι).Kval := by
  first | exact @GlobalTheory.AdForm.ClsKLive.kval | exact GlobalTheory.AdForm.ClsKLive.kval | (intros; apply GlobalTheory.AdForm.ClsKLive.kval <;> assumption)
end
end
