module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvRoots
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupEigenspaceEqTopOfAeval
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeInIsotypicSup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckePolyMulCentralIdempotentMulGenericProjector

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericCharacterProjectorOnTwistFormsFix

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

theorem piKop_fix : ∀ (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool),
    ∀ y ∈ Fm0T D T S In.rho In.chi In.θ i j b, piKop D T S In i j b y = y := by
  intro D T S In i j b y hy
  classical
  haveI : Fintype (Formalism.IndefR.NX.U D.nd) := Fintype.ofFinite _
  have hu : ∀ u : Formalism.IndefR.NX.U D.nd, (actGT D T S In.rho In.chi i j b (u : G0g D.nd)) y =
      ((psiUT D T In.θ i b u : (FractionRing (T.O i))ˣ) : FractionRing (T.O i)) • y := by
    intro u
    have h := (Submodule.mem_iInf _).1 hy u
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h
    simpa using h
  unfold piKop
  rw [finsum_eq_sum_of_fintype, LinearMap.sum_apply]
  have hterm : ∀ u : Formalism.IndefR.NX.U D.nd,
      (readT D T i b (piCoef D In.θ u) • (actGT D T S In.rho In.chi i j b (u : G0g D.nd)).toLinearMap) y =
        readT D T i b ((Nat.card (Formalism.IndefR.NX.U D.nd) : ↥D.LL0)⁻¹) • y := by
    intro u
    rw [LinearMap.smul_apply, LinearEquiv.coe_toLinearMap, hu, smul_smul]
    congr 1
    unfold piCoef psiUT
    simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, ← map_mul, mul_assoc, Units.inv_mul, mul_one]
  rw [Finset.sum_congr rfl (fun u _ => hterm u), Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
  rw [← Nat.cast_smul_eq_nsmul (FractionRing (T.O i)), smul_smul]
  have hne : (Nat.card (Formalism.IndefR.NX.U D.nd) : ↥D.LL0) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have : ((Nat.card (Formalism.IndefR.NX.U D.nd) : ℕ) : FractionRing (T.O i)) *
      readT D T i b ((Nat.card (Formalism.IndefR.NX.U D.nd) : ↥D.LL0)⁻¹) = 1 := by
    rw [← map_natCast (readT D T i b), ← map_mul, mul_inv_cancel₀ hne, map_one]
  rw [this, one_smul]

end GlobalTheory.HeightCounting.FormsStep
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericCharacterProjectorOnTwistFormsFixStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.genericCharacterProjectorOnTwistForms_fix : ∀ (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool),
    ∀ y ∈ Fm0T D T S In.rho In.chi In.θ i j b, piKop D T S In i j b y = y := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.piKop_fix | exact GlobalTheory.HeightCounting.FormsStep.piKop_fix | (intros; apply GlobalTheory.HeightCounting.FormsStep.piKop_fix <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeIdempotentProjectorVanishingBaseChangeTwist

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

theorem transfer_aeval (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (i : T.Tw) (j : ℕ) (b : Bool)
    (Φ : S.WL j →+ FmT D T S i j b)
    (hc : ∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x)
    (F : Module.End D.what₂.LL (S.WL j)) (G : Module.End (FractionRing (T.O i)) (FmT D T S i j b))
    (hFG : ∀ x, Φ (F x) = G (Φ x)) (p : Polynomial ↥D.LL0) (x : S.WL j) :
    Φ (aeval F (p.map (algebraMap ↥D.LL0 D.what₂.LL)) x) = aeval G (p.map (readT D T i b)) (Φ x) := by
  have hpow : ∀ (n : ℕ) (y : S.WL j), Φ ((F ^ n) y) = (G ^ n) (Φ y) := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih => intro y; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hFG]
  induction p using Polynomial.induction_on' generalizing x with
  | add p q hp hq => rw [Polynomial.map_add (f := _), Polynomial.map_add (f := _), map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply,
      map_add, hp, hq]
  | monomial n a =>
    rw [Polynomial.map_monomial, Polynomial.map_monomial, aeval_monomial, aeval_monomial, Module.End.mul_apply,
      Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, IntermediateField.algebraMap_apply,
      hc, hpow]

theorem transfer_piLop (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool)
    (Φ : S.WL j →+ FmT D T S i j b)
    (hc : ∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x)
    (ha : ∀ (g : G0g D.nd) (x : S.WL j), Φ (actL D S j g x) = actGT D T S In.rho In.chi i j b g (Φ x))
    (x : S.WL j) : Φ (piLop D S In.θ j x) = piKop D T S In i j b (Φ x) := by
  haveI : Fintype (Formalism.IndefR.NX.U D.nd) := Fintype.ofFinite _
  unfold piLop piKop

  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, hc, ha, LinearEquiv.coe_coe]

theorem phiKop_eGT_piKop_eq_zero : ∀ (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ)
    (b : Bool) (k : ℕ) (P : PlE D.host),
    1 ≤ j → j ≤ D.R.m → phiLop D S In j k P * eLop D S j * piLop D S In.θ j = 0 →
    phiKop D T S In i j b k P * eGT D T S In.rho In.chi i j b * piKop D T S In i j b = 0 := by
  intro D T S In i j b k P h1 h2 h0
  obtain ⟨Φ, hc, hf, hw⟩ := descend_exists D T S In i j b h1 h2
  have ha := descend_actL D T S In i j b h1 h2 Φ hc hf
  have he : ∀ x, Φ (eLop D S j x) = eGT D T S In.rho In.chi i j b (Φ x) := descend_eSum D T S In i j b Φ hc ha
  have hpi := transfer_piLop D T S In i j b Φ hc ha
  have hr : ∀ w : ↥(WKr D S j), (hLr D S In j k P w : S.WL j) = In.hL j k P w := by
    intro w
    unfold hLr
    split_ifs with h
    · rfl
    · exact absurd ⟨h1, h2⟩ h
  have hh : ∀ x, Φ (In.hL j k P x) = hLT D T S In i j b k P (Φ x) := fun x => hf _ _ hr x
  have hphi : ∀ x, Φ (phiLop D S In j k P x) = phiKop D T S In i j b k P (Φ x) :=
    transfer_aeval D T S i j b Φ hc _ _ hh (evPol D S In j k P)
  have key : ∀ w : ↥(WKr D S j),
      (phiKop D T S In i j b k P * eGT D T S In.rho In.chi i j b * piKop D T S In i j b)
        ((1 : KT D T i b) ⊗ₜ[S.Ks] w : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) = 0 := by
    intro w
    rw [← hw, Module.End.mul_apply, Module.End.mul_apply, ← hpi, ← he, ← hphi]
    have h3 := LinearMap.congr_fun h0 (w : S.WL j)
    rw [Module.End.mul_apply, Module.End.mul_apply] at h3
    rw [h3, LinearMap.zero_apply, map_zero]
  set f := phiKop D T S In i j b k P * eGT D T S In.rho In.chi i j b * piKop D T S In i j b with hfdef
  refine LinearMap.ext fun y => ?_
  rw [LinearMap.zero_apply]
  change KT D T i b ⊗[S.Ks] ↥(WKr D S j) at y
  induction y using TensorProduct.induction_on with
  | zero => exact f.map_zero
  | tmul c w =>
    have hcw : (c ⊗ₜ[S.Ks] w : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) =
        (c : FractionRing (T.O i)) • ((1 : KT D T i b) ⊗ₜ[S.Ks] w : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hcw]
    exact (f.map_smul (c : FractionRing (T.O i))
      (show FmT D T S i j b from ((1 : KT D T i b) ⊗ₜ[S.Ks] w : KT D T i b ⊗[S.Ks] ↥(WKr D S j)))).trans
      (by rw [key]; exact smul_zero _)
  | add y z hy hz =>
    exact (f.map_add (show FmT D T S i j b from y) (show FmT D T S i j b from z)).trans (by rw [hy, hz, add_zero])

end GlobalTheory.HeightCounting.FormsStep
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeIdempotentProjectorVanishingBaseChangeTwistStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.heckeIdempotentProjector_vanishing_baseChange_twistSide : ∀ (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host),
    1 ≤ j → j ≤ D.R.m → phiLop D S In j k P * eLop D S j * piLop D S In.θ j = 0 →
    phiKop D T S In i j b k P * eGT D T S In.rho In.chi i j b * piKop D T S In i j b = 0 := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.phiKop_eGT_piKop_eq_zero | exact GlobalTheory.HeightCounting.FormsStep.phiKop_eGT_piKop_eq_zero | (intros; apply GlobalTheory.HeightCounting.FormsStep.phiKop_eGT_piKop_eq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckePolyMulCentralIdempotentMulGenericProjectorStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.heckePoly_mul_centralIdempotent_mul_genericProjector : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (j k : ℕ) (P : PlE D.host), 1 ≤ j → j ≤ D.R.m → 1 ≤ k → k ≤ D.R.r →
    IsSplitPl D.host P → P ∉ In.Sb → phiLop D S In j k P * eLop D S j * piLop D S In.θ j = 0 := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.phiLop_eLop_piLop | exact GlobalTheory.HeightCounting.FormsStep.phiLop_eLop_piLop | (intros; apply GlobalTheory.HeightCounting.FormsStep.phiLop_eLop_piLop <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.V0TLeISupEigenspace

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
namespace GlobalTheory.HeightCounting.FormsStep
theorem v0t_le_supr_eigenspace : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
    In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    ∀ (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host), HkCond D T i j k P →
      V0T D T S In.rho In.chi In.θ i j b ≤
        ⨆ σ ∈ {σ : D.what₂.FT | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ},
          Module.End.eigenspace (hkT D T S In i j b k P)
            (algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i) ^ k * readT D T i b (In.eig j σ k P)) := by
  intro D cf jE A S In b0 b1 Sx T Sp hSb _ i j b k P hk
  obtain ⟨hj1, hj2, hk1, hk2, hsp, hP0⟩ := hk
  have hPSb : P ∉ In.Sb := by
    intro h
    apply hP0
    have h1 : P ∈ (T.S0 i : Set (PlE D.host)) := by
      rw [Sp.ringSpec_excludedPlaces_eq i]
      exact Or.inr (hSb h)
    exact h1
  have hZ := GlobalTheory.T.heckeIdempotentProjector_vanishing_baseChange_twistSide D T S In i j b k P hj1 hj2 (GlobalTheory.T.heckePoly_mul_centralIdempotent_mul_genericProjector D S In j k P hj1 hj2 hk1 hk2 hsp hPSb)
  have hker : V0T D T S In.rho In.chi In.θ i j b ≤ LinearMap.ker (phiKop D T S In i j b k P) := by
    rintro x ⟨y, hy, rfl⟩
    rw [LinearMap.mem_ker]
    have := LinearMap.congr_fun hZ y
    rw [Module.End.mul_apply, Module.End.mul_apply, GlobalTheory.T.genericCharacterProjectorOnTwistForms_fix D T S In i j b y hy] at this
    exact this
  refine hker.trans ?_
  classical
  have hinj : Function.Injective (readT D T i b) := (readT D T i b).injective
  have hpol : (evPol D S In j k P).map (readT D T i b) =
      ∏ r ∈ (evRoots D S In j k P).image (readT D T i b), (X - C r) := by
    rw [evPol, Polynomial.map_prod, Finset.prod_image (fun x _ y _ h => hinj h)]
    simp
  rw [phiKop, hpol, GlobalTheory.JointDiag.ker_prod]
  refine iSup₂_le fun r hr => ?_
  obtain ⟨r0, hr0, rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hr0
  have hσ' : σ ∈ {σ : D.what₂.FT | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ} := (Finset.mem_filter.mp hσ).2
  refine le_trans ?_ (le_iSup₂_of_le σ hσ' le_rfl)
  intro x hx
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  rw [hkT_eq, LinearMap.smul_apply, hx, smul_smul]
end GlobalTheory.HeightCounting.FormsStep
end
end
end
