module

public import ReciprocityTheory.DualLattices.TowerZeroSurjective
public import ReciprocityTheory.DualLattices.LinPairStatement
public import ReciprocityTheory.DualLattices.SubMemOfCompat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DualTowerMapExists
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EvBasicNEvalSubCoeffMem
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsEndDifferentialRingHom
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFormalChart
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLiftOfNil
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsSeriesOfNaturalOnNilpotent
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsTateMatricesLink
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FinEtaleFormallyUnramified
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FinOfLocalAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FinRepExistsIsPullbackSpec
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FiniteAlgebraSplitLocal
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GroupLawPowerSeries
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ModPToValuationResidueFieldSurjective
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NilpotentCoordinates
public import ReciprocityTheory.DualLattices.FormalChartAtZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TateBasisGram
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TateBasisMatrix
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TeichmullerQuot
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicEndApply

section

@[expose] public section

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PadicOrderAction

def padicEnd (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M] (hM : ∀ x : M, p • x = 0) :
    ℤ_[p] →+* AddMonoid.End M where
  toFun c := nsmulAddMonoidHom (PadicInt.toZMod c).val
  map_one' := by
    ext x
    change (PadicInt.toZMod (1 : ℤ_[p])).val • x = x
    rw [map_one, ZMod.val_one, one_nsmul]
  map_mul' a b := by
    ext x
    change (PadicInt.toZMod (a * b)).val • x = (PadicInt.toZMod a).val • (PadicInt.toZMod b).val • x
    rw [map_mul, ZMod.val_mul, ← nsmul_eq_mod_nsmul _ (hM x), mul_nsmul']
  map_zero' := by
    ext x
    change (PadicInt.toZMod (0 : ℤ_[p])).val • x = 0
    rw [map_zero, ZMod.val_zero, zero_nsmul]
  map_add' a b := by
    ext x
    change (PadicInt.toZMod (a + b)).val • x = (PadicInt.toZMod a).val • x + (PadicInt.toZMod b).val • x
    rw [map_add (f := _), ZMod.val_add, ← nsmul_eq_mod_nsmul _ (hM x), add_nsmul]

def liftInt {A B C : Type} [CommRing A] [CommRing B] [Ring C] (φ : A →+* C) (ψ : B →+* C)
    (h : ∀ a b, φ a * ψ b = ψ b * φ a) : A ⊗[ℤ] B →+* C :=
  (Algebra.TensorProduct.lift φ.toIntAlgHom ψ.toIntAlgHom h).toRingHom

lemma liftInt_tmul {A B C : Type} [CommRing A] [CommRing B] [Ring C] (φ : A →+* C) (ψ : B →+* C)
    (h : ∀ a b, φ a * ψ b = ψ b * φ a) (a : A) (b : B) : liftInt φ ψ h (a ⊗ₜ[ℤ] b) = φ a * ψ b :=
  Algebra.TensorProduct.lift_tmul φ.toIntAlgHom ψ.toIntAlgHom h a b

variable {R₀ : Type} [CommRing R₀]

lemma pTorsion_nsmul_eq_zero (B : BX R₀) (p : ℕ) (S : LAlg R₀) (x : torP B p S) : p • x = 0 :=
  Subtype.ext ((mem_torP B p _).1 x.2)

def resEnd {B : BX R₀} {O : LAlg R₀} (e : OEnd B O) (p : ℕ) {S : LAlg R₀} (s : LHom O S) :
    AddMonoid.End (torP B p S) :=
  ((e.f s).comp (torP B p S).subtype).codRestrict (torP B p S) fun x => by
    rw [mem_torP, ← map_nsmul, pTorsion_nsmul_eq_zero, map_zero]

def ordEnd {B : BX R₀} {O : LAlg R₀} {O₀ : Type} [CommRing O₀] (f : O₀ → OEnd B O) (p : ℕ)
    {S : LAlg R₀} (s : LHom O S)
    (h : ∀ x : B.G S, (f 1).f s x = x ∧ ∀ a b, (f (a + b)).f s x = (f a).f s x + (f b).f s x ∧
      (f (a * b)).f s x = (f a).f s ((f b).f s x)) : O₀ →+* AddMonoid.End (torP B p S) :=
  RingHom.mk' (α := O₀) (β := AddMonoid.End (torP B p S))
    { toFun := fun a => resEnd (f a) p s
      map_one' := AddMonoidHom.ext fun x => Subtype.ext (h x).1
      map_mul' := fun a b => AddMonoidHom.ext fun x => Subtype.ext ((h x).2 a b).2 }
    fun a b => AddMonoidHom.ext fun x => Subtype.ext ((h x).2 a b).1

def complEnd {B : BX R₀} {O : LAlg R₀} {O₀ : Type} [CommRing O₀] (f : O₀ → OEnd B O) (p : ℕ)
    [Fact p.Prime] {S : LAlg R₀} (s : LHom O S)
    (h : ∀ x : B.G S, (f 1).f s x = x ∧ ∀ a b, (f (a + b)).f s x = (f a).f s x + (f b).f s x ∧
      (f (a * b)).f s x = (f a).f s ((f b).f s x)) :
    ℤ_[p] ⊗[ℤ] O₀ →+* AddMonoid.End (torP B p S) :=
  liftInt (padicEnd p _ (pTorsion_nsmul_eq_zero B p S)) (ordEnd f p s h) fun c a =>
    AddMonoidHom.ext fun x => (map_nsmul (ordEnd f p s h a) (PadicInt.toZMod c).val x).symm

lemma complEnd_tmul {B : BX R₀} {O : LAlg R₀} {O₀ : Type} [CommRing O₀] (f : O₀ → OEnd B O) (p : ℕ)
    [Fact p.Prime] {S : LAlg R₀} (s : LHom O S)
    (h : ∀ x : B.G S, (f 1).f s x = x ∧ ∀ a b, (f (a + b)).f s x = (f a).f s x + (f b).f s x ∧
      (f (a * b)).f s x = (f a).f s ((f b).f s x)) (c : ℤ_[p]) (a : O₀) (x : torP B p S) :
    (complEnd f p s h (c ⊗ₜ[ℤ] a) x : B.G S) = (PadicInt.toZMod c).val • (f a).f s x := by
  have e : complEnd f p s h (c ⊗ₜ[ℤ] a) =
      padicEnd p _ (pTorsion_nsmul_eq_zero B p S) c * ordEnd f p s h a := liftInt_tmul _ _ _ c a
  rw [e]
  rfl

def complMat {g : ℕ} {O : Type} [CommRing O] {O₀ : Type} [CommRing O₀] (p : ℕ) [Fact p.Prime]
    [Algebra ℤ_[p] O] (dL : O₀ →+* Matrix (Fin g) (Fin g) O) :
    ℤ_[p] ⊗[ℤ] O₀ →+* Matrix (Fin g) (Fin g) O :=
  liftInt (algebraMap ℤ_[p] (Matrix (Fin g) (Fin g) O)) dL fun c a => Algebra.commutes c (dL a)

lemma complMat_tmul {g : ℕ} {O : Type} [CommRing O] {O₀ : Type} [CommRing O₀] (p : ℕ)
    [Fact p.Prime] [Algebra ℤ_[p] O] (dL : O₀ →+* Matrix (Fin g) (Fin g) O) (c : ℤ_[p]) (a : O₀) :
    complMat p dL (c ⊗ₜ[ℤ] a) = algebraMap ℤ_[p] O c • dL a := by
  rw [complMat, liftInt_tmul, algebraMap_smul]
  exact (Algebra.smul_def c (dL a)).symm

def kerMul {R S : LAlg R₀} (π : LHom R S) (r : (R : Type)) (i : π.ker) : π.ker :=
  ⟨r * i, Ideal.mul_mem_left (RingHom.ker π.1) r i.2⟩

lemma padic_mul_eq {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (t : ℤ_[p] →+* R) (c : ℤ_[p])
    (i : R) (hi : p • i = 0) : t c * i = (PadicInt.toZMod c).val • i := by
  have h : c - ((PadicInt.toZMod c).val : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h
  obtain ⟨d, hd⟩ := h
  have hc : c = d * p + ((PadicInt.toZMod c).val : ℤ_[p]) := by rw [hd]; ring
  rw [nsmul_eq_mul] at hi ⊢
  conv_lhs => rw [hc]
  rw [map_add (f := _), map_mul, map_natCast, map_natCast, add_mul, _root_.mul_assoc, hi, mul_zero, zero_add]

theorem main :
  (∀ {R₀ : Type} [CommRing R₀] {g : ℕ} (B : BX R₀) (O : LAlg R₀) (gb : Module.Basis (Fin g) R₀ B.gg) (O₀ : Type) [CommRing O₀] (f : O₀ → OEnd B O) (p : ℕ) [Fact p.Prime] [Algebra ℤ_[p] (O : Type)] (dL : O₀ →+* Matrix (Fin g) (Fin g) (O : Type)),
    Function.Surjective (algebraMap R₀ (O : Type)) → (∀ {R : LAlg R₀} (s : LHom O R) (x : B.G R), (f 1).f s x = x ∧ ∀ a b, (f (a + b)).f s x = (f a).f s x + (f b).f s x ∧
      (f (a * b)).f s x = (f a).f s ((f b).f s x)) →
    (∀ a {R S : LAlg R₀} (s : LHom O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker) (m : Fin g → π.ker),
      (∀ k, (m k : (R : Type)) = s.1 (dL a k l) * i) →
      (f a).f s (B.tg π hπ (gb l ⊗ₜ[R₀] i)) = B.tg π hπ (∑ k, gb k ⊗ₜ[R₀] m k)) →
    ∃ (A : OAct B O p (ℤ_[p] ⊗[ℤ] O₀)) (ρL : ℤ_[p] ⊗[ℤ] O₀ →+* Matrix (Fin g) (Fin g) (O : Type)),
      (∀ c a, ρL (c ⊗ₜ[ℤ] a) = algebraMap ℤ_[p] (O : Type) c • dL a) ∧
      (∀ a k l, ρL a k l = algebraMap R₀ (O : Type) (gb.repr (A.actL a (gb l)) k)) ∧
      ∀ c a (S : LAlg R₀) (s : LHom O S) (x : torP B p S), (A.act (c ⊗ₜ[ℤ] a) S s x : B.G S) = (PadicInt.toZMod c).val • (f a).f s x) := by
  intro R₀ _ g B O gb O₀ _ f p _ _ dL hs hf htg
  choose pre hpre using hs
  let L : ℤ_[p] ⊗[ℤ] O₀ → B.gg →ₗ[R₀] B.gg := fun a =>
    gb.constr R₀ fun l => ∑ k, pre (complMat p dL a k l) • gb k
  have hL : ∀ a l, L a (gb l) = ∑ k, pre (complMat p dL a k l) • gb k := fun a l =>
    gb.constr_basis R₀ _ l
  have key : ∀ a {R S : LAlg R₀} (s : LHom O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g)
      (i : π.ker) (hi : p • i = 0),
      (complEnd f p s (hf s) a ⟨B.tg π hπ (gb l ⊗ₜ i), tg_torP B p π hπ _ i hi⟩ : B.G R) =
        B.tg π hπ (∑ k, gb k ⊗ₜ[R₀] kerMul π (s.1 (complMat p dL a k l)) i) := by
    intro a R S s π hπ l i hi
    induction a using TensorProduct.induction_on with
    | zero =>
      have : ∀ k, kerMul π (s.1 (complMat p dL 0 k l)) i = 0 := fun k =>
        Subtype.ext (by simp [kerMul])
      simp only [this]
      simp only [TensorProduct.tmul_zero, Finset.sum_const_zero, map_zero]
      rfl
    | tmul c a =>
      rw [complEnd_tmul]
      change _ • (f a).f s (B.tg π hπ (gb l ⊗ₜ i)) = _
      rw [htg a s π hπ l i (fun k => kerMul π (s.1 (dL a k l)) i) (fun k => rfl), ← map_nsmul,
        Finset.smul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      refine (map_nsmul (TensorProduct.mk R₀ B.gg π.ker (gb k)) _ _).symm.trans ?_
      change gb k ⊗ₜ[R₀] _ = _
      congr 1
      apply Subtype.ext
      have hi' : p • (i : (R : Type)) = 0 := congrArg Subtype.val hi
      have h2 := padic_mul_eq (s.1.toRingHom.comp (algebraMap ℤ_[p] (O : Type))) c
        (s.1 (dL a k l) * i) (by rw [← mul_smul_comm, hi', mul_zero])
      change (PadicInt.toZMod c).val • (s.1 (dL a k l) * i) = s.1 (complMat p dL (c ⊗ₜ a) k l) * i
      rw [← h2, complMat_tmul, Matrix.smul_apply, smul_eq_mul, map_mul, _root_.mul_assoc]
      rfl
    | add a b ha hb =>
      have : ∀ k, kerMul π (s.1 (complMat p dL (a + b) k l)) i =
          kerMul π (s.1 (complMat p dL a k l)) i + kerMul π (s.1 (complMat p dL b k l)) i :=
        fun k => Subtype.ext (by simp [kerMul, add_mul])
      simp only [this, TensorProduct.tmul_add, Finset.sum_add_distrib]
      rw [map_add (B.tg π hπ), ← ha, ← hb, map_add (f := _)]
      rfl
  have key2 : ∀ a {R S : LAlg R₀} (s : LHom O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g)
      (i : π.ker) (hi : p • i = 0),
      (complEnd f p s (hf s) a ⟨B.tg π hπ (gb l ⊗ₜ i), tg_torP B p π hπ _ i hi⟩ : B.G R) =
        B.tg π hπ (L a (gb l) ⊗ₜ[R₀] i) := by
    intro a R S s π hπ l i hi
    rw [key a s π hπ l i hi, hL, TensorProduct.sum_tmul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [TensorProduct.smul_tmul]
    congr 1
    apply Subtype.ext
    change s.1 (complMat p dL a k l) * i = pre (complMat p dL a k l) • (i : (R : Type))
    rw [Algebra.smul_def, ← s.1.commutes, hpre]
  refine ⟨{ act := fun a S s => complEnd f p s (hf s) a
            act_one := fun S s x => by rw [map_one]; rfl
            act_mul := fun a b S s x => by rw [map_mul]; rfl
            act_add := fun a b S s x => by rw [map_add (f := _)]; rfl
            act_nat := ?_
            actL := L
            act_tg := ?_ }, complMat p dL, complMat_tmul p dL, ?_,
            fun c a S s x => complEnd_tmul f p s (hf s) c a x⟩
  · intro a S S' s s' φ hφ x
    subst hφ
    change B.map φ (complEnd f p s (hf s) a x : B.G S) =
      (complEnd f p (φ.comp s) (hf _) a ⟨B.map φ x, map_torP B p φ x⟩ : B.G S')
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul c a => rw [complEnd_tmul, complEnd_tmul, map_nsmul, (f a).nat]
    | add a b ha hb =>
      rw [map_add (f := _), map_add (f := _)]
      change B.map φ ((complEnd f p s (hf s) a x : B.G S) + (complEnd f p s (hf s) b x : B.G S)) = _
      rw [map_add (f := _), ha, hb]
      rfl
  · intro a R S s π hπ w i hi
    have hr : ∀ l, p • (gb.repr w l • i) = 0 := fun l => by rw [smul_comm, hi, smul_zero]
    have h1 : (⟨B.tg π hπ (w ⊗ₜ i), tg_torP B p π hπ w i hi⟩ : torP B p R) =
        ∑ l, ⟨B.tg π hπ (gb l ⊗ₜ (gb.repr w l • i)), tg_torP B p π hπ _ _ (hr l)⟩ := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      change B.tg π hπ (w ⊗ₜ i) = ∑ l, B.tg π hπ (gb l ⊗ₜ (gb.repr w l • i))

      rw [← map_sum]
      congr 1
      conv_lhs => rw [← gb.sum_repr w, TensorProduct.sum_tmul]
      exact Finset.sum_congr rfl fun l _ => TensorProduct.smul_tmul _ _ _
    change (complEnd f p s (hf s) a ⟨B.tg π hπ (w ⊗ₜ i), tg_torP B p π hπ w i hi⟩ : B.G R) = _

    rw [h1, map_sum, AddSubmonoidClass.coe_finsetSum,
    Finset.sum_congr rfl fun l _ => key2 a s π hπ l _ (hr l), ← map_sum]
    congr 1

    conv_rhs => rw [← gb.sum_repr w, map_sum, TensorProduct.sum_tmul]
    exact Finset.sum_congr rfl fun l _ => by rw [map_smul, TensorProduct.smul_tmul]
  · intro a k l
    change complMat p dL a k l = algebraMap R₀ (O : Type) (gb.repr (L a (gb l)) k)
    rw [hL, gb.repr_sum_self, hpre]

end GlobalTheory.PadicOrderAction
end
end
end

-- Source module: ReciprocityTheory.DualLattices.SurjectiveAinfTowerZero

section

@[expose] public section

noncomputable section

open WittVector Ideal

namespace ReciprocityTheory.PGsh.Be2

open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Ainf

variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
  (hv : v.Integers O) (ε : PreTilt O p)
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)

theorem surjective_ainfTower_zero : Function.Surjective ((ainfTowerL p O hv ε hε).q 0).1 :=
  fun y => Ideal.Quotient.mk_surjective (I := Ideal.span {(p : O) ^ (0 + 1)}) y

theorem ker_ainfTower_zero : RingHom.ker ((ainfTowerL p O hv ε hε).q 0).1 =
    Ideal.span {((p : ℕ) : ((ainfTowerL p O hv ε hε).O : Type))} := by
  ext a
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  have hq : ((ainfTowerL p O hv ε hε).q 0).1 a =
      Ideal.Quotient.mk (Ideal.span {(p : O) ^ (0 + 1)}) a := rfl
  rw [hq]
  exact (Ideal.Quotient.eq_zero_iff_dvd _ _).trans (by rw [pow_one]; rfl)

theorem ainf_zeta0 (h2 : p = 2) :
    (((ainfTowerL p O hv ε hε).ζ 0 : ((ainfTowerL p O hv ε hε).O : Type)ˣ) :
      ((ainfTowerL p O hv ε hε).O : Type)) = -1 := by
  have hz : (((ainfTowerL p O hv ε hε).ζ 0 : ((ainfTowerL p O hv ε hε).O : Type)ˣ) :
      ((ainfTowerL p O hv ε hε).O : Type)) = ((frobeniusEquiv (PreTilt O p) p).symm ε).untilt := by
    show zetaV p O ε 0 = _
    simp [zetaV, root, fontaineTheta_teichmuller]
  rw [hz]
  clear hz
  haveI : NoZeroDivisors O :=
    hv.hom_inj.noZeroDivisors _ (map_zero _) (map_mul _)
  set z := ((frobeniusEquiv (PreTilt O p) p).symm ε).untilt with hzdef
  clear_value z
  rw [h2] at hε
  exact hε.eq_neg_one_of_two_right

end ReciprocityTheory.PGsh.Be2
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsCompatibleBasis

section

@[expose] public section

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PeriodDatum

theorem exists_basis_of_card (p : ℕ) [hp : Fact p.Prime] (g : ℕ) (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] (hcV : Nat.card V = p ^ (2 * g)) :
    ∃ f : Ix g → V, ∀ x : V, ∃! t : Ix g → ZMod p, x = ∑ j, (t j).val • f j := by
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hcV]; exact pow_ne_zero _ hp.out.ne_zero)
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hrk : Module.finrank (ZMod p) V = Fintype.card (Ix g) := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rw [hcV, Nat.card_zmod] at h
    have h2 := Nat.pow_right_injective hp.out.two_le h
    rw [← h2, Fintype.card_sum, Fintype.card_fin, two_mul]
  let b : Module.Basis (Ix g) (ZMod p) V :=
    (Module.finBasisOfFinrankEq (ZMod p) V hrk).reindex (Fintype.equivFin (Ix g)).symm
  have hsm : ∀ (t : ZMod p) (y : V), t.val • y = t • y := fun t y => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
  refine ⟨b, fun x => ⟨b.equivFun x, ?_, fun t ht => ?_⟩⟩
  · simp only [hsm]
    rw [← b.equivFun_symm_apply, LinearEquiv.symm_apply_apply]
  · simp only [hsm] at ht
    rw [← b.equivFun_symm_apply] at ht
    rw [ht, LinearEquiv.apply_symm_apply]

theorem exists_compatible_basis (p : ℕ) [hp : Fact p.Prime] (g : ℕ) (Γ : Type) [AddCommGroup Γ]
    (hdiv : ∀ x : Γ, ∃ y, p • y = x) (hcard : Nat.card {x : Γ // p • x = 0} = p ^ (2 * g)) :
    ∃ τ : Ix g → ℕ → Γ, (∀ i n, (p ^ (n + 1)) • τ i n = 0) ∧ (∀ i n, τ i n = p • τ i (n + 1)) ∧
      ∀ x : Γ, p • x = 0 → ∃! t : Ix g → ZMod p, x = ∑ j, (t j).val • τ j 0 := by
  obtain ⟨V, hV⟩ : ∃ V : AddSubgroup Γ, ∀ x : Γ, x ∈ V ↔ p • x = 0 :=
    ⟨(nsmulAddMonoidHom p : Γ →+ Γ).ker, fun x => Iff.rfl⟩
  have hcV : Nat.card V = p ^ (2 * g) :=
    (Nat.card_congr (Equiv.subtypeEquivRight hV)).trans hcard
  obtain ⟨b, hb⟩ := @exists_basis_of_card p _ g V _
    (AddCommGroup.zmodModule (fun x => Subtype.ext ((hV _).1 x.2))) hcV
  choose d hd using hdiv
  let τ : Ix g → ℕ → Γ := fun i n => d^[n] (b i : Γ)
  have hτp : ∀ i n, τ i n = p • τ i (n + 1) := fun i n => by
    simp only [τ, Function.iterate_succ_apply', hd]
  have hsum : ∀ t : Ix g → ZMod p, ((∑ j, (t j).val • b j : V) : Γ) = ∑ j, (t j).val • τ j 0 :=
    fun t => by
      rw [AddSubmonoidClass.coe_finsetSum]
      rfl
  refine ⟨τ, fun i n => ?_, hτp, fun x hx => ?_⟩
  · induction n with
    | zero => rw [zero_add, pow_one]; exact (hV _).1 (b i).2
    | succ n ih => rw [pow_succ, mul_smul, ← hτp i n, ih]
  · obtain ⟨t, ht, hu⟩ := hb ⟨x, (hV x).2 hx⟩
    refine ⟨t, ?_, fun t' ht' => hu t' (Subtype.ext ?_)⟩
    · exact (congrArg Subtype.val ht).trans (hsum t)
    · exact ht'.trans (hsum t').symm

theorem main :
  (∀ (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) (g : ℕ)
    (G : Over (Spec (CommRingCat.of (Ainf.R0 p O ε)))) [GrpObj G] [IsCommMonObj G] (B : BX (Ainf.R0 p O ε))
    (e : ∀ R : LAlg (Ainf.R0 p O ε), B.G R → (sp (R₀ := (Ainf.R0 p O ε)) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) →
    (∀ {R S : LAlg (Ainf.R0 p O ε)} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) →
    SmoothOfRelativeDimension g G.hom → IsFinite ((𝟙 G) ^ p : G ⟶ G).left → Flat ((𝟙 G) ^ p : G ⟶ G).left →
    (∀ x : B.G (Ainf.ainfTowerL p O hv ε hε).O, ∃ y, p • y = x) → Nat.card {x : B.G (Ainf.ainfTowerL p O hv ε hε).O // p • x = 0} = p ^ (2 * g) →
    (∀ x : B.G (Ainf.ainfTowerL p O hv ε hε).O, p • x = 0 → (∀ y : B.G (Ainf.ainfTowerL p O hv ε hε).O, p • y = 0 → B.IsPairing p x y 1) → x = 0) →
    ∀ [Algebra ℤ_[p] ((Ainf.ainfTowerL p O hv ε hε).O : Type)] (O₀ : Type) [CommRing O₀] (cj : O₀ ≃ₐ[ℤ] O₀) (Ad : O₀ → OAdj B (Ainf.ainfTowerL p O hv ε hε).O),
    (∀ a, (Ad a).ab = (Ad (cj a)).a) → (∀ a, cj (cj a) = a) →
    (∀ {R : LAlg (Ainf.R0 p O ε)} (s : LHom (Ainf.ainfTowerL p O hv ε hε).O R) (x : B.G R), (Ad 1).a.f s x = x ∧ ∀ a b, (Ad (a + b)).a.f s x = (Ad a).a.f s x + (Ad b).a.f s x ∧
      (Ad (a * b)).a.f s x = (Ad a).a.f s ((Ad b).a.f s x)) →
    ∃ (Dt : DualTower (Ainf.ainfTowerL p O hv ε hε)) (D : Dat p g B (Ainf.ainfTowerL p O hv ε hε) Dt (ℤ_[p] ⊗[ℤ] O₀) (Algebra.TensorProduct.congr (AlgEquiv.refl : ℤ_[p] ≃ₐ[ℤ_[p]] ℤ_[p]) cj) (Ainf.ainfTowerL p O hv ε hε).c),
      D.H.P = 0 ∧ D.H.PL = 0 ∧
      (∀ a {R S : LAlg (Ainf.R0 p O ε)} (s : LHom (Ainf.ainfTowerL p O hv ε hε).O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker) (m : Fin g → π.ker),
      (∀ k, (m k : (R : Type)) = s.1 (D.H.ρL (1 ⊗ₜ[ℤ] a) k l) * i) →
      (Ad a).a.f s (B.tg π hπ (D.ch.gb l ⊗ₜ[(Ainf.R0 p O ε)] i)) = B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[(Ainf.R0 p O ε)] m k)) ∧
      ∀ a j n, (Ad a).a.f (LHom.id (Ainf.ainfTowerL p O hv ε hε).O) (D.L.τ j n) = ∑ k, (PadicInt.toZModPow (n + 1) (D.H.ρ (1 ⊗ₜ[ℤ] a) k j)).val • D.L.τ k n) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε g G _ _ B e hbij hadd hnat hsm hfin hflat hdiv hcard hperf
    _ O₀ _ cj Ad hab hcj hAd
  haveI : IsLocalRing (Ainf.R0 p O ε) := WdAinf.ainf_thetaQuotRing_isLocalRing p O hv ε hε
  haveI : IsDomain ((Ainf.ainfTowerL p O hv ε hε).O : Type) := Ainf.ainfTower_isDomain p O hv ε hε
  have hsm' : Smooth G.hom := SmoothOfRelativeDimension.smooth g G.hom
  obtain ⟨K, wd, hnil, hK, hKl⟩ :=
    GlobalTheory.wData_ainfTower_exists GlobalTheory.WittQuot.teichmuller_quot p O hv ε hε
  obtain ⟨ch⟩ := GlobalTheory.FormalChartOf.exists_formalChart GlobalTheory.NilCoord.nilpotent_coordinates
    (GlobalTheory.ChLaw.groupLaw_powerSeries GlobalTheory.nEval_basic
      (GlobalTheory.exists_series_of_natural_on_nilpotent GlobalTheory.nEval_basic))
    G g B e hbij hadd hnat hsm K hK hKl
  have sm := GlobalTheory.SmoothNilLift.main G B e hbij hadd hnat hsm' K wd.W wd.ρW hnil
  obtain ⟨fin⟩ := @GlobalTheory.FinOf.main GlobalTheory.finRep_kernel_mul_finite_free GlobalTheory.finite_algebra_split_local
    GlobalTheory.finEtale_main _ _ G _ _ (Ainf.ainfTowerL p O hv ε hε).O p B e hbij hadd hnat hfin hflat hsm'
    C _ _ _ v (inferInstanceAs (Algebra O C)) hv (Fact.out : p.Prime).ne_zero
  obtain ⟨Dt⟩ := GlobalTheory.exists_dualTower (Ainf.ainfTowerL p O hv ε hε)
  obtain ⟨τ, hτ, hτp, hbas⟩ := exists_compatible_basis p g _ hdiv hcard
  obtain ⟨dL, hdL⟩ := GlobalTheory.exists_endDifferential_ringHom B _ ch.gb O₀ (fun a => (Ad a).a) hAd
  obtain ⟨A, H, L, hP, hPL, hL, hρL, hρ⟩ := GlobalTheory.exists_tateMatrices_link GlobalTheory.tate_basis_matrix
    GlobalTheory.tateBasis_gram GlobalTheory.PadicOrderAction.main B (Ainf.ainfTowerL p O hv ε hε) Dt ch.gb O₀ cj Ad dL
    (WdAinf.thetaBar_surj p O hv ε hε) hab hcj hAd hdL
    (fun n => Ideal.mk_ker (I := Ideal.span {(p : O) ^ (n + 1)}))
    (fun n => IsPrimitiveRoot.coe_units_iff.1 (Ainf.zeta_primitive p O hv ε hε n))
    (fun n => Units.ext (Ainf.zeta_succ_pow p O ε n))
    τ hτ hτp hbas hperf
  refine ⟨Dt,
    { K := K
      ρO := wd.ρ1.comp ((Ainf.ainfTowerL p O hv ε hε).q 0)
      ch := ch
      wd := wd
      ρO_eq := rfl
      sm := sm
      fin := fin
      A := A
      H := H
      L := L
      tower_zero_surjective := surjective_ainfTower_zero p O hv ε hε
      tower_zero_ker := ker_ainfTower_zero p O hv ε hε
      zeta0 := ainf_zeta0 p O hv ε hε }, hP, hPL, ?_, ?_⟩
  · intro a R S s π hπ l i m hm
    exact hdL a s π hπ l i m (fun k => by rw [hm k]; exact congrArg (fun M => s.1 (M k l) * (i : (R : Type))) (hρL a))
  · intro a j n
    subst hL
    exact hρ a j n

end GlobalTheory.PeriodDatum
end
end
end
