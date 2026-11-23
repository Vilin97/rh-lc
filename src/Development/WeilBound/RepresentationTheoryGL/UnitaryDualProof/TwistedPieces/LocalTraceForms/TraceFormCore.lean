module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.TraceForm
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Tactic.Linter.Style

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.TraceCompSmulRight

section

@[expose] public section

noncomputable section

open Module

namespace PositivityTheory.RgUd.TP.Loc.Ptf

section Fibre

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem mk_smul (I : Ideal R) (r : R) (w : V ⧸ (I • (⊤ : Submodule R V))) :
    (Ideal.Quotient.mk I r) • w = r • w := by
  induction w using Submodule.Quotient.induction_on with
  | H v => rfl

theorem le_comap (I : Ideal R) (x : V →ₗ[R] V) :
    I • (⊤ : Submodule R V) ≤ (I • (⊤ : Submodule R V)).comap x := by
  rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
  exact Submodule.smul_mono le_rfl le_top

def xq (I : Ideal R) (x : V →ₗ[R] V) :
    (V ⧸ (I • (⊤ : Submodule R V))) →ₗ[R ⧸ I] (V ⧸ (I • (⊤ : Submodule R V))) where
  toFun := Submodule.mapQ _ _ x (le_comap I x)
  map_add' := map_add _
  map_smul' c w := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    simp only [RingHom.id_apply, mk_smul]
    exact map_smul _ r w

theorem xq_mk (I : Ideal R) (x : V →ₗ[R] V) (v : V) :
    xq I x (Submodule.Quotient.mk v) = Submodule.Quotient.mk (x v) := rfl

theorem xq_ext (I : Ideal R) {f g : (V ⧸ (I • (⊤ : Submodule R V))) →ₗ[R ⧸ I] (V ⧸ (I • (⊤ : Submodule R V)))}
    (h : ∀ v : V, f (Submodule.Quotient.mk v) = g (Submodule.Quotient.mk v)) : f = g :=
  LinearMap.ext fun w => by
    induction w using Submodule.Quotient.induction_on with
    | H v => exact h v

theorem xq_mul (I : Ideal R) (x y : V →ₗ[R] V) : xq I (x * y) = xq I x * xq I y :=
  xq_ext I fun _ => rfl

theorem xq_one (I : Ideal R) : xq I (1 : V →ₗ[R] V) = 1 := xq_ext I fun _ => rfl

theorem xq_zero (I : Ideal R) : xq I (0 : V →ₗ[R] V) = 0 := xq_ext I fun _ => rfl

theorem xq_add (I : Ideal R) (x y : V →ₗ[R] V) : xq I (x + y) = xq I x + xq I y :=
  xq_ext I fun _ => rfl

theorem xq_pow (I : Ideal R) (x : V →ₗ[R] V) (m : ℕ) : xq I (x ^ m) = xq I x ^ m := by
  induction m with
  | zero => simp [xq_one]
  | succ m ih => rw [pow_succ, xq_mul, ih, pow_succ]

theorem xq_smul {k : Type*} [Field k] [Algebra k R] [Module k V] [IsScalarTower k R V] (I : Ideal R) (c : k)
    (x : V →ₗ[R] V) : xq I (c • x) = (algebraMap k (R ⧸ I) c) • xq I x := by
  refine xq_ext I fun v => ?_
  rw [LinearMap.smul_apply, xq_mk, xq_mk, LinearMap.smul_apply, ← algebraMap_smul R c (x v),
    ← Ideal.Quotient.mk_algebraMap, mk_smul]
  rfl

theorem trace_comp_smulRight {K W : Type*} [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (f : W →ₗ[K] W) (φ : Module.Dual K W) (w : W) : LinearMap.trace K W (f * φ.smulRight w) = φ (f w) := by
  have e : f * φ.smulRight w = φ.smulRight (f w) := by
    ext u
    simp
  have e2 : φ.smulRight (f w) = dualTensorHom K W W (φ ⊗ₜ f w) := by
    ext u
    simp [dualTensorHom_apply]
  rw [e, e2, LinearMap.trace_eq_contract_apply]
  simp

end Fibre

open Classical

attribute [local instance] Ideal.Quotient.field

instance isMax {R : Type*} [CommRing R] (I : MaximalSpectrum R) : I.asIdeal.IsMaximal := I.isMaximal

theorem finQ (k : Type*) {R V : Type*} [Field k] [CommRing R] [Algebra k R] [AddCommGroup V] [Module R V] [Module k V]
    [IsScalarTower k R V] [FiniteDimensional k V] (I : MaximalSpectrum R) :
    FiniteDimensional (R ⧸ I.asIdeal) (V ⧸ (I.asIdeal • (⊤ : Submodule R V))) := by
  haveI : Module.Finite R V := Module.Finite.of_restrictScalars_finite k R V
  exact Module.Finite.of_restrictScalars_finite R _ _

theorem exists_lam (k : Type*) {R : Type*} [Field k] [CommRing R] [Algebra k R] (I : MaximalSpectrum R) :
    ∃ l : (R ⧸ I.asIdeal) →ₗ[k] k, l 1 ≠ 0 := by
  let b := Module.Free.chooseBasis k (R ⧸ I.asIdeal)
  have h1 : b.repr 1 ≠ 0 := by
    intro h
    exact one_ne_zero (b.repr.injective (h.trans (map_zero _).symm))
  obtain ⟨i, hi⟩ : ∃ i, b.repr 1 i ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact h1 (Finsupp.ext hne)
  exact ⟨b.coord i, hi⟩

variable {k R V : Type*} [Field k] [CommRing R] [IsArtinianRing R] [IsReduced R] [Algebra k R]
  [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V] [FiniteDimensional k V]

instance : Fintype (MaximalSpectrum R) := Fintype.ofFinite _

def lam (I : MaximalSpectrum R) : (R ⧸ I.asIdeal) →ₗ[k] k := (exists_lam k I).choose

theorem lam_one (I : MaximalSpectrum R) : lam (k := k) I 1 ≠ 0 := (exists_lam k I).choose_spec

def tI (I : MaximalSpectrum R) (x : V →ₗ[R] V) : k :=
  haveI := finQ k (V := V) I
  lam (k := k) I (LinearMap.trace (R ⧸ I.asIdeal) _ (xq I.asIdeal x))

theorem tI_add (I : MaximalSpectrum R) (x y : V →ₗ[R] V) : tI (k := k) I (x + y) = tI I x + tI I y := by
  simp only [tI, xq_add, map_add (f := _)]

theorem tI_smul (I : MaximalSpectrum R) (c : k) (x : V →ₗ[R] V) : tI (k := k) I (c • x) = c • tI I x := by
  simp only [tI, xq_smul, map_smul, smul_eq_mul]
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

def tau : (V →ₗ[R] V) →ₗ[k] k where
  toFun x := ∑ I : MaximalSpectrum R, tI (k := k) I x
  map_add' x y := by simp only [tI_add, Finset.sum_add_distrib]
  map_smul' c x := by simp only [tI_smul, RingHom.id_apply, Finset.smul_sum]

theorem tau_apply (x : V →ₗ[R] V) : tau (k := k) x = ∑ I : MaximalSpectrum R, tI (k := k) I x := rfl

theorem tau_comm (x y : V →ₗ[R] V) : tau (k := k) (x * y) = tau (k := k) (y * x) := by
  simp only [tau_apply, tI, xq_mul, LinearMap.trace_mul_comm]

theorem tau_nil (x : V →ₗ[R] V) (hx : IsNilpotent x) : tau (k := k) x = 0 := by
  rw [tau_apply]
  refine Finset.sum_eq_zero fun I _ => ?_
  haveI := finQ k (V := V) I
  obtain ⟨m, hm⟩ := hx
  have h1 : IsNilpotent (xq I.asIdeal x) := ⟨m, by rw [← xq_pow, hm, xq_zero]⟩
  have h2 := (LinearMap.isNilpotent_trace_of_isNilpotent h1).eq_zero
  simp only [tI, h2, map_zero]

def eI (I : MaximalSpectrum R) : R := (IsArtinianRing.equivPi R).symm (Pi.single I 1)

theorem equivPi_apply' (r : R) (J : MaximalSpectrum R) :
    IsArtinianRing.equivPi R r J = Ideal.Quotient.mk J.asIdeal r := rfl

theorem eI_mem {I J : MaximalSpectrum R} (h : J ≠ I) : eI I ∈ J.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← equivPi_apply', eI, AlgEquiv.apply_symm_apply, Pi.single_eq_of_ne h]

theorem eI_sub_one (I : MaximalSpectrum R) : eI I - 1 ∈ I.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← equivPi_apply', eI, AlgEquiv.apply_symm_apply, Pi.single_eq_same,
    map_one, sub_self]

theorem eI_mul (I : MaximalSpectrum R) {r : R} (hr : r ∈ I.asIdeal) : eI I * r = 0 := by
  apply (IsArtinianRing.equivPi R).injective
  rw [map_mul, map_zero, eI, AlgEquiv.apply_symm_apply]
  funext J
  by_cases h : J = I
  · subst h
    simp [equivPi_apply', Ideal.Quotient.eq_zero_iff_mem.2 hr]
  · simp [Pi.single_eq_of_ne h]

theorem sum_eI : ∑ I : MaximalSpectrum R, eI I = 1 := by
  apply (IsArtinianRing.equivPi R).injective

  rw [map_sum, map_one]
  simp only [eI, AlgEquiv.apply_symm_apply]
  exact Finset.univ_sum_single 1

theorem eI_smul_eq_zero (I : MaximalSpectrum R) {w : V} (hw : w ∈ I.asIdeal • (⊤ : Submodule R V)) :
    eI I • w = 0 := by
  refine Submodule.smul_induction_on (p := fun w => eI I • w = 0) hw (fun r hr m _ => ?_) (fun a b ha hb => ?_)
  · rw [smul_smul, eI_mul I hr, zero_smul]
  · rw [smul_add, ha, hb, add_zero]

theorem eq_zero_of_xq (x : V →ₗ[R] V) (h : ∀ I : MaximalSpectrum R, xq I.asIdeal x = 0) : x = 0 := by
  ext v
  have hv : ∀ I : MaximalSpectrum R, x v ∈ I.asIdeal • (⊤ : Submodule R V) := fun I => by
    rw [← Submodule.Quotient.mk_eq_zero, ← xq_mk, h I, LinearMap.zero_apply]
  rw [LinearMap.zero_apply, ← one_smul R (x v), ← sum_eI, Finset.sum_smul]
  exact Finset.sum_eq_zero fun I _ => eI_smul_eq_zero I (hv I)

def sec (I : MaximalSpectrum R) : (V ⧸ (I.asIdeal • (⊤ : Submodule R V))) →ₗ[R] V :=
  (I.asIdeal • (⊤ : Submodule R V)).liftQ (eI I • LinearMap.id) fun w hw => by
    simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
    exact eI_smul_eq_zero I hw

theorem exists_lift (I : MaximalSpectrum R)
    (g : (V ⧸ (I.asIdeal • (⊤ : Submodule R V))) →ₗ[R ⧸ I.asIdeal] (V ⧸ (I.asIdeal • (⊤ : Submodule R V)))) :
    ∃ y : V →ₗ[R] V, xq I.asIdeal y = g ∧ ∀ J ≠ I, xq J.asIdeal y = 0 := by
  refine ⟨sec I ∘ₗ (g.restrictScalars R) ∘ₗ (I.asIdeal • (⊤ : Submodule R V)).mkQ, ?_, fun J hJ => ?_⟩
  · refine xq_ext _ fun v => ?_
    obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective _ (g (Submodule.Quotient.mk v))
    rw [xq_mk]
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.restrictScalars_apply]
    rw [← hu, sec, Submodule.liftQ_apply]
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
    have e : eI I • u - u = (eI I - 1) • u := by rw [sub_smul, one_smul]
    rw [e]
    exact Submodule.smul_mem_smul (eI_sub_one I) (Submodule.mem_top : u ∈ (⊤ : Submodule R V))
  · refine xq_ext _ fun v => ?_
    obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective _ (g (Submodule.Quotient.mk v))
    rw [xq_mk]
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.restrictScalars_apply]
    rw [← hu, sec, Submodule.liftQ_apply]
    simp only [LinearMap.smul_apply, LinearMap.id_apply, LinearMap.zero_apply]
    rw [Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul (eI_mem hJ) (Submodule.mem_top : u ∈ (⊤ : Submodule R V))

theorem tau_nondeg (x : V →ₗ[R] V) (h : ∀ y : V →ₗ[R] V, tau (k := k) (x * y) = 0) : x = 0 := by
  by_contra hx
  obtain ⟨I, hI⟩ : ∃ I : MaximalSpectrum R, xq I.asIdeal x ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact hx (eq_zero_of_xq x hne)
  haveI := finQ k (V := V) I
  obtain ⟨w, hw⟩ : ∃ w, xq I.asIdeal x w ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact hI (LinearMap.ext hne)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual (R ⧸ I.asIdeal) _, φ (xq I.asIdeal x w) ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact hw ((Module.forall_dual_apply_eq_zero_iff _ _).1 hne)
  obtain ⟨y, hy1, hy2⟩ := exists_lift I ((φ (xq I.asIdeal x w))⁻¹ • φ.smulRight w)
  have := h y
  rw [tau_apply, Finset.sum_eq_single I] at this
  · apply lam_one (k := k) I
    simp only [tI, xq_mul, hy1] at this
    rwa [mul_smul_comm, map_smul, trace_comp_smulRight, smul_eq_mul, inv_mul_cancel₀ hφ] at this
  · intro J _ hJ
    simp only [tI, xq_mul, hy2 J hJ, mul_zero, map_zero]
  · intro hn
    exact absurd (Finset.mem_univ I) hn

theorem exists_tau : ∃ τ : (V →ₗ[R] V) →ₗ[k] k, (∀ x y, τ (x * y) = τ (y * x)) ∧
    (∀ x, (∀ y, τ (x * y) = 0) → x = 0) ∧ ∀ x, IsNilpotent x → τ x = 0 :=
  ⟨tau, tau_comm, tau_nondeg, tau_nil⟩

end PositivityTheory.RgUd.TP.Loc.Ptf
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.TraceFormCore

section

@[expose] public section

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.TP.Loc.Ptf

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP

variable {k : Type} [Field k] {n : ℕ}

def bSub (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Submodule k (Matrix (Fin n) (Fin n) k) where
  carrier := Bz Z
  add_mem' {x y} hx hy a ha := by rw [mul_add, add_mul, hx a ha, hy a ha]
  zero_mem' a _ := by simp
  smul_mem' c x hx a ha := by rw [mul_smul_comm, smul_mul_assoc, hx a ha]

theorem mul_mem_bz {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {x y : Matrix (Fin n) (Fin n) k} (hx : x ∈ Bz Z)
    (hy : y ∈ Bz Z) : x * y ∈ Bz Z := by
  intro a ha
  rw [← mul_assoc, hx a ha, mul_assoc, hy a ha, ← mul_assoc]

def RZ (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Type := Z

section Inst

variable (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z)

def crZ : CommRing (RZ Z) := { (inferInstance : Ring Z) with mul_comm := fun a b => Subtype.ext (hZ.1 _ a.2 _ b.2) }

def valZ : @RingHom (RZ Z) (Matrix (Fin n) (Fin n) k) (crZ Z hZ).toNonAssocSemiring _ :=
  letI := crZ Z hZ
  { toFun := fun z => (show Z from z).1
    map_one' := rfl
    map_mul' := fun _ _ => rfl
    map_zero' := rfl
    map_add' := fun _ _ => rfl }

def algZ : @RingHom k (RZ Z) _ (crZ Z hZ).toNonAssocSemiring :=
  letI := crZ Z hZ
  { toFun := fun c => (show RZ Z from (⟨algebraMap k _ c, Z.algebraMap_mem c⟩ : Z))
    map_one' := Subtype.ext (map_one _)
    map_mul' := fun a b => Subtype.ext (map_mul (algebraMap k (Matrix (Fin n) (Fin n) k)) a b)
    map_zero' := Subtype.ext (map_zero _)
    map_add' := fun a b => Subtype.ext (map_add (algebraMap k (Matrix (Fin n) (Fin n) k)) a b) }

end Inst

theorem traceForm_core (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) :
    ∃ τ : Matrix (Fin n) (Fin n) k →ₗ[k] k,
      (∀ x ∈ Bz Z, ∀ y ∈ Bz Z, τ (x * y) = τ (y * x)) ∧ (∀ x ∈ Bz Z, (∀ y ∈ Bz Z, τ (x * y) = 0) → x = 0) ∧
        ∀ x ∈ NB Z, τ x = 0 := by
  letI : CommRing (RZ Z) := crZ Z hZ
  letI : Algebra k (RZ Z) := (algZ Z hZ).toAlgebra
  letI : Module (RZ Z) (Fin n → k) := Module.compHom (Fin n → k)
    ((Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toRingEquiv.toRingHom.comp (valZ Z hZ))
  have hsmul : ∀ (r : RZ Z) (v : Fin n → k), r • v = (valZ Z hZ r) *ᵥ v := fun r v => rfl
  have hval : ∀ (c : k) (r : RZ Z), valZ Z hZ (c • r) = c • valZ Z hZ r := by
    intro c r
    rw [Algebra.smul_def, map_mul]
    show algebraMap k (Matrix (Fin n) (Fin n) k) c * valZ Z hZ r = _
    rw [Algebra.smul_def]
  haveI : IsScalarTower k (RZ Z) (Fin n → k) := ⟨fun c r v => by
    rw [hsmul, hsmul, hval, Matrix.smul_mulVec]⟩
  let L : RZ Z →ₗ[k] Matrix (Fin n) (Fin n) k :=
    { toFun := valZ Z hZ
      map_add' := map_add _
      map_smul' := hval }
  have hLinj : Function.Injective L := fun a b h => Subtype.ext h
  haveI : Module.Finite k (RZ Z) := Module.Finite.of_injective L hLinj
  haveI : IsArtinianRing (RZ Z) := IsArtinianRing.of_finite k (RZ Z)
  haveI : IsReduced (RZ Z) := hZ.2
  obtain ⟨τ0, hc, hnd, hnil⟩ := exists_tau (k := k) (R := RZ Z) (V := Fin n → k)
  have hcomm : ∀ x ∈ Bz Z, ∀ r : RZ Z, x * valZ Z hZ r = valZ Z hZ r * x :=
    fun x hx r => (hx _ (show Z from r).2).symm
  let ψ : bSub Z →ₗ[k] ((Fin n → k) →ₗ[RZ Z] (Fin n → k)) :=
    { toFun := fun x =>
        { toFun := fun v => x.1 *ᵥ v
          map_add' := fun v w => Matrix.mulVec_add _ _ _
          map_smul' := fun r v => by
            show x.1 *ᵥ (valZ Z hZ r *ᵥ v) = valZ Z hZ r *ᵥ (x.1 *ᵥ v)
            rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcomm x.1 x.2 r] }
      map_add' := fun x y => LinearMap.ext fun v => by
        show (x.1 + y.1) *ᵥ v = x.1 *ᵥ v + y.1 *ᵥ v
        exact Matrix.add_mulVec _ _ _
      map_smul' := fun c x => LinearMap.ext fun v => by
        show (c • x.1) *ᵥ v = c • (x.1 *ᵥ v)
        exact Matrix.smul_mulVec _ _ _ }
  have hψ : ∀ (x : bSub Z) (v : Fin n → k), ψ x v = x.1 *ᵥ v := fun x v => rfl
  have hψmul : ∀ x (hx : x ∈ Bz Z) y (hy : y ∈ Bz Z),
      ψ ⟨x * y, mul_mem_bz hx hy⟩ = ψ ⟨x, hx⟩ * ψ ⟨y, hy⟩ := by
    intro x hx y hy
    refine LinearMap.ext fun v => ?_
    rw [Module.End.mul_apply, hψ, hψ, hψ, Matrix.mulVec_mulVec]
  obtain ⟨τ, hτ⟩ := LinearMap.exists_extend (τ0.comp ψ)
  have hτx : ∀ x (hx : x ∈ Bz Z), τ x = τ0 (ψ ⟨x, hx⟩) := fun x hx =>
    LinearMap.congr_fun hτ ⟨x, hx⟩
  refine ⟨τ, ?_, ?_, ?_⟩
  · intro x hx y hy
    rw [hτx _ (mul_mem_bz hx hy), hτx _ (mul_mem_bz hy hx), hψmul x hx y hy, hψmul y hy x hx, hc]
  · intro x hx H
    have hsurj : ∀ g : (Fin n → k) →ₗ[RZ Z] (Fin n → k), ∃ y : bSub Z, ψ y = g := by
      intro g
      let y := LinearMap.toMatrix' (g.restrictScalars k)
      have hy : ∀ v, y *ᵥ v = g v := fun v => LinearMap.toMatrix'_mulVec _ _
      have hyB : y ∈ Bz Z := by
        intro a ha
        apply Matrix.toLin'.injective
        refine LinearMap.ext fun v => ?_
        rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec,
          ← Matrix.mulVec_mulVec, hy, hy]
        exact (g.map_smul (show RZ Z from (⟨a, ha⟩ : Z)) v).symm
      exact ⟨⟨y, hyB⟩, LinearMap.ext fun v => hy v⟩
    have h0 : ψ ⟨x, hx⟩ = 0 := hnd _ fun g => by
      obtain ⟨y, rfl⟩ := hsurj g
      rw [← hψmul x hx y.1 y.2, ← hτx]
      exact H y.1 y.2
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, map_zero, LinearMap.zero_apply, ← hψ ⟨x, hx⟩, h0,
      LinearMap.zero_apply]
  · rintro x ⟨hx, m, hm⟩
    rw [hτx x hx]
    apply hnil
    refine ⟨m, LinearMap.ext fun v => ?_⟩
    have hpow : ∀ j : ℕ, (ψ ⟨x, hx⟩ ^ j) v = (x ^ j) *ᵥ v := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ', Module.End.mul_apply, ih, hψ, Matrix.mulVec_mulVec, pow_succ']
    rw [hpow, hm, LinearMap.zero_apply, Matrix.zero_mulVec]

theorem traceForm (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    TraceForm k := fun _ Z hZ => traceForm_core Z hZ

end PositivityTheory.RgUd.TP.Loc.Ptf
end
end
end
