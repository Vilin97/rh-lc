module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulHomInjective
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactClosureZpowersLeftMulGLIffIntegralStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerEqMapNormOneTorusStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjIntegralIffLatticeUnimodularStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLLatticeSpannedByGLColumnsEqFullLattice

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TwOrbLat

theorem exists_lat_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ)
    (e : K.E ≃+* w.adicCompletion E) (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (b : Module.Basis (Fin a) K.E B.A)
    (L : Submodule K.O B.A), GlobalTheory.UnitLemma.IsLat K.O K.E L → ∃ q : GLw a w, GlobalTheory.TwLat.lat e b q = L := by
  intro E _ _ _ w K e a B b L hL
  obtain ⟨hfg, hspan⟩ := hL
  haveI : Module.Finite K.O L := Module.Finite.iff_fg.mpr hfg
  haveI : NoZeroSMulDivisors K.O B.A := ⟨fun {r x} h => by
    rw [← algebraMap_smul K.E r x] at h
    rcases smul_eq_zero.mp h with h | h
    · left; exact (IsFractionRing.injective K.O K.E) (by simpa using h)
    · right; exact h⟩
  haveI : Module.Free K.O L := Module.free_of_finite_type_torsion_free'
  let y := Module.Free.chooseBasis K.O L
  let v : Module.Free.ChooseBasisIndex K.O L → B.A := fun i => (y i : B.A)
  have hli : LinearIndependent K.O v := y.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
  have hliE : LinearIndependent K.E v := (LinearIndependent.iff_fractionRing K.O K.E).mp hli
  have hLv : Submodule.span K.O (Set.range v) = L := by
    have : Set.range v = L.subtype '' Set.range y := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, y.span_eq, Submodule.map_subtype_top]
  have hspE : Submodule.span K.E (Set.range v) = ⊤ := by
    rw [← Submodule.span_span_of_tower K.O K.E, hLv]; exact hspan
  let c := Module.Basis.mk hliE hspE.ge
  let c' := c.reindex (c.indexEquiv b)
  let U : (Matrix (Fin a) (Fin a) K.E)ˣ :=
    ⟨b.toMatrix c', c'.toMatrix b, b.toMatrix_mul_toMatrix_flip c', c'.toMatrix_mul_toMatrix_flip b⟩
  refine ⟨Units.map (e.toRingHom.mapMatrix : Matrix (Fin a) (Fin a) K.E →+* _).toMonoidHom U, ?_⟩
  rw [latOf_eq, ← hLv]
  have hcol : ∀ j, (ofCrd e b fun i =>
      (Units.map (e.toRingHom.mapMatrix : Matrix (Fin a) (Fin a) K.E →+* _).toMonoidHom U).val i j) = c' j := by
    intro j
    rw [← ofCrd_crd e b (c' j)]
    congr 1
  simp only [hcol]
  congr 1
  ext x
  simp only [Set.mem_range]
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨(c.indexEquiv b).symm j, ?_⟩
    simp [c', c, v]
  · rintro ⟨i, rfl⟩
    refine ⟨c.indexEquiv b i, ?_⟩
    simp [c', c, v]

end GlobalTheory.TwOrbLat
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLLatticeSpannedByGLColumnsEqFullLatticeStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_GL_latticeSpannedByGLColumns_eq_fullLattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (b : Module.Basis (Fin a) K.E B.A) (L : Submodule K.O B.A), GlobalTheory.UnitLemma.IsLat K.O K.E L → ∃ q : GLw a w, GlobalTheory.TwLat.lat e b q = L := by
  first | exact @GlobalTheory.TwOrbLat.exists_lat_eq | exact GlobalTheory.TwOrbLat.exists_lat_eq | (intros; apply GlobalTheory.TwOrbLat.exists_lat_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSpannedByGLColumnsEqIff

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TwOrbLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {a : ℕ} {B : GlobalTheory.UnitLemma.InvAlg K} (b : Module.Basis (Fin a) K.E B.A)

theorem crd_smulO (c : K.O) (y : B.A) : crd e b (c • y) = e (algebraMap K.O K.E c) • crd e b y := by
  rw [← crd_smul, algebraMap_smul]

theorem crd_zero : crd e b (0 : B.A) = 0 := by
  funext i; simp [crd]

theorem mem_lat_iff (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (q : GLw a w) (y : B.A) :
    y ∈ GlobalTheory.TwLat.lat e b q ↔ ∀ i, Valued.v (((q⁻¹ : GLw a w).val *ᵥ crd e b y) i) ≤ 1 := by
  rw [latOf_eq]
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro i
      rw [crd_ofCrd, ← col_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    | zero => intro i; simp [crd_zero]
    | add x z _ _ hx hz =>
      intro i
      rw [crd_add, Matrix.mulVec_add, Pi.add_apply]
      exact (Valued.v.map_add _ _).trans (max_le (hx i) (hz i))
    | smul c x _ hx =>
      intro i
      rw [crd_smulO, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul]
      exact mul_le_one' ((he _).1 ⟨c, rfl⟩) (hx i)
  · intro h
    choose c hc using fun j => (he (e.symm (((q⁻¹ : GLw a w).val *ᵥ crd e b y) j))).2 (by
      rw [RingEquiv.apply_symm_apply]; exact h j)
    have hy : y = ∑ j, c j • ofCrd e b (fun i => q.val i j) := by
      apply crd_injective e b
      rw [crd_sum]
      have h1 : crd e b y = q.val *ᵥ ((q⁻¹ : GLw a w).val *ᵥ crd e b y) := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      conv_lhs => rw [h1]
      funext i
      simp only [crd_smulO, hc, RingEquiv.apply_symm_apply, crd_ofCrd, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [hy]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem lat_le_iff (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (q q' : GLw a w) :
    GlobalTheory.TwLat.lat e b q ≤ GlobalTheory.TwLat.lat e b q' ↔ ∀ i j, Valued.v ((q'⁻¹ * q : GLw a w).val i j) ≤ 1 := by
  constructor
  · intro hle i j
    have hm : ofCrd e b (fun i => q.val i j) ∈ GlobalTheory.TwLat.lat e b q := by
      rw [latOf_eq]; exact Submodule.subset_span ⟨j, rfl⟩
    have := (mem_lat_iff e b he q' _).1 (hle hm) i
    rw [crd_ofCrd, ← col_mul, ← Units.val_mul] at this
    exact this
  · intro h
    conv_lhs => rw [latOf_eq]
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, mem_lat_iff e b he, crd_ofCrd, ← col_mul, ← Units.val_mul]
    exact fun i => h i j

theorem lat_eq_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ)
    (e : K.E ≃+* w.adicCompletion E), (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) →
    ∀ (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (b : Module.Basis (Fin a) K.E B.A) (q q' : GLw a w),
    GlobalTheory.TwLat.lat e b q = GlobalTheory.TwLat.lat e b q' ↔ q⁻¹ * q' ∈ GlobalTheory.LFun.KGL w (n := a) := by
  intro E _ _ _ w K e he a B b q q'
  rw [le_antisymm_iff, lat_le_iff e b he, lat_le_iff e b he, GlobalTheory.LFun.KGL, GlobalTheory.AdelicU.mem_GLint_iff,
    _root_.mul_inv_rev, inv_inv]
  exact and_comm

end GlobalTheory.TwOrbLat
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSpannedByGLColumnsEqIffStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.latticeSpannedByGLColumns_eq_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (b : Module.Basis (Fin a) K.E B.A) (q q' : GLw a w), GlobalTheory.TwLat.lat e b q = GlobalTheory.TwLat.lat e b q' ↔ q⁻¹ * q' ∈ GlobalTheory.LFun.KGL w (n := a) := by
  first | exact @GlobalTheory.TwOrbLat.lat_eq_iff | exact GlobalTheory.TwOrbLat.lat_eq_iff | (intros; apply GlobalTheory.TwOrbLat.lat_eq_iff <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralUnitGLEqHermitianLatticeCo

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TwOrbLat

open GlobalTheory.UnitLemma

variable {K : UQ} {B : InvAlg K}

theorem mulLat_mem_iff (t : B.Aˣ) (L : Submodule K.O B.A) (y : B.A) :
    y ∈ mulLat K.O (t : B.A) L ↔ ((t⁻¹ : B.Aˣ) : B.A) * y ∈ L := by
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 h
    simpa [← mul_assoc] using hx
  · intro h
    exact Submodule.mem_map.2 ⟨_, h, by simp [← mul_assoc]⟩

theorem mem_stabLat_iff (t : B.Aˣ) (L : Submodule K.O B.A) :
    t ∈ stabLat K.O L ↔ mulLat K.O (t : B.A) L = L := by
  constructor
  · intro h
    ext y
    rw [mulLat_mem_iff, h (((t⁻¹ : B.Aˣ) : B.A) * y), ← mul_assoc, Units.mul_inv, one_mul]
  · intro h y
    conv_rhs => rw [← h]
    rw [mulLat_mem_iff, ← mul_assoc, Units.inv_mul, one_mul]

theorem stabLat_mulLat (t : B.Aˣ) (L : Submodule K.O B.A) :
    stabLat K.O (mulLat K.O (t : B.A) L) = stabLat K.O L := by
  ext s
  change (∀ y, y ∈ mulLat K.O (t : B.A) L ↔ (s : B.A) * y ∈ mulLat K.O (t : B.A) L) ↔ ∀ y, y ∈ L ↔ (s : B.A) * y ∈ L
  simp only [mulLat_mem_iff]
  constructor
  · intro h y
    have := h ((t : B.A) * y)
    have e1 : ((t⁻¹ : B.Aˣ) : B.A) * ((t : B.A) * y) = y := by rw [← mul_assoc, Units.inv_mul, one_mul]
    have e2 : ((t⁻¹ : B.Aˣ) : B.A) * ((s : B.A) * ((t : B.A) * y)) = s * y := by rw [mul_left_comm, e1]
    rwa [e1, e2] at this
  · intro h y
    rw [h (((t⁻¹ : B.Aˣ) : B.A) * y), mul_left_comm]

theorem avg_const {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have hR : rStab (fun _ : H => c) = ⊤ := by
    ext k; simp [GlobalTheory.TwOrbConj.mem_rStab]
  unfold avg
  have h1 : ∀ x : H ⧸ (⊤ : Subgroup H), x = 1 := fun x =>
    QuotientGroup.induction_on x fun g => (QuotientGroup.eq_one_iff g).2 (Subgroup.mem_top g)
  rw [hR, Subgroup.index_top, finsum_eq_single _ (1 : H ⧸ (⊤ : Subgroup H)) (fun x hx => absurd (h1 x) hx)]
  simp

theorem cast_finsum {α : Type} (f : α → ℚ) : ((∑ᶠ i, f i : ℚ) : ℂ) = ∑ᶠ i, (f i : ℂ) := by
  by_cases h : (Function.support f).Finite
  · exact (Rat.castHom ℂ).toAddMonoidHom.map_finsum h
  · have h' : ¬ (Function.support fun i => (f i : ℂ)).Finite := by
      have : (Function.support fun i => (f i : ℂ)) = Function.support f := by ext i; simp
      rwa [this]
    rw [finsum_of_infinite_support h, finsum_of_infinite_support h', Rat.cast_zero]

end GlobalTheory.TwOrbLat

open GlobalTheory.UnitLemma GlobalTheory.TwOrbLat in
theorem GlobalTheory.TwOrbLat.twOrb_unit_eq_orbSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K), B.P.Separable → ∀ (β : B.Aˣ) (ε : B.A), (ε = 1 ∨ ε = -1) → B.σ (β : B.A) = β * (ε * B.g) → ∀ (b : Module.Basis (Fin a) K.E B.A) (δ : GLw a w), (∀ i j, ((δ.val * GlobalTheory.Tw.Phi a (w.adicCompletion E))⁻¹)ᵀ i j = e (B.herm β (b i) (b j))) → twOrb (thL a w) (GlobalTheory.LFun.KGL w (n := a)) δ ((GlobalTheory.LFun.KGL w (n := a) : Set (GLw a w)).indicator 1) = ((GlobalTheory.UnitLemma.orbSum K.O B.T {L : Submodule K.O B.A | GlobalTheory.UnitLemma.IsLat K.O K.E L ∧ ∀ z, z ∈ L ↔ ∀ y ∈ L, B.herm β y z ∈ (algebraMap K.O K.E).range} (fun _ => 1) : ℚ) : ℂ) := by
  intro E _ _ _ hU w hw K e he hO a B hP β ε hε hβ b δ hδ
  set θ := thL a w with hθ
  set Kg := GlobalTheory.LFun.KGL w (n := a) with hKg
  set ι := mulGL e b with hι
  set T' := twCent θ δ with hT'
  have hCent : T' = B.T.map ι := GlobalTheory.T.twistedCentralizer_eq_map_normOneTorus E w hw K e he a B hP β ε hε hβ b δ hδ
  have hinj : Function.Injective ι := mulGL_injective e b
  have hθK : ∀ k ∈ Kg, θ k ∈ Kg := GlobalTheory.BCT.ThBasic.thL_mem_KGL hU a w

  have hstab : ∀ (t : B.Aˣ) (q : GLw a w), ι t ∈ Kg.map (MulAut.conj q).toMonoidHom ↔
      t ∈ stabLat K.O (GlobalTheory.TwLat.lat e b q) := by
    intro t q
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, mem_stabLat_iff,
      ← latOf_mul e b t q, eq_comm, GlobalTheory.T.latticeSpannedByGLColumns_eq_iff E w K e hO a B b, mul_assoc]
  have hcpt : cptPart T' = (intUnits K.O B.A ⊓ B.T).map ι := by
    rw [hCent]
    unfold cptPart
    have hS : {x | x ∈ B.T.map ι ∧ IsCompact (closure (Subgroup.zpowers x : Set (GLw a w)))} =
        ι '' ((intUnits K.O B.A ⊓ B.T : Subgroup B.Aˣ) : Set B.Aˣ) := by
      ext x
      constructor
      · rintro ⟨⟨t, ht, rfl⟩, hc⟩
        exact ⟨t, ⟨(GlobalTheory.T.isCompact_closure_zpowers_leftMulGL_iff_integral E w K e hO a B b t).1 hc, ht⟩, rfl⟩
      · rintro ⟨t, ⟨hi, ht⟩, rfl⟩
        exact ⟨⟨t, ht, rfl⟩, (GlobalTheory.T.isCompact_closure_zpowers_leftMulGL_iff_integral E w K e hO a B b t).2 hi⟩
    rw [hS, ← MonoidHom.map_closure, Subgroup.closure_eq]
  have hRel : ∀ y : GLw a w, (T' ⊓ Kg.map (MulAut.conj y).toMonoidHom).relIndex (cptPart T') =
      (stabLat K.O (GlobalTheory.TwLat.lat e b y) ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) := by
    intro y
    have h1 : T' ⊓ Kg.map (MulAut.conj y).toMonoidHom = (stabLat K.O (GlobalTheory.TwLat.lat e b y) ⊓ B.T).map ι := by
      ext x
      rw [Subgroup.mem_inf, hCent]
      constructor
      · rintro ⟨⟨t, ht, rfl⟩, hx⟩
        exact ⟨t, ⟨(hstab t y).1 hx, ht⟩, rfl⟩
      · rintro ⟨t, ⟨hs, ht⟩, rfl⟩
        exact ⟨⟨t, ht, rfl⟩, (hstab t y).2 hs⟩
    rw [h1, hcpt, Subgroup.relIndex_map_map_of_injective _ _ hinj]

  set P : GLw a w → Prop := fun y => y⁻¹ * δ * θ y ∈ Kg with hP_def
  have hPinv : ∀ (y t k : GLw a w), t ∈ T' → k ∈ Kg → (P (t * y * k) ↔ P y) := by
    intro y t k ht hk
    have hd : t⁻¹ * δ * θ t = δ := by
      rw [mul_assoc, ← (GlobalTheory.TwOrbConj.mem_twCent θ δ t).1 ht, inv_mul_cancel_left]
    have e1 : (t * y * k)⁻¹ * δ * θ (t * y * k) = k⁻¹ * (y⁻¹ * δ * θ y) * θ k := by
      calc (t * y * k)⁻¹ * δ * θ (t * y * k) = k⁻¹ * (y⁻¹ * (t⁻¹ * δ * θ t) * θ y) * θ k := by
            simp only [map_mul, _root_.mul_inv_rev]; group
        _ = k⁻¹ * (y⁻¹ * δ * θ y) * θ k := by rw [hd]
    simp only [hP_def]
    rw [e1]
    constructor
    · intro h
      have := Kg.mul_mem (Kg.mul_mem hk h) (Kg.inv_mem (hθK k hk))
      simpa [mul_assoc] using this
    · intro h
      exact Kg.mul_mem (Kg.mul_mem (Kg.inv_mem hk) h) (hθK k hk)

  have hsum : ∀ y : GLw a w, GlobalTheory.TwOrbConj.summand θ Kg δ ((Kg : Set (GLw a w)).indicator 1) y =
      if P y then ((((stabLat K.O (GlobalTheory.TwLat.lat e b y) ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) : ℕ) : ℂ)) else 0 := by
    intro y
    have hconst : (fun k : Kg => (Kg : Set (GLw a w)).indicator 1 ((y * k)⁻¹ * δ * θ (y * k))) =
        fun _ => (if P y then (1 : ℂ) else 0) := by
      funext k
      have := hPinv y 1 k (T'.one_mem) k.2
      rw [one_mul] at this
      simp only [Set.indicator_apply, SetLike.mem_coe, Pi.one_apply]
      by_cases h : P y
      · rw [if_pos h, if_pos ((this.2 h))]
      · rw [if_neg h, if_neg (fun h' => h (this.1 h'))]
    unfold GlobalTheory.TwOrbConj.summand
    rw [hconst, avg_const, hRel]
    split_ifs <;> simp

  set X : Set (Submodule K.O B.A) := {L : Submodule K.O B.A | IsLat K.O K.E L ∧
    ∀ z, z ∈ L ↔ ∀ y ∈ L, B.herm β y z ∈ (algebraMap K.O K.E).range} with hX
  have hUni : ∀ y : GLw a w, P y ↔ GlobalTheory.TwLat.lat e b y ∈ X := by
    intro y
    simp only [hP_def, hX, Set.mem_setOf_eq]
    rw [GlobalTheory.T.twistedConj_integral_iff_lattice_unimodular E w hw K e he hO a B β b δ hδ y]
    exact ⟨fun h => ⟨latOf_isLat e b y, h⟩, fun h => h.2⟩
  let r : X → X → Prop := fun L M => ∃ t ∈ B.T, (M : Submodule K.O B.A) = mulLat K.O (t : B.A) (L : Submodule K.O B.A)
  have hr : Equivalence r := by
    refine ⟨fun L => ⟨1, B.T.one_mem, ?_⟩, fun {L M} ⟨t, ht, h⟩ => ⟨t⁻¹, B.T.inv_mem ht, ?_⟩,
      fun {L M N} ⟨t, ht, h⟩ ⟨s, hs, h'⟩ => ⟨s * t, B.T.mul_mem hs ht, ?_⟩⟩
    · ext y; rw [mulLat_mem_iff]; simp
    · ext y; rw [mulLat_mem_iff, h, mulLat_mem_iff]; simp
    · ext y; rw [h', mulLat_mem_iff, h, mulLat_mem_iff, mulLat_mem_iff, ← mul_assoc]; simp [mul_comm]

  let φ : {q : DoubleCoset.Quotient (T' : Set (GLw a w)) (Kg : Set (GLw a w)) // P (Quotient.out q)} →
      Orb K.O B.T X := fun q => Quot.mk _ ⟨GlobalTheory.TwLat.lat e b (Quotient.out q.1), (hUni _).1 q.2⟩
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨q, hq⟩ ⟨q', hq'⟩ h
      obtain ⟨t, ht, h1⟩ := hr.eqvGen_iff.1 (Quot.eqvGen_exact h)
      simp only at h1
      rw [← latOf_mul e b t, GlobalTheory.T.latticeSpannedByGLColumns_eq_iff E w K e hO a B b] at h1
      apply Subtype.ext
      simp only
      rw [← DoubleCoset.out_eq' (H := T') (K := Kg) q, ← DoubleCoset.out_eq' (H := T') (K := Kg) q', DoubleCoset.eq]
      refine ⟨ι t, by rw [hCent]; exact ⟨t, ht, rfl⟩, _, Kg.inv_mem h1, ?_⟩
      rw [_root_.mul_inv_rev, inv_inv, mul_inv_cancel_left]
    · intro o
      induction o using Quot.ind with
      | mk L =>
        obtain ⟨q0, hq0⟩ := GlobalTheory.T.exists_GL_latticeSpannedByGLColumns_eq_fullLattice E w K e a B b L.1 L.2.1
        obtain ⟨t', ht', k, hk, he'⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1
          (DoubleCoset.out_eq' (H := T') (K := Kg) (DoubleCoset.mk T' Kg q0)).symm
        have hP0 : P q0 := (hUni q0).2 (hq0 ▸ L.2)
        refine ⟨⟨DoubleCoset.mk _ _ q0, by rw [he']; exact (hPinv q0 t' k ht' hk).2 hP0⟩, ?_⟩
        apply Quot.sound
        rw [hCent] at ht'
        obtain ⟨t, ht, rfl⟩ := ht'
        refine ⟨t⁻¹, B.T.inv_mem ht, ?_⟩
        show L.1 = _
        simp only
        rw [he', mul_assoc, latOf_mul e b t,
          ← (GlobalTheory.T.latticeSpannedByGLColumns_eq_iff E w K e hO a B b q0 (q0 * k)).2 (by simpa using hk), hq0]
        ext y; rw [mulLat_mem_iff, mulLat_mem_iff]; simp

  rw [GlobalTheory.TwOrbConj.twOrb_eq, orbSum, cast_finsum]
  simp_rw [hsum]
  rw [show (∑ᶠ q : DoubleCoset.Quotient (T' : Set (GLw a w)) (Kg : Set (GLw a w)), if P (Quotient.out q) then
      ((((stabLat K.O (GlobalTheory.TwLat.lat e b (Quotient.out q)) ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) : ℕ) : ℂ)) else 0) =
      ∑ᶠ q : {q : DoubleCoset.Quotient (T' : Set (GLw a w)) (Kg : Set (GLw a w)) // P (Quotient.out q)},
        ((((stabLat K.O (GlobalTheory.TwLat.lat e b (Quotient.out q.1)) ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) : ℕ) : ℂ)) by
    exact (finsum_congr fun q => finsum_eq_if.symm).trans (finsum_subtype_eq_finsum_cond
      (fun q : DoubleCoset.Quotient (T' : Set (GLw a w)) (Kg : Set (GLw a w)) => P (Quotient.out q))
      (f := fun q => ((((stabLat K.O (GlobalTheory.TwLat.lat e b (Quotient.out q)) ⊓ B.T).relIndex
        (intUnits K.O B.A ⊓ B.T) : ℕ) : ℂ)))).symm]
  refine finsum_eq_of_bijective φ hφ fun q => ?_
  obtain ⟨s, hs, hs'⟩ := hr.eqvGen_iff.1 (Quot.eqvGen_exact (Quot.out_eq (φ q)))
  have hs2 : GlobalTheory.TwLat.lat e b (Quotient.out q.1) = mulLat K.O (s : B.A) (Quot.out (φ q)).1 := hs'
  rw [hs2, stabLat_mulLat]
  push_cast
  simp
end
end
end
