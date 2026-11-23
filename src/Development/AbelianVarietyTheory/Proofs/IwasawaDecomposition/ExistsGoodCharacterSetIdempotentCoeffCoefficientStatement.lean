module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
public import Formalism.LocalToGlobal.Columns.GoodXgFin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemLevelOfLocalDepth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCentralIdempotentOfGoodSeriesIdempotent
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrCharCompMemComplexIrrCharSetStatement
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
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
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrCharRealiseOfPrimitiveRootCard
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralIdempotentEqSumCharacterIdempotentsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassFunctionActsByScalarOnIrrCharStatement
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CyclicSplitting.IrrDecomp
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Mathlib.RingTheory.PicardGroup

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrCharMemClosurePrimitiveRootCard

section

@[expose] public section

open Formalism.L2.DIV

namespace GlobalTheory

theorem absIrrChar_mem_closure_primitiveRoot {G : Type} [Group G] [Fintype G] {K : Type} [Field K]
    [CharZero K] (z : K) (hz : IsPrimitiveRoot z (Fintype.card G)) (χ : G → K) (hχ : IsAbsIrrChar χ)
    (g : G) : χ g ∈ Subring.closure ({z} : Set K) := by
  obtain ⟨n, ρ, -, hch⟩ := hχ
  set N := Fintype.card G with hN
  haveI : NeZero N := ⟨Fintype.card_ne_zero⟩
  set f := ρ g with hf
  have hfN : f ^ N = 1 := by rw [hf, ← map_pow, pow_card_eq_one, map_one]
  have htr : LinearMap.trace (AlgebraicClosure K) _ f = (LinearMap.charpoly f).roots.sum := by
    rw [LinearMap.trace_eq_matrix_trace (AlgebraicClosure K) (Pi.basisFun (AlgebraicClosure K) (Fin n)),
      Matrix.trace_eq_sum_roots_charpoly, LinearMap.charpoly_toMatrix]
  have hz' : IsPrimitiveRoot (algebraMap K (AlgebraicClosure K) z) N :=
    hz.map_of_injective (algebraMap K (AlgebraicClosure K)).injective
  have hroot : ∀ μ ∈ (LinearMap.charpoly f).roots,
      ∃ k : ℕ, μ = algebraMap K (AlgebraicClosure K) (z ^ k) := by
    intro μ hμ
    have hev := (Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).mpr (Polynomial.isRoot_of_mem_roots hμ)
    obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
    have h1 := hv.pow_apply N
    rw [hfN] at h1
    have hμN : μ ^ N = 1 := by
      have h2 : (μ ^ N - 1) • v = 0 := by
        rw [sub_smul, ← h1, one_smul]; simp
      rcases smul_eq_zero.mp h2 with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hv.2
    obtain ⟨k, -, hk⟩ := hz'.eq_pow_of_pow_eq_one hμN
    exact ⟨k, by rw [map_pow, hk]⟩
  have hsum : ∀ m : Multiset (AlgebraicClosure K),
      (∀ μ ∈ m, ∃ k : ℕ, μ = algebraMap K (AlgebraicClosure K) (z ^ k)) →
      ∃ y ∈ Subring.closure ({z} : Set K), algebraMap K (AlgebraicClosure K) y = m.sum := by
    intro m
    induction m using Multiset.induction_on with
    | empty => intro _; exact ⟨0, zero_mem _, by simp⟩
    | cons a m ih =>
      intro h
      obtain ⟨y, hy, hy'⟩ := ih (fun μ hμ => h μ (Multiset.mem_cons_of_mem hμ))
      obtain ⟨k, hk⟩ := h a (Multiset.mem_cons_self a m)
      refine ⟨z ^ k + y, add_mem (pow_mem (Subring.subset_closure (Set.mem_singleton z)) k) hy, ?_⟩
      rw [Multiset.sum_cons, map_add (f := _), hy', hk]
  obtain ⟨y, hy, hy'⟩ := hsum _ hroot
  have hχg : algebraMap K (AlgebraicClosure K) (χ g) = algebraMap K (AlgebraicClosure K) y := by
    rw [← hch g, hy', ← htr]; rfl
  rw [(algebraMap K (AlgebraicClosure K)).injective hχg]
  exact hy

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrCharMemClosurePrimitiveRootCardStatement

section

@[expose] public section

open Formalism.L2.DIV

theorem _root_.GlobalTheory.T.absIrrChar_mem_closure_primitiveRoot_card : ∀ {G : Type} [inst : Group G] [inst_1 : Fintype G] {K : Type} [inst_2 : Field K] [inst_3 : CharZero K] (z : K), IsPrimitiveRoot z (Fintype.card G) → ∀ (χ : G → K), IsAbsIrrChar χ → ∀ g : G, χ g ∈ Subring.closure ({z} : Set K) := by
  first | exact @GlobalTheory.absIrrChar_mem_closure_primitiveRoot | exact GlobalTheory.absIrrChar_mem_closure_primitiveRoot | (intros; apply GlobalTheory.absIrrChar_mem_closure_primitiveRoot <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrCharRealiseOfPrimitiveRootCardStatement

section

@[expose] public section

open Formalism.L2.DIV

theorem _root_.GlobalTheory.T.absIrrChar_realise_of_primitiveRoot_card : ∀ {G : Type} [inst : Group G] [inst_1 : Fintype G] {K : Type} [inst_2 : Field K] (σ : K →+* ℂ) (z : K), IsPrimitiveRoot z (Fintype.card G) → ∀ (ψ : G → ℂ), ψ ∈ Formalism.L2.Col.gxIrrSet (G := G) ℂ → ∃ χ : G → K, IsAbsIrrChar χ ∧ ∀ g, σ (χ g) = ψ g := by
  first | exact @GlobalTheory.BrauerRealise.absIrr_realise_of_isPrimitiveRoot | exact GlobalTheory.BrauerRealise.absIrr_realise_of_isPrimitiveRoot | (intros; apply GlobalTheory.BrauerRealise.absIrr_realise_of_isPrimitiveRoot <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumIrrCharOneMulIrrCharColumnOrthogonality

section

@[expose] public section

open Formalism.L2.DIV

namespace GlobalTheory.ColumnOrth

variable {G : Type} [Group G] [Fintype G] [DecidableEq G]

theorem leftRegular_character (g : G) :
    (Representation.leftRegular ℂ G).character g = if g = 1 then (Fintype.card G : ℂ) else 0 := by
  classical
  unfold Representation.character
  rw [LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis G ℂ), Matrix.trace]
  by_cases h : g = 1
  · subst h
    simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun x _ => ?_
    have hx : g * x ≠ x := by simpa using h
    simp [Matrix.diag, LinearMap.toMatrix_apply, MonoidAlgebra.basis, hx]

theorem sum_char_one_mul_char (A : Finset (G → ℂ))
    (hA : ∀ ψ, ψ ∈ A ↔ ψ ∈ Formalism.L2.Col.gxIrrSet (G := G) ℂ) (g : G) :
    ∑ ψ ∈ A, ψ 1 * ψ g = if g = 1 then (Fintype.card G : ℂ) else 0 := by
  classical
  obtain ⟨r, d, τ, hirr, hch⟩ :=
    CycSplitWork.char_eq_sum_irreducible (G := G) (L := ℂ) (Representation.leftRegular ℂ G)
  set χ : Fin r → (G → ℂ) := fun i => (τ i).character with hχ
  have hmem : ∀ i, χ i ∈ A := fun i => (hA _).2 ⟨d i, τ i, hirr i, rfl⟩
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hmult : ∀ ψ ∈ A, (({i | χ i = ψ} : Finset (Fin r)).card : ℂ) = ψ 1 := by
    intro ψ hψ
    have hψ' := (hA ψ).1 hψ
    have h1 : (Nat.card G : ℂ)⁻¹ * ∑ x : G, (Representation.leftRegular ℂ G).character x * ψ x⁻¹ = ψ 1 := by
      simp_rw [leftRegular_character, ite_mul, zero_mul]
      rw [Finset.sum_ite_eq' Finset.univ (1 : G)]
      simp [Nat.card_eq_fintype_card, hcard]
    have h2 : (Nat.card G : ℂ)⁻¹ * ∑ x : G, (Representation.leftRegular ℂ G).character x * ψ x⁻¹ =
        ∑ i, if χ i = ψ then (1 : ℂ) else 0 := by
      simp_rw [hch, Finset.sum_mul]
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      convert Formalism.L2.Col.gx_orth ⟨d i, τ i, hirr i, rfl⟩ hψ'
    rw [← h1, h2, Finset.sum_boole]
  have hr := leftRegular_character (G := G) g
  rw [hch g] at hr
  rw [← hr, ← Finset.sum_fiberwise_of_maps_to (g := χ) (t := A) (fun i _ => hmem i)]
  refine Finset.sum_congr rfl fun ψ hψ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => ψ g) fun i hi => congrFun (Finset.mem_filter.1 hi).2 g, Finset.sum_const, nsmul_eq_mul,
    hmult ψ hψ]

end GlobalTheory.ColumnOrth
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumIrrCharOneMulIrrCharColumnOrthogonalityStatement

section

@[expose] public section

open Formalism.L2.DIV

theorem _root_.GlobalTheory.T.sum_irrChar_one_mul_irrChar_column_orthogonality : ∀ {G : Type} [inst : Group G] [inst_1 : Fintype G] [inst_2 : DecidableEq G] (A : Finset (G → ℂ)), (∀ ψ, ψ ∈ A ↔ ψ ∈ Formalism.L2.Col.gxIrrSet (G := G) ℂ) → ∀ g : G, ∑ ψ ∈ A, ψ 1 * ψ g = if g = 1 then (Fintype.card G : ℂ) else 0 := by
  first | exact @GlobalTheory.ColumnOrth.sum_char_one_mul_char | exact GlobalTheory.ColumnOrth.sum_char_one_mul_char | (intros; apply GlobalTheory.ColumnOrth.sum_char_one_mul_char <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGoodCharacterSetIdempotentCoeffCoefficient

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.GoodSetExists

section Gen

variable {G : Type} [Group G] [Fintype G]

theorem one_ne_zero_of_mem (ψ : G → ℂ) (h : ψ ∈ Formalism.L2.Col.gxIrrSet (G := G) ℂ) : ψ 1 ≠ 0 := by
  obtain ⟨n, ρ, hρ, rfl⟩ := h
  intro e
  rw [Representation.char_one, Nat.cast_eq_zero, Module.finrank_zero_iff] at e
  exact (bot_ne_top (α := Subrepresentation ρ)) (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem coeff_conj_of_center {e : MonoidAlgebra ℂ G} (he : e ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G)) (x y : G) :
    e.coeff (y * x * y⁻¹) = e.coeff x := by
  have h := congrArg (fun a : MonoidAlgebra ℂ G => a.coeff (y * x))
    ((Subalgebra.mem_center_iff.1 he (MonoidAlgebra.single y 1)).symm)
  simp only [MonoidAlgebra.coeff_mul_single_apply, MonoidAlgebra.coeff_single_mul_apply, mul_one, one_mul,
    inv_mul_cancel_left] at h
  exact h

end Gen

section Record

variable (X : Stages) (px : PreX X.B.toPre)

theorem exists_goodSet_Ks (eR : Gc X.B px ≃* G0g X.toD7.nd) :
    ∃ Xg : Finset (Gc X.B px → X.B.LL), GoodSet X (px := px) eR Xg ∧ ∀ g, (idemOf Xg).coeff g ∈ X.B.Ks := by
  classical
  let σ := X.B.embLL
  let f := MonoidAlgebra.domCongr ℂ ℂ eR.symm
  let e : MonoidAlgebra ℂ (Gc X.B px) := f X.toD7.ntypes.e0
  have hcoeff : ∀ g, e.coeff g = X.toD7.ntypes.e0.coeff (eR g) := fun g => by
    simp [e, f, MonoidAlgebra.domCongr_apply]
  obtain ⟨hcen0, hid0⟩ := GlobalTheory.GoodLatCompare.goodSeriesIdempotent_central_idempotent X.toD7
  have hid : e * e = e := by simp only [e, ← map_mul, hid0]
  have hcen : e ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (Gc X.B px)) := by
    refine Subalgebra.mem_center_iff.2 fun b => ?_
    obtain ⟨c, rfl⟩ := f.surjective b
    simp only [e, ← map_mul, (Subalgebra.mem_center_iff.1 hcen0 c)]
  have hcard : Fintype.card (Gc X.B px) = X.B.restRowsFiniteGroupCard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr eR.toEquiv]
    have : ∀ k, NeZero (X.toD7.host.g k) := fun k => ⟨(X.toD7.host.g_prime k).ne_zero⟩
    rw [Nat.card_pi, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    change ∏ _y : X.toD7.nd.PlG k, Nat.card (GL (Fin X.toD7.R.r) (ZMod (X.toD7.host.g k))) = _
    rw [Finset.prod_const, Finset.card_univ, X.toD7.nd.card_PlG k]
    rfl
  obtain ⟨z, hzK, hz⟩ := X.B.roots_Ks X.B.restRowsFiniteGroupCard (by simp)
  have hzp : IsPrimitiveRoot z (Fintype.card (Gc X.B px)) := by
    rw [hcard, ← IsPrimitiveRoot.map_iff_of_injective σ.injective]
    rw [show σ z = _ from hz]
    exact Complex.isPrimitiveRoot_exp _ X.B.restRowsFiniteGroupCard_pos.ne'
  refine ⟨Formalism.L2.Col.XgE σ e, Model.goodSet_of_idem X eR _ Formalism.L2.Col.XgE_irr fun g => ?_, fun g => ?_⟩
  · let A := (Formalism.L2.Col.gxIrrSet_finite (G := Gc X.B px) (k := ℂ)).toFinset
    have hA : ∀ ψ, ψ ∈ A ↔ ψ ∈ Formalism.L2.Col.gxIrrSet (G := Gc X.B px) ℂ := fun ψ => Set.Finite.mem_toFinset _
    have hexp := GlobalTheory.T.centralIdempotent_eq_sum_character_idempotents A e (fun ψ hψ => one_ne_zero_of_mem ψ ((hA ψ).1 hψ)) (GlobalTheory.T.sum_irrChar_one_mul_irrChar_column_orthogonality A hA)
      (fun ψ hψ x => GlobalTheory.T.classFunction_acts_by_scalar_on_irrChar e (coeff_conj_of_center hcen) ψ ((hA ψ).1 hψ) x) hid
    have himg : (A.filter fun ψ => ∑ g, e.coeff g * ψ g = ψ 1) =
        (Formalism.L2.Col.XgE σ e).image (fun χ g => σ (χ g)) := by
      ext ψ
      simp only [Finset.mem_filter, Finset.mem_image, hA, Formalism.L2.Col.mem_XgE]
      constructor
      · rintro ⟨hψ, hs⟩
        obtain ⟨χ, hχ, hχψ⟩ := GlobalTheory.T.absIrrChar_realise_of_primitiveRoot_card σ z hzp ψ hψ
        refine ⟨χ, ⟨hχ, ?_⟩, funext hχψ⟩
        simp only [hχψ]
        exact hs
      · rintro ⟨χ, ⟨hχ, hs⟩, rfl⟩
        exact ⟨GlobalTheory.T.absIrrChar_comp_mem_complexIrrCharSet σ χ hχ, hs⟩
    have hinj : Set.InjOn (fun (χ : Gc X.B px → X.B.LL) g => σ (χ g)) (Formalism.L2.Col.XgE σ e : Set _) :=
      fun χ _ χ' _ h => funext fun g => σ.injective (congrFun h g)
    rw [← hcoeff g]
    conv_rhs => rw [hexp]

    rw [himg, coeff_idemOf, coeff_idemOf, Finset.sum_image hinj, map_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    simp [σ, map_div₀, map_mul, map_natCast]
  · rw [coeff_idemOf]
    have hcl : ∀ y ∈ Subring.closure ({z} : Set X.B.LL), y ∈ X.B.Ks := fun y hy => by
      have : Subring.closure ({z} : Set X.B.LL) ≤ X.B.Ks.toSubfield.toSubring := by
        rw [Subring.closure_le, Set.singleton_subset_iff]
        exact hzK
      exact this hy
    refine IntermediateField.sum_mem _ fun χ hχ => ?_
    have hχ' := Formalism.L2.Col.XgE_irr χ hχ
    exact IntermediateField.mul_mem _ (IntermediateField.div_mem _ (hcl _ (GlobalTheory.T.absIrrChar_mem_closure_primitiveRoot_card z hzp χ hχ' 1))
      (IntermediateField.natCast_mem _ _)) (hcl _ (GlobalTheory.T.absIrrChar_mem_closure_primitiveRoot_card z hzp χ hχ' _))

end Record

end GlobalTheory.Mem.R3.GoodSetExists

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGoodCharacterSetIdempotentCoeffCoefficientStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.exists_goodCharacterSet_idempotent_coeff_coefficientField : ∀ (X : Stages) (px : PreX X.B.toPre) (eR : Gc X.B px ≃* G0g X.toD7.nd), ∃ Xg : Finset (Gc X.B px → X.B.LL), GoodSet X (px := px) eR Xg ∧ ∀ g, (idemOf Xg).coeff g ∈ X.B.Ks := by
  first | exact @GlobalTheory.Mem.R3.GoodSetExists.exists_goodSet_Ks | exact GlobalTheory.Mem.R3.GoodSetExists.exists_goodSet_Ks | (intros; apply GlobalTheory.Mem.R3.GoodSetExists.exists_goodSet_Ks <;> assumption)
end
end
