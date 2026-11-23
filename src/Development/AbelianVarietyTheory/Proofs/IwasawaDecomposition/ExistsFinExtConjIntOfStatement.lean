module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingEquivFinExtIntegersPadicIntOf
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.RingTheory.Localization.Module
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsConjIntegral

section

@[expose] public section

noncomputable section
open Matrix Module

namespace GlobalTheory.StableLattice

theorem lift_of_integral {O K : Type} [CommRing O] [Field K] [Algebra O K]
    (hinj : Function.Injective (algebraMap O K)) {Γ : Type} [Group Γ] {n : ℕ}
    (φ : Γ →* GL (Fin n) K)
    (h : ∀ g i j, ((φ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ (algebraMap O K).range) :
    ∃ r : Γ →* GL (Fin n) O, ∀ g, Matrix.GeneralLinearGroup.map (algebraMap O K) (r g) = φ g := by
  classical
  let f : O →+* K := algebraMap O K
  have h' : ∀ g i j, ∃ x : O, f x = ((φ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j :=
    fun g i j => RingHom.mem_range.1 (h g i j)
  choose c hc using h'
  let M : Γ → Matrix (Fin n) (Fin n) O := fun g => Matrix.of fun i j => c g i j
  have hmi : Function.Injective (f.mapMatrix : Matrix (Fin n) (Fin n) O →+* Matrix (Fin n) (Fin n) K) :=
    fun A B hAB => Matrix.ext fun i j => hinj (by simpa using congrFun (congrFun hAB i) j)
  have hM : ∀ g, f.mapMatrix (M g) = ((φ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    fun g => Matrix.ext fun i j => hc g i j
  let ρ : Γ →* GL (Fin n) O :=
    { toFun := fun g => ⟨M g, M g⁻¹,
        hmi (by rw [map_mul, hM, hM, map_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]),
        hmi (by rw [map_mul, hM, hM, map_one, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one])⟩
      map_one' := Units.ext (hmi (by rw [hM, map_one, Units.val_one, Units.val_one, map_one]))
      map_mul' := fun g h => Units.ext (hmi (by
        show f.mapMatrix (M (g * h)) = f.mapMatrix (M g * M h)
        rw [map_mul, hM, hM, hM, map_mul, Units.val_mul])) }
  exact ⟨ρ, fun g => Units.ext (hM g)⟩

theorem exists_conj_integral {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    {Γ : Type} [Group Γ] {n : ℕ} (σ : Γ →* GL (Fin n) (FractionRing O)) (T : Finset Γ)
    (hT : ∀ x : Γ, ∃ t ∈ T, ∀ i j, ((σ (t⁻¹ * x) : GL (Fin n) (FractionRing O)) :
      Matrix (Fin n) (Fin n) (FractionRing O)) i j ∈ (algebraMap O (FractionRing O)).range) :
    ∃ P : GL (Fin n) (FractionRing O), ∀ g i j,
      ((P⁻¹ * σ g * P : GL (Fin n) (FractionRing O)) : Matrix (Fin n) (Fin n) (FractionRing O)) i j
        ∈ (algebraMap O (FractionRing O)).range := by
  classical
  let K := FractionRing O
  let S : Γ → Matrix (Fin n) (Fin n) K := fun g => ((σ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  let gen : T × Fin n → (Fin n → K) := fun p => S p.1 *ᵥ Pi.single p.2 1
  let M : Submodule O (Fin n → K) := Submodule.span O (Set.range gen)
  have hA : ∀ t (ht : t ∈ T), ∀ w : Fin n → K, (∀ k, w k ∈ (algebraMap O K).range) → S t *ᵥ w ∈ M := by
    intro t ht w hw
    choose u hu using fun k => RingHom.mem_range.1 (hw k)
    have : S t *ᵥ w = ∑ k, u k • gen (⟨t, ht⟩, k) := by
      ext a
      simp only [gen, Matrix.mulVec_single_one]
      simp only [Finset.sum_apply, Pi.smul_apply, Matrix.transpose_apply, Matrix.col_apply, Algebra.smul_def,
        Matrix.mulVec, dotProduct, ← hu]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have he : ∀ i, (Pi.single i 1 : Fin n → K) ∈ M := by
    intro i
    obtain ⟨t, ht, hU⟩ := hT 1
    have h1 : S t * S (t⁻¹ * 1) = 1 := by
      simp only [S]
      rw [← Units.val_mul, ← map_mul, mul_one, mul_inv_cancel, map_one, Units.val_one]
    have : (Pi.single i 1 : Fin n → K) = S t *ᵥ (S (t⁻¹ * 1) *ᵥ Pi.single i 1) := by
      rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    rw [this]
    refine hA t ht _ fun k => ?_
    rw [Matrix.mulVec_single_one]
    exact hU k i
  have hstab : ∀ g, ∀ x ∈ M, S g *ᵥ x ∈ M := by
    intro g
    let A : (Fin n → K) →ₗ[O] (Fin n → K) := (Matrix.toLin' (S g)).restrictScalars O
    have hle : M.map A ≤ M := by
      rw [Submodule.map_span_le]
      rintro _ ⟨⟨⟨t, ht⟩, i⟩, rfl⟩
      obtain ⟨t', ht', hU⟩ := hT (g * t)
      have h1 : S g * S t = S t' * S (t'⁻¹ * (g * t)) := by
        simp only [S]
        rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, mul_inv_cancel_left]
      show S g *ᵥ (S t *ᵥ Pi.single i 1) ∈ M
      rw [Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec]
      refine hA t' ht' _ fun k => ?_
      rw [Matrix.mulVec_single_one]
      exact hU k i
    intro x hx
    exact hle ⟨x, hx, rfl⟩
  haveI : Module.Finite O M := Module.Finite.span_of_finite (R := O) (Set.finite_range gen)
  haveI : Module.Free O M := Module.free_of_finite_type_torsion_free'
  let ι := Module.Free.ChooseBasisIndex O M
  let b : Basis ι O M := Module.Free.chooseBasis O M
  let v : ι → (Fin n → K) := fun i => (b i : Fin n → K)
  have hcoord : ∀ x (hx : x ∈ M), x = ∑ i, algebraMap O K (b.repr ⟨x, hx⟩ i) • v i := by
    intro x hx
    have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at this
    simp only [algebraMap_smul, v]
    exact this.symm
  have hli : LinearIndependent K v :=
    (LinearIndependent.iff_fractionRing O K).1 (b.linearIndependent.map' M.subtype M.ker_subtype)
  have hsp : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← (Pi.basisFun K (Fin n)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [Pi.basisFun_apply, hcoord _ (he i)]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let bK : Basis ι K (Fin n → K) := Basis.mk hli hsp
  have hrep : ∀ x (hx : x ∈ M) k, bK.repr x k = algebraMap O K (b.repr ⟨x, hx⟩ k) := by
    intro x hx k
    have h1 : x = bK.equivFun.symm (fun i => algebraMap O K (b.repr ⟨x, hx⟩ i)) := by
      rw [Basis.equivFun_symm_apply]
      simp only [bK, Basis.coe_mk]
      exact hcoord x hx
    rw [← Basis.equivFun_apply]
    conv_lhs => rw [h1]
    rw [LinearEquiv.apply_symm_apply]
  have hcard : Fintype.card ι = n :=
    (Module.finrank_eq_card_basis bK).symm.trans (Module.finrank_fin_fun K)
  let e : ι ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let bK' : Basis (Fin n) K (Fin n → K) := bK.reindex e
  let E := Pi.basisFun K (Fin n)
  let Pu : GL (Fin n) K := ⟨E.toMatrix bK', bK'.toMatrix E, E.toMatrix_mul_toMatrix_flip bK',
    bK'.toMatrix_mul_toMatrix_flip E⟩
  refine ⟨Pu, fun g i j => ?_⟩
  have hmat : ((Pu⁻¹ * σ g * Pu : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      LinearMap.toMatrix bK' bK' (Matrix.toLin' (S g)) := by
    rw [← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (b := bK') (c := bK') (b' := E) (c' := E),
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
    simp only [Units.val_mul]
    rfl
  have hmem : S g *ᵥ bK' j ∈ M := by
    refine hstab g _ ?_
    simp only [bK', Basis.reindex_apply, bK, Basis.coe_mk, v]
    exact (b _).2
  rw [hmat, LinearMap.toMatrix_apply, Matrix.toLin'_apply, Basis.repr_reindex_apply, hrep _ hmem]
  exact ⟨_, rfl⟩

end GlobalTheory.StableLattice
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinExtConjIntOf

section

@[expose] public section

open Formalism.BasicNotions

noncomputable section

namespace GlobalTheory.IntegralConjFinExt

open Matrix

theorem norm_sum_le_one (l : ℕ) [Fact l.Prime] {ι : Type} (s : Finset ι) (f : ι → PadicAlgCl l)
    (h : ∀ i ∈ s, ‖f i‖ ≤ 1) : ‖∑ i ∈ s, f i‖ ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (PadicAlgCl.isNonarchimedean l _ _).trans
      (max_le (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem norm_one_apply_le (l : ℕ) [Fact l.Prime] (a : ℕ) (i j : Fin a) :
    ‖(1 : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j‖ ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp

def intSubgroup (l : ℕ) [Fact l.Prime] {Γ : Type} [Group Γ] {a : ℕ}
    (ρ : Γ →* GL (Fin a) (PadicAlgCl l)) : Subgroup Γ where
  carrier := {g | ∀ i j, ‖(ρ g : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j‖ ≤ 1 ∧
    ‖(ρ g⁻¹ : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j‖ ≤ 1}
  one_mem' := fun i j => by
    simp only [inv_one, map_one, Units.val_one]
    exact ⟨norm_one_apply_le l a i j, norm_one_apply_le l a i j⟩
  mul_mem' := fun {g h} hg hh i j => by
    rw [_root_.mul_inv_rev, map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_apply,
      Matrix.mul_apply]
    exact ⟨norm_sum_le_one l _ _ fun k _ => by
        rw [norm_mul]; exact mul_le_one₀ (hg i k).1 (norm_nonneg _) (hh k j).1,
      norm_sum_le_one l _ _ fun k _ => by
        rw [norm_mul]; exact mul_le_one₀ (hh i k).2 (norm_nonneg _) (hg k j).2⟩
  inv_mem' := fun {g} hg i j => ⟨(hg i j).2, by rw [inv_inv]; exact (hg i j).1⟩

theorem isOpen_intSubgroup (l : ℕ) [Fact l.Prime] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) (PadicAlgCl l))
    (hρ : Continuous (fun g => ((ρ g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)))) :
    IsOpen (intSubgroup l ρ : Set Γ) := by
  let V : Set Γ := ⋂ i, ⋂ j,
    ({g | ‖(ρ g : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j - (1 : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j‖ < 1} ∩
     {g | ‖(ρ g⁻¹ : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j - (1 : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j‖ < 1})
  have hVo : IsOpen V :=
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (isOpen_lt (((hρ.matrix_elem i j).sub continuous_const).norm) continuous_const).inter
        (isOpen_lt ((((hρ.matrix_elem i j).comp continuous_inv).sub continuous_const).norm) continuous_const)
  have hV1 : (1 : Γ) ∈ V := by
    simp only [V, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq, inv_one, map_one, Units.val_one,
      sub_self, norm_zero, zero_lt_one, and_self, implies_true]
  have hle : ∀ x y : PadicAlgCl l, ‖x - y‖ < 1 → ‖y‖ ≤ 1 → ‖x‖ ≤ 1 := fun x y hxy hy => by
    have := PadicAlgCl.isNonarchimedean l (x - y) y
    rw [sub_add_cancel] at this
    exact this.trans (max_le hxy.le hy)
  have hVU : V ⊆ (intSubgroup l ρ : Set Γ) := fun g hg i j => by
    simp only [V, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq] at hg
    exact ⟨hle _ _ (hg i j).1 (norm_one_apply_le l a i j), hle _ _ (hg i j).2 (norm_one_apply_le l a i j)⟩
  exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hVo.mem_nhds hV1) hVU)



theorem exists_finExt_conj_intOf : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] (a : ℕ) (ρ : Γ →* GL (Fin a) (PadicAlgCl l)), Continuous (fun g => ((ρ g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) → ∃ (L : Loc.FinExt l) (P : GL (Fin a) (PadicAlgCl l)), ∀ g i k, ((P⁻¹ * ρ g * P : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i k ∈ Formalism.L2.TwC.intOf l L.1 := by
  intro l _ Γ _ _ _ _ _ a ρ hρ
  letI : DecidableEq Γ := Classical.decEq Γ
  obtain ⟨L, -, hL⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l Γ a ρ hρ ⟨⊥, inferInstance⟩
  haveI : FiniteDimensional ℚ_[l] L.1 := L.2
  let U := intSubgroup l ρ
  haveI : Finite (Γ ⧸ U) := Subgroup.quotient_finite_of_isOpen _ (isOpen_intSubgroup l ρ hρ)
  haveI : Fintype (Γ ⧸ U) := Fintype.ofFinite _
  let T : Finset Γ := Finset.univ.image (fun q : Γ ⧸ U => q.out)
  have hTU : ∀ x : Γ, ∃ t ∈ T, t⁻¹ * x ∈ U := by
    intro x
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul U x
    refine ⟨(x : Γ ⧸ U).out, Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
    rw [hh, _root_.mul_inv_rev, inv_mul_cancel_right]
    exact U.inv_mem h.2
  obtain ⟨r, hr⟩ := GlobalTheory.StableLattice.lift_of_integral (O := L.1) (K := PadicAlgCl l)
    Subtype.val_injective ρ (fun g i j => ⟨⟨_, hL g i j⟩, rfl⟩)
  have hre : ∀ g i j, (((r g : GL (Fin a) L.1) : Matrix (Fin a) (Fin a) L.1) i j : PadicAlgCl l) =
      ((ρ g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j := by
    intro g i j
    rw [← hr g, Matrix.GeneralLinearGroup.map_apply]
    rfl
  let e : L.1 ≃ₐ[Loc.OL L] FractionRing (Loc.OL L) :=
    IsLocalization.algEquiv (nonZeroDivisors (Loc.OL L)) L.1 (FractionRing (Loc.OL L))
  let σ : Γ →* GL (Fin a) (FractionRing (Loc.OL L)) :=
    (Matrix.GeneralLinearGroup.map e.toRingEquiv.toRingHom).comp r
  have hσ : ∀ x : Γ, ∃ t ∈ T, ∀ i j, (σ (t⁻¹ * x)).val i j ∈
        (algebraMap (Loc.OL L) (FractionRing (Loc.OL L))).range := by
    intro x
    obtain ⟨t, ht, hu⟩ := hTU x
    refine ⟨t, ht, fun i j => ?_⟩
    have hmem : ((r (t⁻¹ * x) : GL (Fin a) L.1) : Matrix (Fin a) (Fin a) L.1) i j ∈ Loc.OL L := by
      rw [Formalism.BasicNotions.Examples₂.LB.mem_OL, hre]
      exact (hu i j).1
    refine ⟨⟨_, hmem⟩, ?_⟩
    simp only [σ, MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map_apply]
    rw [← e.commutes]
    rfl
  obtain ⟨P', hP'⟩ := GlobalTheory.StableLattice.exists_conj_integral σ T hσ
  let φ : FractionRing (Loc.OL L) →+* PadicAlgCl l :=
    (algebraMap L.1 (PadicAlgCl l)).comp e.symm.toRingEquiv.toRingHom
  have hφσ : ∀ g, Matrix.GeneralLinearGroup.map φ (σ g) = ρ g := by
    intro g
    rw [← hr g]
    ext i j
    simp only [σ, φ, MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map_apply, RingHom.comp_apply]
    congr 1
    exact e.symm_apply_apply _
  refine ⟨L, Matrix.GeneralLinearGroup.map φ P', fun g i k => ?_⟩
  have h1 : (Matrix.GeneralLinearGroup.map φ P')⁻¹ * ρ g * Matrix.GeneralLinearGroup.map φ P' =
      Matrix.GeneralLinearGroup.map φ (P'⁻¹ * σ g * P') := by
    rw [MonoidHom.map_mul (Matrix.GeneralLinearGroup.map φ), MonoidHom.map_mul (Matrix.GeneralLinearGroup.map φ),
      MonoidHom.map_inv (Matrix.GeneralLinearGroup.map φ), hφσ]
  suffices key : ((Matrix.GeneralLinearGroup.map φ (P'⁻¹ * σ g * P') : GL (Fin a) (PadicAlgCl l)) :
      Matrix (Fin a) (Fin a) (PadicAlgCl l)) i k ∈ Formalism.L2.TwC.intOf l L.1 by
    rw [← h1] at key
    exact key
  obtain ⟨z, hz⟩ := hP' g i k
  rw [Matrix.GeneralLinearGroup.map_apply, ← hz]
  have h2 : φ (algebraMap (Loc.OL L) (FractionRing (Loc.OL L)) z) = (((z : L.1)) : PadicAlgCl l) := by
    simp only [φ, RingHom.comp_apply]
    rw [← e.commutes z]
    show algebraMap L.1 (PadicAlgCl l) (e.symm (e _)) = _
    rw [e.symm_apply_apply]
    rfl
  rw [h2, GlobalTheory.IntOfFinExt.mem_intOf_iff]
  exact ⟨(z : L.1).2, (Formalism.BasicNotions.Examples₂.LB.mem_OL L _).1 z.2⟩

end GlobalTheory.IntegralConjFinExt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinExtConjIntOfStatement

section

@[expose] public section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.exists_finExt_conj_entries_mem_intOf : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] (a : ℕ) (ρ : Γ →* GL (Fin a) (PadicAlgCl l)), Continuous (fun g => ((ρ g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) → ∃ (L : Loc.FinExt l) (P : GL (Fin a) (PadicAlgCl l)), ∀ g i k, ((P⁻¹ * ρ g * P : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i k ∈ Formalism.L2.TwC.intOf l L.1 := by
  first | exact @GlobalTheory.IntegralConjFinExt.exists_finExt_conj_intOf | exact GlobalTheory.IntegralConjFinExt.exists_finExt_conj_intOf | (intros; apply GlobalTheory.IntegralConjFinExt.exists_finExt_conj_intOf <;> assumption)
end
end
