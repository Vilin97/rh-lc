module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensCut
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.Module.BigOperators
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensEqZeroOfNotMem

section

@[expose] public section

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem algebraMap_mem_LO (c : F) (hc : c ∈ 𝒪[F]) : algebraMap F E c ∈ M.L.O := by
  rw [M.L.O_def]
  have h := isIntegral_algebraMap (R := 𝒪[F]) (A := E) (x := ⟨c, hc⟩)
  rw [IsScalarTower.algebraMap_apply 𝒪[F] F E] at h
  exact h

theorem dens_eq_zero_of_not_mem (H : Loc.HermSp M V) (ϖ : 𝒪[F]) {abelian₂ : Submodule M.L.O V} (hSD : H.IsSelfDual abelian₂)
    {ι : Type} [Fintype ι] (G₀ : Matrix ι ι E) (a b : ι) (hab : G₀ a b ∉ M.L.O) : H.dens ϖ abelian₂ G₀ = 0 := by
  unfold Loc.HermSp.dens
  have hE : IsEmpty {v : ι → V // H.Prim abelian₂ v ∧ ∀ a b, H.h (v b) (v a) - G₀ a b ∈
      Submodule.span M.L.O {algebraMap F E (ϖ : F)}} := by
    refine ⟨fun v => hab ?_⟩
    obtain ⟨hP, hG⟩ := v.2
    have h1 : H.h (v.1 b) (v.1 a) ∈ M.L.O := (hSD.2.2 (v.1 b)).1 (hP.1 b) (v.1 a) (hP.1 a)
    have h2 := hG a b
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h2
    have hϖ : algebraMap F E (ϖ : F) ∈ M.L.O := algebraMap_mem_LO _ ϖ.2
    have h3 : H.h (v.1 b) (v.1 a) - G₀ a b ∈ M.L.O := by
      rw [← hc]
      exact M.L.O.mul_mem c.2 hϖ
    have h4 : G₀ a b = H.h (v.1 b) (v.1 a) - (H.h (v.1 b) (v.1 a) - G₀ a b) := by ring
    rw [h4]
    exact M.L.O.sub_mem h1 h3
  have h0 : Set.range (fun v : {v : ι → V // H.Prim abelian₂ v ∧ ∀ a b, H.h (v b) (v a) - G₀ a b ∈
      Submodule.span M.L.O {algebraMap F E (ϖ : F)}} =>
        fun a => Submodule.Quotient.mk (p := H.smulLat (algebraMap F E (ϖ : F)) abelian₂) (v.1 a)) = ∅ :=
    Set.range_eq_empty _
  rw [h0]
  simp

end Local

def GaPlusIntMM : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (_L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ →
      ∀ (Z : MatZ D) (F' : LFlag (D.sp.Y 0) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        (∀ (p : PlF D) (a b : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)),
          GaPlus M δ p (Tn u) (Tn u') Z a b ∈ (M p).L.O) →
        Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F')

theorem notIntDens_of (h1 : LocSelfDual) (hG : GaPlusIntMM) : NotIntDens := by
  intro D δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI
  by_contra hall
  push_neg at hall
  apply hI
  refine hG D δ M hA L u u' hT F0 what₂ hR Z F' hz hZ hP fun p a b => ?_
  by_contra hab
  exact hall p (dens_eq_zero_of_not_mem (L.H p) (ϖ p) (h1 D δ M hA L p) _ a b hab)

end Formalism.L2.SG.Pf.Cnt
end
end
end

-- Source module: Lemmata.GeneralBFactThirdAltForm.Imports

section

@[expose] public section

namespace Bl.general_b_fact_third_alt_form

theorem goal1 :
  ∀ {E : Type} [inst : CommRing.{0} E] {O : Subring.{0} E} {V : Type} [inst_1 : AddCommGroup.{0} V]
  [inst_2 : Module.{0, 0} E V] {ι : Type} [inst_3 : Fintype.{0} ι] [inst_4 : DecidableEq.{1} ι] (g b : ι → V),
  LinearIndependent.{0, 0, 0} (Subtype.{1} fun (x : E) ↦ Membership.mem.{0, 0} O x) g →
    Eq.{1} (Submodule.span.{0, 0} (Subtype.{1} fun (x : E) ↦ Membership.mem.{0, 0} O x) (Set.range.{0, 1} g))
        (Submodule.span.{0, 0} (Subtype.{1} fun (x : E) ↦ Membership.mem.{0, 0} O x) (Set.range.{0, 1} b)) →
      Exists.{1} fun (Q : Matrix.{0, 0, 0} ι ι (Subtype.{1} fun (x : E) ↦ Membership.mem.{0, 0} O x)) ↦
        Exists.{1} fun (P : Matrix.{0, 0, 0} ι ι (Subtype.{1} fun (x : E) ↦ Membership.mem.{0, 0} O x)) ↦
          And
            (∀ (j : ι),
              Eq.{1} (g j) (Finset.sum.{0, 0} Finset.univ.{0} fun (i : ι) ↦ HSMul.hSMul.{0, 0, 0} (Q i j) (b i)))
            (Eq.{1} (HMul.hMul.{0, 0, 0} P Q) 1) := by
  intro E _ O V _ _ ι _ _ g b hg hspan
  have hgb : ∀ j, g j ∈ Submodule.span O (Set.range b) := fun j => hspan ▸ Submodule.subset_span ⟨j, rfl⟩
  have hbg : ∀ i, b i ∈ Submodule.span O (Set.range g) := fun i => hspan.symm ▸ Submodule.subset_span ⟨i, rfl⟩
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun O).1 (hgb j)
  choose d hd using fun i => (Submodule.mem_span_range_iff_exists_fun O).1 (hbg i)
  have key : ∀ j, ∑ k, ((Matrix.of fun k i => d i k) * (Matrix.of fun i j => c j i)) k j • g k = g j := by
    intro j
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_smul]
    conv_rhs => rw [← hc j]
    simp only [← hd, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  refine ⟨Matrix.of fun i j => c j i, Matrix.of fun k i => d i k, fun j => (hc j).symm, ?_⟩
  ext k j
  have hz := Fintype.linearIndependent_iff.1 hg
    (fun k => ((Matrix.of fun k i => d i k) * (Matrix.of fun i j => c j i)) k j - (1 : Matrix ι ι O) k j) ?_ k
  · exact congrArg Subtype.val (sub_eq_zero.1 hz)
  · simp only [sub_smul, Finset.sum_sub_distrib, key, Matrix.one_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]

end Bl.general_b_fact_third_alt_form
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NotIntDensOfSteps

section

@[expose] public section

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt.DualityBasisChange

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Herm

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)

theorem h_zero_left (y : V) : H.h 0 y = 0 := by
  have := H.h_smul_left 0 0 y
  simpa using this

theorem h_smul_right (c : E) (x y : V) : H.h x (c • y) = M.L.cj c * H.h x y := by
  rw [H.h_herm (c • y) x, H.h_smul_left, map_mul, ← H.h_herm y x]

theorem h_sum_left {ι : Type} (s : Finset ι) (x : ι → V) (y : V) :
    H.h (∑ i ∈ s, x i) y = ∑ i ∈ s, H.h (x i) y := by
  induction s using Finset.induction_on with
  | empty => simp [h_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, ih]

theorem h_sum_right {ι : Type} (s : Finset ι) (x : ι → V) (y : V) :
    H.h y (∑ i ∈ s, x i) = ∑ i ∈ s, H.h y (x i) := by

  rw [H.h_herm (∑ i ∈ s, x i) y, h_sum_left, map_sum]
  exact Finset.sum_congr rfl fun i _ => (H.h_herm (x i) y).symm

theorem gram_comb {ι : Type} [Fintype ι] (v : ι → V) (A : Matrix ι ι E) :
    (Matrix.of fun a b => H.h (∑ d, A d b • v d) (∑ c, A c a • v c)) =
      (A.map M.L.cj).transpose * (Matrix.of fun a b => H.h (v b) (v a)) * A := by
  ext a b
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, h_sum_left,
    h_sum_right, H.h_smul_left, h_smul_right, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

end Herm

section Basis

variable {E : Type} [CommRing E] {O : Subring E} {V : Type} [AddCommGroup V] [Module E V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem change_basis (g b : ι → V) (hg : LinearIndependent O g)
    (hs : Submodule.span O (Set.range g) = Submodule.span O (Set.range b)) :
    ∃ Q P : Matrix ι ι O, (∀ j, g j = ∑ i, Q i j • b i) ∧ P * Q = 1 := by
  first | exact Bl.general_b_fact_third_alt_form.goal1 .. | (apply Bl.general_b_fact_third_alt_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third_alt_form.goal1 <;> assumption)

end Basis

section Glob

variable {D : Formalism.BasicNotions.D7}

theorem flag_hT {T : D.host.E} (F : FlagG (VS D) D.R.rS T) (a b : Fin (D.R.rS + 1)) :
    (VS D).hT (F.fvec a) (F.fvec b) = if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then -T else 0 := by
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => simp [FlagG.fvec, F.z_norm]
    | cast b =>
      simp only [FlagG.fvec, Fin.snoc_last, Fin.snoc_castSucc]
      rw [if_neg (by simp [Fin.castSucc_ne_last])]
      rw [← (VS D).herm.eq (F.e b) F.z, F.z_orth b, map_zero]
  | cast a =>
    simp only [FlagG.fvec, Fin.snoc_castSucc]
    rw [if_neg (by simp [Fin.castSucc_ne_last])]
    induction b using Fin.lastCases with
    | last => simp only [Fin.snoc_last]; exact F.z_orth a
    | cast b => simp only [Fin.snoc_castSucc]; exact F.e_iso a b

def vfam {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') :
    Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → (VS D).V :=
  Sum.elim F0.fvec F'.fl.fvec

theorem ga_eq {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') :
    Ga T T' (ZhatL (lf D F0) F') = Matrix.of fun a b => brS (VS D) (vfam F0 F' b) (vfam F0 F' a) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · simp only [Ga, Matrix.fromBlocks_apply₁₁, Matrix.of_apply, vfam, Sum.elim_inl, brS]
    rw [flag_hT]
  · simp [Ga, vfam, brS, ZhatL, Zhat]
  · simp only [Ga, Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply, Matrix.of_apply, vfam, Sum.elim_inl,
      Sum.elim_inr, brS, ZhatL, Zhat]
    rw [← (VS D).herm.eq (F0.fvec b) (F'.fl.fvec a)]
    rfl
  · simp only [Ga, Matrix.fromBlocks_apply₂₂, Matrix.of_apply, vfam, Sum.elim_inr, brS]
    rw [flag_hT]

variable {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}

def g0 (L : LocSp D M) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) {T T' : D.host.E}
    (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → L.V p :=
  fun a => phi δ p a • L.bc p (vfam F0 F' a)

theorem gaLoc_eq (L : LocSp D M) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) {T T' : D.host.E}
    (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') :
    GaLoc M δ p T T' (ZhatL (lf D F0) F') = Matrix.of fun a b => (L.H p).h (g0 L δ p F0 F' b) (g0 L δ p F0 F' a) := by
  ext a b
  simp only [GaLoc, Matrix.of_apply, g0, (L.H p).h_smul_left, h_smul_right, L.bc_form, ga_eq]
  ring

def amat (p : PlF D) (g : Loc.SplitG (M p).L) :
    Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
  Matrix.fromBlocks 1 (-(algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹)) •
      (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep)) 0
    (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹) •
      (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep))

def locFam (L : LocSp D M) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) {T T' : D.host.E}
    (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → L.V p :=
  match (M p).split with
  | none => g0 L δ p F0 F'
  | some g => fun b => ∑ d, amat p g d b • g0 L δ p F0 F' d

theorem gaPlus_eq_gram (L : LocSp D M) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) {T T' : D.host.E}
    (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') :
    GaPlus M δ p T T' (ZhatL (lf D F0) F') =
      Matrix.of fun a b => (L.H p).h (locFam L δ p F0 F' b) (locFam L δ p F0 F' a) := by
  unfold GaPlus locFam
  cases hs : (M p).split with
  | none => simp only; exact gaLoc_eq L δ p F0 F'
  | some g =>
    simp only
    rw [gram_comb, gaLoc_eq L δ p F0 F']
    rfl

end Glob

section Cut

def FrameBasisL : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ F' : LFlag (D.sp.Y 0) D.R.rS (Tn u'), F'.zt = F'.fl.z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') (ZhatL (lf D F0) F')) → ∀ p : PlF D,
        LinearIndependent (M p).L.O (locFam L δ p F0 F') ∧
          Submodule.span (M p).L.O (Set.range (locFam L δ p F0 F')) = lattice₂ L p (MMof D F0 F')

def JordanL : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ F' : LFlag (D.sp.Y 0) D.R.rS (Tn u'), F'.zt = F'.fl.z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') (ZhatL (lf D F0) F')) →
        Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F') →
        ∀ (p : PlF D) (ϖ : 𝒪[(D.s.atP p).Fp]), Irreducible ϖ →
        ∃ (b : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → L.V p)
          (a : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → 𝒪[(D.s.atP p).Fp]),
          Submodule.span (M p).L.O (Set.range b) = lattice₂ L p (MMof D F0 F') ∧
          (∀ i j, i ≠ j → (L.H p).h (b j) (b i) = 0) ∧
          (∀ i, (L.H p).h (b i) (b i) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (a i : (D.s.atP p).Fp)) ∧
          (Finset.univ.filter fun i => ϖ ∣ a i).card = cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal

theorem gaPlusDiag_of (hF : FrameBasisL) (hJ : JordanL) : GaPlusDiag := by
  intro D δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI p
  subst hZ
  obtain ⟨hli, hsp⟩ := hF D δ M hA L u u' hT F0 what₂ hR F' hz hP p
  obtain ⟨b, a, hbs, horth, hdiag, hcnt⟩ := hJ D δ M hA L u u' hT F0 what₂ hR F' hz hP hI p (ϖ p) (hϖ p)
  obtain ⟨Q, P, hQ, hPQ⟩ := change_basis (O := (M p).L.O) (locFam L δ p F0 F') b hli (hsp.trans hbs.symm)
  have hdet : (Q.map (M p).L.O.subtype).det = ((Q.det : (M p).L.O) : (D.s.atP p).Ep) :=
    (RingHom.map_det (M p).L.O.subtype Q).symm
  refine ⟨Q.map (M p).L.O.subtype, a, fun i j => (Q i j).2, ⟨((P.det : (M p).L.O) : (D.s.atP p).Ep), P.det.2, ?_⟩, ?_, hcnt⟩
  · rw [hdet]
    have h1 : P.det * Q.det = 1 := by rw [← Matrix.det_mul, hPQ, Matrix.det_one]
    have h2 : ((Q.det * P.det : (M p).L.O) : (D.s.atP p).Ep) = 1 := by rw [mul_comm, h1]; rfl
    simpa using h2
  · rw [gaPlus_eq_gram L δ p F0 F']
    have hg : locFam L δ p F0 F' = fun j => ∑ i, (Q.map (M p).L.O.subtype) i j • b i := by
      funext j
      rw [hQ j]
      rfl
    rw [hg, gram_comb]
    congr 2
    ext i j
    simp only [Matrix.of_apply, Matrix.diagonal_apply]
    split_ifs with hij
    · subst hij; exact hdiag i
    · exact horth i j hij

end Cut

section Int

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem cj_mem_O (x : E) (hx : x ∈ M.L.O) : M.L.cj x ∈ M.L.O := by
  rw [M.L.O_def] at hx ⊢
  exact hx.map (M.L.cj.toAlgHom.restrictScalars 𝒪[F])

theorem h_int_span (H : Loc.HermSp M V) {ι : Type} (g : ι → V) (hG : ∀ a b, H.h (g b) (g a) ∈ M.L.O)
    {x y : V} (hx : x ∈ Submodule.span M.L.O (Set.range g)) (hy : y ∈ Submodule.span M.L.O (Set.range g)) :
    H.h x y ∈ M.L.O := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨a, rfl⟩ := hy; exact hG a b
    | zero => have := h_smul_right H 0 (g b) 0; rw [zero_smul, map_zero, zero_mul] at this; rw [this]; exact M.L.O.zero_mem
    | add y y' _ _ ih ih' =>
      rw [H.h_herm (y + y') (g b), H.h_add_left, map_add (f := _), ← H.h_herm y (g b), ← H.h_herm y' (g b)]
      exact M.L.O.add_mem ih ih'
    | smul c y _ ih =>
      rw [Subring.smul_def, h_smul_right]
      exact M.L.O.mul_mem (cj_mem_O _ c.2) ih
  | zero => rw [h_zero_left]; exact M.L.O.zero_mem
  | add x x' _ _ ih ih' => rw [H.h_add_left]; exact M.L.O.add_mem ih ih'
  | smul c x _ ih => rw [Subring.smul_def, H.h_smul_left]; exact M.L.O.mul_mem c.2 ih

end Int

section S3

def LocGlobIntE : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (x : D.host.E), (∀ p : PlF D, (D.s.atP p).ιE x ∈ (D.s.atP p).O) →
    x ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)

theorem gaPlusIntMM_of (hF : FrameBasisL) (hLG : LocGlobIntE) : GaPlusIntMM := by
  intro D δ M hA L u u' hT F0 what₂ hR Z F' hz hZ hP hInt
  subst hZ
  intro x hx y hy
  refine hLG D _ fun p => ?_
  obtain ⟨-, hsp⟩ := hF D δ M hA L u u' hT F0 what₂ hR F' hz hP p
  have hmem : ∀ v ∈ MMof D F0 F', L.bc p v ∈ Submodule.span (M p).L.O (Set.range (locFam L δ p F0 F')) :=
    fun v hv => hsp ▸ Submodule.subset_span ⟨v, hv, rfl⟩
  have e : (D.s.atP p).ιE ((VS D).hT x y) = (L.H p).h (L.bc p y) (L.bc p x) := (L.bc_form p y x).symm
  rw [e, ← (hA p).2.2.2.1]
  refine h_int_span (L.H p) (locFam L δ p F0 F') (fun a b => ?_) (hmem y hy) (hmem x hx)
  have := hInt p a b
  rw [gaPlus_eq_gram L δ p F0 F'] at this
  exact this

theorem notIntDens_of_steps (h1 : LocSelfDual) (hF : FrameBasisL) (hLG : LocGlobIntE) : NotIntDens :=
  notIntDens_of h1 (gaPlusIntMM_of hF hLG)

end S3

end Formalism.L2.SG.Pf.Cnt.DualityBasisChange
end
end
end
