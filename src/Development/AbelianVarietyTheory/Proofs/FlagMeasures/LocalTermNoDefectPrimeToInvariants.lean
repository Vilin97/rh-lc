module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameStandardLatticeHermitianIntegral
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramDetJoinedFamilyEqPmNormDifferenceStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFamilyUnitriangularChangeOfMemFrameUnipotentStatement
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Mathlib.Tactic.ReduceModChar
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameStandardLatticeHermitianIntegralStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

theorem _root_.GlobalTheory.T.frameStandardLattice_hermitian_integral : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f)) (hL : Fr.IsInner L), ∀ x ∈ Fr.LamStd L, ∀ y ∈ Fr.LamStd L, H.h x y ∈ M.L.O := by
  first | exact @GlobalTheory.LocStdInt.lamStd_integral | exact GlobalTheory.LocStdInt.lamStd_integral | (intros; apply GlobalTheory.LocStdInt.lamStd_integral <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairingLeadingMinorEqOfUnitriangularChanges

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

namespace GlobalTheory.MinorTri

theorem sum_eq_sum_castLE {E : Type} [AddCommMonoid E] {n l : ℕ} (hl : l ≤ n) (φ : Fin n → E)
    (h : ∀ c : Fin n, l ≤ c.val → φ c = 0) : ∑ c, φ c = ∑ c : Fin l, φ (Fin.castLE hl c) := by
  refine (Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl)
    (fun c : Fin l => φ (Fin.castLE hl c)) φ ?_ (fun _ => rfl)).symm
  intro c hc
  apply h
  by_contra hlt
  exact hc ⟨⟨c.val, by omega⟩, Fin.ext rfl⟩

theorem det_block_uni {E : Type} [CommRing E] {n l : ℕ} (hl : l ≤ n) (A : Matrix (Fin n) (Fin n) E)
    (hA : Uni A) : (A.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
  obtain ⟨h0, h1⟩ := hA
  rw [Matrix.det_of_upperTriangular]
  · simp [Matrix.submatrix_apply, h1]
  · intro i j hij
    simp only [Matrix.submatrix_apply]
    apply h0
    rw [Fin.lt_def, Fin.coe_castLE, Fin.coe_castLE]
    exact hij

theorem block_mul_uni {E : Type} [CommRing E] {n l : ℕ} (hl : l ≤ n) (Z A : Matrix (Fin n) (Fin n) E)
    (hA : Uni A) : (Z * A).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      Z.submatrix (Fin.castLE hl) (Fin.castLE hl) * A.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
  obtain ⟨h0, -⟩ := hA
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [sum_eq_sum_castLE hl _ ?_]
  intro c hc
  rw [h0 c (Fin.castLE hl j) (by rw [Fin.lt_def, Fin.coe_castLE]; exact lt_of_lt_of_le j.isLt hc), mul_zero]

theorem det_block_mul_uni {E : Type} [CommRing E] {n l : ℕ} (hl : l ≤ n) (Z A : Matrix (Fin n) (Fin n) E)
    (hA : Uni A) : ((Z * A).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  rw [block_mul_uni hl Z A hA, Matrix.det_mul, det_block_uni hl A hA, mul_one]

theorem det_block_transpose_uni_mul {E : Type} [CommRing E] {n l : ℕ} (hl : l ≤ n)
    (Z A : Matrix (Fin n) (Fin n) E) (hA : Uni A) :
    ((A.transpose * Z).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  have e : A.transpose * Z = (Z.transpose * A).transpose := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [e, ← Matrix.transpose_submatrix, Matrix.det_transpose, det_block_mul_uni hl _ _ hA,
    ← Matrix.transpose_submatrix, Matrix.det_transpose]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem h_sum_left (H : HermSp M V) {ι : Type} (s : Finset ι) (c : ι → E) (v : ι → V) (y : V) :
    H.h (∑ i ∈ s, c i • v i) y = ∑ i ∈ s, c i * H.h (v i) y := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h0 := H.h_smul_left 0 0 y
    simpa using h0
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]

theorem h_sum_right (H : HermSp M V) {ι : Type} (s : Finset ι) (c : ι → E) (v : ι → V) (x : V) :
    H.h x (∑ i ∈ s, c i • v i) = ∑ i ∈ s, M.L.cj (c i) * H.h x (v i) := by

  rw [H.h_herm (∑ i ∈ s, c i • v i) x, h_sum_left H, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← H.h_herm (v i) x]

theorem Dl_eq_of_tri (H : HermSp M V) {r : ℕ} (f f' g g' : Fin (r + 1) → V) (hg : Tri E f g)
    (hg' : Tri E f' g') (l : ℕ) : H.Dl g g' l = H.Dl f f' l := by
  obtain ⟨A, hA, hAc⟩ := hg
  obtain ⟨A', hA', hA'c⟩ := hg'
  obtain ⟨hA0, hA1⟩ := hA
  have hB : Uni (A.map M.L.cj) := by
    unfold Uni
    exact ⟨fun a b hab => by simp [Matrix.map_apply, hA0 a b hab], fun a => by simp [Matrix.map_apply, hA1 a]⟩
  have hZ : H.Zhat g g' = (A.map M.L.cj).transpose * H.Zhat f f' * A' := by
    ext a b
    simp only [HermSp.Zhat, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    rw [hAc a, hA'c b, h_sum_left H]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [h_sum_right H, mul_comm]
  unfold HermSp.Dl
  split_ifs with hl
  · rw [hZ, det_block_mul_uni hl _ A' hA', det_block_transpose_uni_mul hl _ _ hB]
  · rfl

end GlobalTheory.MinorTri
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairingLeadingMinorEqOfUnitriangularChangesStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

theorem _root_.GlobalTheory.T.pairingLeadingMinor_eq_of_unitriangular_changes : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ} (f f' g g' : Fin (r + 1) → V) (hg : Tri E f g) (hg' : Tri E f' g') (l : ℕ), H.Dl g g' l = H.Dl f f' l := by
  first | exact @GlobalTheory.MinorTri.Dl_eq_of_tri | exact GlobalTheory.MinorTri.Dl_eq_of_tri | (intros; apply GlobalTheory.MinorTri.Dl_eq_of_tri <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.SaturatedSpanOfGramDetIsUnitIntegralLattice

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

namespace GlobalTheory

theorem satur_of_gram_det_unit : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {ι : Type} [Fintype ι] [DecidableEq ι] (Λ : Submodule M.L.O V) (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, H.h x y ∈ M.L.O) (m : ι → V) (hm : ∀ i, m i ∈ Λ) (hdet : IsUnitO M (H.gram m).det), ∀ v ∈ Λ, v ∈ Submodule.span E (Set.range m) → v ∈ Submodule.span M.L.O (Set.range m) := by
  intro F _ _ _ E _ _ _ _ M V _ _ H ι _ _ Λ hΛ m hm hdet v hv hvE
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hvE

  have hG : ∀ a b, H.gram m a b ∈ M.L.O := fun a b => hΛ _ (hm b) _ (hm a)
  let G' : Matrix ι ι M.L.O := Matrix.of fun a b => ⟨H.gram m a b, hG a b⟩
  have hmap : M.L.O.subtype.mapMatrix G' = H.gram m := by
    ext a b
    rfl
  have hadj : ∀ a b, (H.gram m).adjugate a b ∈ M.L.O := by
    intro a b
    rw [← hmap, ← RingHom.map_adjugate]
    exact (G'.adjugate a b).2

  have hpair : ∀ a, (Matrix.mulVec (H.gram m) c) a ∈ M.L.O := by
    intro a
    have hsum : H.h (∑ i, c i • m i) (m a) = (Matrix.mulVec (H.gram m) c) a := by
      let φ : V →+ E := AddMonoidHom.mk' (fun x => H.h x (m a)) (fun x x' => H.h_add_left x x' (m a))
      have hφ : H.h (∑ i, c i • m i) (m a) = φ (∑ i, c i • m i) := rfl

      rw [hφ, map_sum]
      simp only [Matrix.mulVec, dotProduct, HermSp.gram, Matrix.of_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      show H.h (c i • m i) (m a) = _
      rw [H.h_smul_left, mul_comm]
    rw [← hsum]
    exact hΛ _ hv _ (hm a)

  have hdc : ∀ i, (H.gram m).det * c i ∈ M.L.O := by
    intro i
    have key : Matrix.mulVec (H.gram m).adjugate (Matrix.mulVec (H.gram m) c) = (H.gram m).det • c := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    have hi := congrFun key i
    rw [Pi.smul_apply, smul_eq_mul] at hi
    have hmem : ∀ w : ι → E, (∀ j, w j ∈ M.L.O) → (Matrix.mulVec (H.gram m).adjugate w) i ∈ M.L.O := by
      intro w hw
      simp only [Matrix.mulVec, dotProduct]
      exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hadj i j) (hw j)
    rw [← hi]
    exact hmem _ hpair

  obtain ⟨_, y, hy, hdy⟩ := hdet
  have hc : ∀ i, c i ∈ M.L.O := by
    intro i
    have hci : c i = y * ((H.gram m).det * c i) := by
      rw [← mul_assoc, mul_comm y, hdy, one_mul]
    rw [hci]
    exact Subring.mul_mem _ hy (hdc i)
  refine Submodule.sum_mem _ fun i _ => ?_
  have hsm : c i • m i = (⟨c i, hc i⟩ : M.L.O) • m i := rfl
  rw [hsm]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.SaturatedSpanOfGramDetIsUnitIntegralLatticeStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

theorem _root_.GlobalTheory.T.saturated_span_of_gramDet_isUnit_integralLattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {ι : Type} [Fintype ι] [DecidableEq ι] (Λ : Submodule M.L.O V) (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, H.h x y ∈ M.L.O) (m : ι → V) (hm : ∀ i, m i ∈ Λ) (hdet : IsUnitO M (H.gram m).det), ∀ v ∈ Λ, v ∈ Submodule.span E (Set.range m) → v ∈ Submodule.span M.L.O (Set.range m) := by
  first | exact @GlobalTheory.satur_of_gram_det_unit | exact GlobalTheory.satur_of_gram_det_unit | (intros; apply GlobalTheory.satur_of_gram_det_unit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermNoDefectPrimeToInvariants

section

@[expose] public section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocNoDef
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

section Gen

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem N_unitary (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) : ∀ n ∈ Fr.N, IsUnitary H n := by
  intro n hn
  induction hn using Subgroup.closure_induction with
  | mem x hx => exact hx.1
  | one => intro a b; rfl
  | mul x y _ _ hx hy => intro a b; rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hx, hy]
  | inv x _ hx =>
    intro a b
    have hxx : ∀ v, x (x⁻¹ v) = v := fun v => by rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl
    rw [← hx (x⁻¹ a) (x⁻¹ b), hxx, hxx]

theorem frame_mem_lamStd (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f))
    (hL : Fr.IsInner L) (b : Fin (r + 1)) : Fr.f b ∈ Fr.LamStd L := by
  apply Submodule.subset_span
  obtain ⟨-, -, xz, hxz, hxzL, -⟩ := hL
  induction b using Fin.lastCases with
  | last =>
    have h1 : ∀ a, H.h (Fr.f (Fin.last r)) (Fr.es a) = 0 := fun a => by
      rw [H.h_herm (Fr.es a), Fr.h_sz, map_zero]
    have h2 : ∀ a : Fin r, H.h (Fr.f (Fin.last r)) (Fr.e a) = 0 := fun a =>
      Fr.h_iso _ _ (Or.inr (Fin.castSucc_lt_last a).ne)
    refine ⟨fun a => by rw [h1]; exact M.L.O.zero_mem, fun a => by rw [h2]; exact M.L.O.zero_mem, xz, ?_, hxzL⟩
    simp [FrameD.prF, h1, h2, hxz, FrameD.z]
  | cast a =>
    have h1 : ∀ c, H.h (Fr.f a.castSucc) (Fr.es c) = if a = c then 1 else 0 := fun c => Fr.h_es a c
    have h2 : ∀ c : Fin r, H.h (Fr.f a.castSucc) (Fr.e c) = 0 := fun c =>
      Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last a).ne)
    refine ⟨fun c => ?_, fun c => by rw [h2]; exact M.L.O.zero_mem, 0, ?_, by simp⟩
    · rw [h1]; split_ifs
      · exact M.L.O.one_mem
      · exact M.L.O.zero_mem
    · have h2' : ∀ c : Fin r, H.h (Fr.f a.castSucc) (Fr.f c.castSucc) = 0 := h2
      simp [FrameD.prF, h1, h2', FrameD.e]

theorem noDefect_gen (H : HermSp M V) {r : ℕ} (P : FPair H r) (hR : P.RelG (theta M)) (hP : P.PrimeTo)
    (d : Datum P) (t : Term V M r) (ht : IsTermOver P d t) : ¬ BBne (H := H) t := by
  rintro ⟨v, hvΛ, hvE, hvO⟩
  have hs : M.split = none := hP.1
  have hMM : H.MMfam t = Sum.elim t.f t.f' := by
    unfold HermSp.MMfam; rw [hs]
  rw [hMM] at hvE hvO
  obtain ⟨hT, hT', ⟨n, hn, hf, hΛ⟩, ⟨n', hn', hf', hΛ'⟩, -⟩ := ht
  have hu := N_unitary H P.A n hn
  have hu' := N_unitary H P.B n' hn'

  have hint : ∀ x ∈ t.abelian₂, ∀ y ∈ t.abelian₂, H.h x y ∈ M.L.O := by
    intro x hx y hy
    rw [hΛ] at hx hy
    obtain ⟨x0, hx0, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨y0, hy0, rfl⟩ := Submodule.mem_map.mp hy
    simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
    rw [hu]
    exact GlobalTheory.T.frameStandardLattice_hermitian_integral H P.A d.L d.hL x0 hx0 y0 hy0
  have hmem : ∀ i, Sum.elim t.f t.f' i ∈ t.abelian₂ := by
    rintro (b | b)
    · simp only [Sum.elim_inl, hf]
      rw [hΛ]
      exact Submodule.mem_map_of_mem (f := ((n : V →ₗ[E] V).restrictScalars M.L.O))
        (frame_mem_lamStd H P.A d.L d.hL b)
    · simp only [Sum.elim_inr, hf']
      rw [hΛ']
      exact Submodule.mem_map_of_mem (f := ((n' : V →ₗ[E] V).restrictScalars M.L.O))
        (frame_mem_lamStd H P.B d.L' d.hL' b)
  have hDl : ∀ l, H.Dl t.f t.f' l = H.Dl P.A.f P.B.f l := by
    intro l
    rw [hf, hf']
    exact GlobalTheory.T.pairingLeadingMinor_eq_of_unitriangular_changes H _ _ _ _ (GlobalTheory.T.isFamilyUnitriangularChange_of_mem_frameUnipotent H P.A n hn) (GlobalTheory.T.isFamilyUnitriangularChange_of_mem_frameUnipotent H P.B n' hn') l
  have hG : H.Gdet t.f t.f' t.T t.T' = P.Gv := by
    simp only [HermSp.Gdet, hDl, hT, hT', FPair.Gv]
  have hfr : ∀ (Fr : FrameD H r) (g : V ≃ₗ[E] V), IsUnitary H g → ∀ a b,
      H.h (g (Fr.f a)) (g (Fr.f b)) =
        if a = Fin.last r ∧ b = Fin.last r then -(algebraMap F E Fr.T) else 0 := by
    intro Fr g hg a b
    rw [hg]
    split_ifs with hab
    · rw [hab.1, hab.2]; exact Fr.h_zz
    · apply Fr.h_iso
      tauto
  have hdet := GlobalTheory.T.gramDet_joinedFamily_eq_pm_norm_difference H t.f t.f' t.T t.T'
    (by intro a b; rw [hf, hT]; exact hfr P.A n hu a b)
    (by intro a b; rw [hf', hT']; exact hfr P.B n' hu' a b)
    (by rw [hDl]; exact hR.2.1)
  rw [hG] at hdet
  have hU : IsUnitO M (H.gram (Sum.elim t.f t.f')).det := by
    obtain ⟨h1, y, hy, hxy⟩ := hP.2.1
    rcases hdet with h | h
    · rw [h]; exact ⟨h1, y, hy, hxy⟩
    · rw [h]
      refine ⟨M.L.O.neg_mem h1, -y, M.L.O.neg_mem hy, ?_⟩
      rw [neg_mul_neg]; exact hxy
  exact hvO (GlobalTheory.T.saturated_span_of_gramDet_isUnit_integralLattice H t.abelian₂ hint (Sum.elim t.f t.f') hmem hU v hvΛ hvE)

end Gen

theorem noDefect : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (p : PlF D), (FP p).RelG (LocNG.theta (Z.M p)) → (FP p).PrimeTo → ∀ (d : LocNG.Datum (FP p)) (t : Loc.Term (Vp D p) (Z.M p) D.R.rS), LocNG.IsTermOver (FP p) d t → ¬ LocNG.BBne (H := locH Z p) t :=
  fun _ _ FP p hR hP d t ht => noDefect_gen _ (FP p) hR hP d t ht

end GlobalTheory.LocNoDef

end
end
end
