module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemSpanCornerSeparableStatement
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentBlockCharPolyEqCharpolyImageStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Mathlib.RingTheory.PicardGroup

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemSubmoduleAllCharpolySeparable

section

@[expose] public section

open Polynomial

namespace GlobalTheory.SepGeneric

theorem separable_iff_resultant {K : Type} [Field K] {f : K[X]} (hf : f.Monic) {t : ℕ}
    (ht : f.natDegree = t) : f.Separable ↔ resultant f (derivative f) t t ≠ 0 := by
  have hle : (derivative f).natDegree ≤ t :=
    (natDegree_derivative_le f).trans (by omega)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  have h1 : resultant f (derivative f) t t
      = resultant f (derivative f) f.natDegree (derivative f).natDegree := by
    have := resultant_add_right_deg f (derivative f) t (derivative f).natDegree k le_rfl
    rw [← hk] at this
    rw [this, ← ht, hf.coeff_natDegree]
    simp
  rw [h1, ← isUnit_iff_ne_zero, isUnit_resultant_iff_isCoprime hf]
  rfl

theorem finite_bad_base {K : Type} [Field K] {t : ℕ} (B A : Matrix (Fin t) (Fin t) K)
    (hB : B.charpoly.Separable) : {l : K | ¬ (B + l • A).charpoly.Separable}.Finite := by
  classical
  let N : Matrix (Fin t) (Fin t) K[X] := B.map C + (X : K[X]) • A.map C
  let D : K[X] := resultant N.charpoly (derivative N.charpoly) t t
  have hN : ∀ l : K, N.map (evalRingHom l) = B + l • A := by
    intro l
    ext i j
    simp [N]
    ring
  have hD : ∀ l : K, (B + l • A).charpoly.Separable ↔ D.eval l ≠ 0 := by
    intro l
    rw [separable_iff_resultant (Matrix.charpoly_monic _)
      (t := t) (by simp), ← hN, Matrix.charpoly_map, derivative_map, resultant_map_map]
    rfl
  have hD0 : D ≠ 0 := by
    intro h
    have := (hD 0).1 (by simpa using hB)
    simp [h] at this
  refine (D.roots.toFinset.finite_toSet).subset ?_
  intro l hl
  simp only [Set.mem_setOf_eq, hD, not_not] at hl
  simp [hD0, hl]

theorem separable_smul {K : Type} [Field K] {t : ℕ} (A : Matrix (Fin t) (Fin t) K) {c : K}
    (hc : c ≠ 0) (hA : A.charpoly.Separable) : (c • A).charpoly.Separable := by
  classical
  have h1 : (c • A).charpoly = C c ^ t * A.charpoly.comp (C c⁻¹ * X) := by
    have : (c • A).charmatrix = (C c : K[X]) • (A.charmatrix.map (compRingHom (C c⁻¹ * X))) := by
      ext1 i j
      by_cases h : i = j
      · subst h
        have h3 : (C c : K[X]) * (C c⁻¹ * X) = X := by
          rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hc, C_1, one_mul]
        simp [mul_sub, h3]
      · simp [Matrix.charmatrix_apply_ne _ _ _ h]
    rw [Matrix.charpoly, this, Matrix.det_smul, Matrix.charpoly, Fintype.card_fin]
    congr 1
    exact ((compRingHom (C c⁻¹ * X)).map_det A.charmatrix).symm
  have h2 : (A.charpoly.comp (C c⁻¹ * X)).Separable := by
    rw [separable_def, derivative_comp]
    have hu : IsUnit (derivative (C c⁻¹ * X : K[X])) := by
      simpa using isUnit_C.2 (IsUnit.mk0 _ (inv_ne_zero hc))
    rw [isCoprime_mul_unit_left_right hu]
    exact ((separable_def _).1 hA).map (compRingHom (C c⁻¹ * X))
  rw [h1, mul_comm]
  exact h2.mul_unit ((isUnit_C.2 (IsUnit.mk0 _ hc)).pow t)

theorem finite_bad_dir {K : Type} [Field K] {t : ℕ} (B A : Matrix (Fin t) (Fin t) K) {c : K}
    (hc : c ≠ 0) (hA : (c • A).charpoly.Separable) :
    {l : K | ¬ (B + l • A).charpoly.Separable}.Finite := by
  have hA' : A.charpoly.Separable := by
    have := separable_smul _ (inv_ne_zero hc) hA
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  have hf := (finite_bad_base A B hA').preimage (f := fun l : K => l⁻¹) inv_injective.injOn
  refine (hf.insert 0).subset ?_
  intro l hl
  by_cases h0 : l = 0
  · exact Or.inl h0
  · refine Or.inr ?_
    intro h
    apply hl
    have := separable_smul _ h0 h
    rwa [smul_add, smul_smul, mul_inv_cancel₀ h0, one_smul, add_comm] at this

theorem exists_separable {O K X : Type} [CommRing O] [IsDomain O] [Infinite O] [Field K]
    [Algebra O K] [IsFractionRing O K] [Finite X] (t : ℕ)
    (M : Submodule O (X → Matrix (Fin t) (Fin t) K)) (a : X → Matrix (Fin t) (Fin t) K)
    (h : ∀ x, (a x).charpoly.Separable ∨
      ∃ s ∈ M, ∃ c : K, c ≠ 0 ∧ (c • s x).charpoly.Separable) :
    ∃ s ∈ M, ∀ x, (a x + s x).charpoly.Separable := by
  classical
  have key : ∀ Y : Finset X, ∃ s ∈ M, ∀ x ∈ Y, (a x + s x).charpoly.Separable := by
    intro Y
    induction Y using Finset.induction_on with
    | empty => exact ⟨0, M.zero_mem, by simp⟩
    | insert x Y hx ih =>
      obtain ⟨s, hs, hY⟩ := ih
      have h1 : ∃ s' ∈ M, {l : K | ¬ (a x + s x + l • s' x).charpoly.Separable}.Finite := by
        rcases h x with h | ⟨s', hs', c, hc, h⟩
        · refine ⟨s, hs, ?_⟩
          have hf := (finite_bad_base (a x) (s x) h).preimage (f := fun l : K => 1 + l)
            (add_right_injective 1).injOn
          refine hf.subset ?_
          intro l hl
          simpa [add_smul, add_assoc] using hl
        · exact ⟨s', hs', finite_bad_dir _ _ hc h⟩
      obtain ⟨s', hs', h1⟩ := h1
      have h2 : (⋃ y ∈ insert x Y,
          {l : K | ¬ (a y + s y + l • s' y).charpoly.Separable}).Finite := by
        refine (insert x Y).finite_toSet.biUnion ?_
        intro y hy
        rcases Finset.mem_insert.1 hy with rfl | hy
        · exact h1
        · exact finite_bad_base _ _ (hY y hy)
      have h3 := h2.preimage (f := algebraMap O K) (IsFractionRing.injective O K).injOn
      obtain ⟨l, hl⟩ := h3.exists_notMem
      refine ⟨s + l • s', M.add_mem hs (M.smul_mem l hs'), ?_⟩
      intro y hy
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_not] at hl
      have := hl y hy
      rwa [algebraMap_smul, add_assoc] at this
  have := Fintype.ofFinite X
  obtain ⟨s, hs, h⟩ := key Finset.univ
  exact ⟨s, hs, fun x => h x (Finset.mem_univ x)⟩

end GlobalTheory.SepGeneric
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemSubmoduleAllCharpolySeparableStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

theorem _root_.GlobalTheory.T.exists_mem_submodule_all_charpoly_separable : ∀ {O K X : Type} [CommRing O] [IsDomain O] [Infinite O] [Field K] [Algebra O K] [IsFractionRing O K] [Finite X] (t : ℕ) (M : Submodule O (X → Matrix (Fin t) (Fin t) K)) (a : X → Matrix (Fin t) (Fin t) K), (∀ x, (a x).charpoly.Separable ∨ ∃ s ∈ M, ∃ c : K, c ≠ 0 ∧ (c • s x).charpoly.Separable) → ∃ s ∈ M, ∀ x, (a x + s x).charpoly.Separable := by
  first | exact @GlobalTheory.SepGeneric.exists_separable | exact GlobalTheory.SepGeneric.exists_separable | (intros; apply GlobalTheory.SepGeneric.exists_separable <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHeckeSpanCorrectionDistinctEigenvalues

section

@[expose] public section

noncomputable section

namespace GlobalTheory.SpanRing

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices Polynomial

theorem blockPol_map_ringHom {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B)
    (e M : Matrix (Fin n) (Fin n) A) : (blockPol e M).map f = blockPol (e.map f) (M.map f) := by
  unfold blockPol
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

theorem map_mem_span_frac {Γ A : Type} [CommRing A] [IsDomain A] {n : ℕ}
    (σ : Γ → Matrix (Fin n) (Fin n) A) {w : Matrix (Fin n) (Fin n) A}
    (hw : w ∈ Submodule.span A (Set.range σ)) :
    w.map (toFr A) ∈ Submodule.span (FractionRing A) (Set.range fun g => (σ g).map (toFr A)) := by
  induction hw using Submodule.span_induction with
  | mem y hy => obtain ⟨h, rfl⟩ := hy; exact Submodule.subset_span ⟨h, rfl⟩
  | zero => simp
  | add y z _ _ hy hz =>
    rw [Matrix.map_add _ (map_add _)]
    exact add_mem hy hz
  | smul c y _ hy =>
    have : (c • y).map (toFr A) = toFr A c • y.map (toFr A) := by
      ext i j; simp
    rw [this]
    exact Submodule.smul_mem _ _ hy

theorem exists_denom_span_frac {Γ A : Type} [CommRing A] [IsDomain A] {n : ℕ}
    (σ : Γ → Matrix (Fin n) (Fin n) A) {m : Matrix (Fin n) (Fin n) (FractionRing A)}
    (hm : m ∈ Submodule.span (FractionRing A) (Set.range fun g => (σ g).map (toFr A))) :
    ∃ d : A, d ≠ 0 ∧ ∃ w ∈ Submodule.span A (Set.range σ), w.map (toFr A) = toFr A d • m := by
  induction hm using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨h, rfl⟩ := hy
    exact ⟨1, one_ne_zero, σ h, Submodule.subset_span ⟨h, rfl⟩, by simp⟩
  | zero => exact ⟨1, one_ne_zero, 0, zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d, hd, w, hw, e⟩ := hy
    obtain ⟨d', hd', w', hw', e'⟩ := hz
    refine ⟨d * d', mul_ne_zero hd hd', d' • w + d • w',
      add_mem (Submodule.smul_mem _ _ hw) (Submodule.smul_mem _ _ hw'), ?_⟩
    ext i j
    have h1 := congrFun (congrFun e i) j
    have h2 := congrFun (congrFun e' i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, map_add (f := _),
      map_mul] at h1 h2 ⊢
    rw [h1, h2]; ring
  | smul c y _ hy =>
    obtain ⟨d, hd, w, hw, e⟩ := hy
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := A) c
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hq1 : algebraMap A (FractionRing A) q ≠ 0 := by simpa using hq0
    refine ⟨d * q, mul_ne_zero hd hq0, p • w, Submodule.smul_mem _ _ hw, ?_⟩
    ext i j
    have h1 := congrFun (congrFun e i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul] at h1 ⊢
    rw [h1]
    simp only [toFr]
    field_simp

theorem exists_correction_distinct_eigenvalues {Γ X A : Type} [Group Γ] [Finite X] [CommRing A]
    [IsDomain A] [CharZero A] {n t : ℕ} (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A))
    (π : X) (g0 : Γ) (eB : X → Matrix (Fin n) (Fin n) A) (z : A) (hz : z ≠ 0)
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → A) x ≠ (f : X → A) y)
    (hirr : ∀ x, AbsIrrDistinct (overK (rep x))) (hin : InRing T rep eB) (hid : eB * eB = eB)
    (hrk : ∀ x, ((eB x).map (toFr A)).rank = t)
    (hπ : ((blockPol (eB π) (eB π * mat (rep π) g0 * eB π)).map (toFr A)).Separable) :
    ∃ s, InMatrixCongruenceModule T rep π eB s ∧ ∀ x,
      (((blockPol (eB x) (eB x * mat (rep x) g0 * eB x + z • s x)).map (toFr A)).rootSet
        (AlgebraicClosure (FractionRing A))).ncard = t := by
  classical
  have hidx : ∀ x, eB x * eB x = eB x := fun x => congrFun hid x
  have hidK : ∀ x, (eB x).map (toFr A) * (eB x).map (toFr A) = (eB x).map (toFr A) := fun x => by
    rw [← Matrix.map_mul, hidx]
  choose a b hba hab hpol using fun x => GlobalTheory.T.idempotentBlockCharPoly_eq_charpoly_image ((eB x).map (toFr A)) (hidK x) (hrk x)
  have hbe : ∀ x, b x * (eB x).map (toFr A) = b x := fun x => by
    rw [← hab, ← Matrix.mul_assoc, hba, Matrix.one_mul]
  have hea : ∀ x, (eB x).map (toFr A) * a x = a x := fun x => by
    rw [← hab, Matrix.mul_assoc, hba, Matrix.mul_one]
  have hpolA : ∀ x (M : Matrix (Fin n) (Fin n) A),
      (blockPol (eB x) (eB x * M * eB x)).map (toFr A) = (b x * M.map (toFr A) * a x).charpoly := by
    intro x M
    rw [blockPol_map_ringHom, Matrix.map_mul, Matrix.map_mul, hpol]
  let φ : (X → Matrix (Fin n) (Fin n) A) →ₗ[A] (X → Matrix (Fin t) (Fin t) (FractionRing A)) :=
    { toFun := fun s x => b x * (z • s x).map (toFr A) * a x
      map_add' := fun s s' => by
        funext x
        simp only [Pi.add_apply, smul_add, Matrix.map_add _ (map_add (toFr A)), Matrix.mul_add,
          Matrix.add_mul]
      map_smul' := fun c s => by
        funext x
        have : (z • c • s x).map (toFr A) = c • (z • s x).map (toFr A) := by
          ext i j
          simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
          rw [Algebra.smul_def, mul_left_comm]
        simp only [this, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, Pi.smul_apply] }
  have hφ : ∀ s x, φ s x = b x * (z • s x).map (toFr A) * a x := fun _ _ => rfl
  obtain ⟨_, ⟨s, hs, rfl⟩, hsx⟩ := GlobalTheory.T.exists_mem_submodule_all_charpoly_separable (O := A) (K := FractionRing A) t
    ((spanRingCornerIdealModule T rep π eB).map φ) (fun x => b x * (mat (rep x) g0).map (toFr A) * a x) (by
      intro x
      by_cases hx : x = π
      · left
        subst hx
        rwa [hpolA] at hπ
      · right
        have hmem : a x * b x ∈ Submodule.span (FractionRing A)
            (Set.range fun g => (mat (rep x) g).map (toFr A)) := by
          rw [hab]
          exact map_mem_span_frac _ (eval_mem_span hin x)
        obtain ⟨m, hm, hms⟩ := GlobalTheory.T.exists_mem_span_corner_charpoly_separable (mapM (toFr A) ((Units.coeHom _).comp (rep x)))
          (a x) (b x) (hirr x) (hba x) hmem
        obtain ⟨d, hd, w, hw, hwm⟩ := exists_denom_span_frac (mat (rep x)) hm
        obtain ⟨w', hw', rfl⟩ := exists_inRing_eval (T := T) x hw
        obtain ⟨f, hf, hfx⟩ := hsep x π hx
        have hj : f - algebraMap A (X → A) (f π) ∈ T := T.sub_mem hf (T.algebraMap_mem _)
        have hjx : f x - f π ≠ 0 := sub_ne_zero.2 hfx
        have hc : toFr A (z * (f x - f π) * d) ≠ 0 :=
          (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).2
            (mul_ne_zero (mul_ne_zero hz hjx) hd)
        refine ⟨_, ⟨fun y => (f - algebraMap A (X → A) (f π)) y • (eB y * w' y * eB y),
          Submodule.subset_span ⟨_, hj, by simp, w', hw', rfl⟩, rfl⟩,
          (toFr A (z * (f x - f π) * d))⁻¹, inv_ne_zero hc, ?_⟩
        have h1 : (z • ((f - algebraMap A (X → A) (f π)) x • (eB x * w' x * eB x))).map (toFr A) =
            toFr A (z * (f x - f π) * d) •
              ((eB x).map (toFr A) * m * (eB x).map (toFr A)) := by
          have h2 : ∀ (c : A) (M : Matrix (Fin n) (Fin n) A),
              (c • M).map (toFr A) = toFr A c • M.map (toFr A) := fun c M => by
            ext i j; simp
          rw [h2, h2, Matrix.map_mul, Matrix.map_mul, hwm]
          simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, map_mul, mul_assoc]
          simp
        rw [hφ, h1, Matrix.mul_smul, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hc, one_smul,
          ← Matrix.mul_assoc, ← Matrix.mul_assoc, hbe, Matrix.mul_assoc _ _ (a x), hea]
        exact hms)
  have hs' := (mem_spanRingCornerIdealModule_iff T rep π eB s).1 hs
  refine ⟨s, hs', fun x => ?_⟩
  have hc := InMatrixCongruenceModule.corner hid hs' x
  have h1 : eB x * mat (rep x) g0 * eB x + z • s x = eB x * (mat (rep x) g0 + z • s x) * eB x := by
    rw [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, hc.1, hc.2]
  have h2 := hsx x
  rw [hφ, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.map_add _ (map_add (toFr A))] at h2
  rw [h1, hpolA, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
    Polynomial.card_rootSet_eq_natDegree h2 (IsAlgClosed.splits _), Matrix.charpoly_natDegree_eq_dim,
    Fintype.card_fin]

end GlobalTheory.SpanRing

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHeckeSpanCorrectionDistinctEigenvaluesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

theorem _root_.GlobalTheory.T.exists_heckeSpan_correction_distinct_eigenvalues : ∀ {Γ X A : Type} [Group Γ] [Finite X] [CommRing A] [IsDomain A] [CharZero A] {n t : ℕ} (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) (π : X) (g0 : Γ) (eB : X → Matrix (Fin n) (Fin n) A) (z : A), z ≠ 0 → (∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → A) x ≠ (f : X → A) y) → (∀ x, AbsIrrDistinct (overK (rep x))) → InRing T rep eB → eB * eB = eB → (∀ x, ((eB x).map (toFr A)).rank = t) → ((blockPol (eB π) (eB π * mat (rep π) g0 * eB π)).map (toFr A)).Separable → ∃ s, InMatrixCongruenceModule T rep π eB s ∧ ∀ x, (((blockPol (eB x) (eB x * mat (rep x) g0 * eB x + z • s x)).map (toFr A)).rootSet (AlgebraicClosure (FractionRing A))).ncard = t := by
  first | exact @GlobalTheory.SpanRing.exists_correction_distinct_eigenvalues | exact GlobalTheory.SpanRing.exists_correction_distinct_eigenvalues | (intros; apply GlobalTheory.SpanRing.exists_correction_distinct_eigenvalues <;> assumption)
end
end
