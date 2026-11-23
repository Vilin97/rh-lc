module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedPhiModuleDescentFiniteLevelStatement
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftStratifiedSolutionSuccOfCover

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem mem_span_range_of_isBaseChange {R S M N : Type} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    {f : M →ₗ[R] N} (hf : IsBaseChange S f) (w : N) : w ∈ Submodule.span S (Set.range f) := by
  obtain ⟨y, rfl⟩ := hf.equiv.surjective w
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul s x => rw [hf.equiv_tmul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  | add a b ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb

theorem le_of_span_eq_top_of_isBaseChange {R S N : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (P Q : Submodule R N) (hPQ : P ≤ Q) (hQ : IsBaseChange S Q.subtype)
    (hP : Submodule.span S (P : Set N) = ⊤) : Q ≤ P := by
  let ι := Submodule.inclusion hPQ
  have hs : Function.Surjective (ι.lTensor S) := by
    intro y
    have hv : hQ.equiv y ∈ Submodule.span S (P : Set N) := hP ▸ Submodule.mem_top
    have key : ∀ v ∈ Submodule.span S (P : Set N), ∃ y' : S ⊗[R] P, hQ.equiv (ι.baseChange S y') = v := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx => exact ⟨1 ⊗ₜ ⟨x, hx⟩, by simp [ι, hQ.equiv_tmul]⟩
      | zero => exact ⟨0, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha⟩ := hx
        obtain ⟨b, hb⟩ := hy
        exact ⟨a + b, by simp [ha, hb]⟩
      | smul c x _ hx =>
        obtain ⟨a, ha⟩ := hx
        exact ⟨c • a, by simp [ha]⟩
    obtain ⟨y', hy'⟩ := key _ hv
    exact ⟨y', by rw [← LinearMap.baseChange_eq_ltensor]; exact hQ.equiv.injective hy'⟩
  have hι := (Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S ι).mp hs
  intro x hx
  obtain ⟨y, hy⟩ := hι ⟨x, hx⟩
  have hx' : (y : N) = x := congrArg Subtype.val hy
  exact hx' ▸ y.2

theorem lift_solution_succ_of_descent {l : ℕ} {R : Type} [CommRing R] {d : ℕ} {B C D : Obj l R} (h : Hom B C)
    (p q : Hom C D) (hcomm : p.comp h = q.comp h) (m : ℕ) (hff : (qmap h m).FaithfullyFlat)
    (ε : Matrix (Fin d) (Fin d) D.A)
    (H : ∀ k : ℕ, letI := (qmap h k).toAlgebra
      ∃ N : Submodule (B.A ⧸ adI B ^ k) (Fin d → C.A ⧸ adI C ^ k),
        (∀ z, z ∈ N ↔ (fun i => qmap p k (z i)) =
          (ε.map (Ideal.Quotient.mk (adI D ^ k))).mulVec fun i => qmap q k (z i)) ∧
        IsBaseChange (C.A ⧸ adI C ^ k) N.subtype)
    (z : Fin d → C.A) (hz : ∀ i, p.f (z i) - ε.mulVec (fun j => q.f (z j)) i ∈ adI D ^ m) :
    ∃ z' : Fin d → C.A, (∀ i, z' i - z i ∈ adI C ^ m) ∧
      ∀ i, p.f (z' i) - ε.mulVec (fun j => q.f (z' j)) i ∈ adI D ^ (m + 1) := by
  have hmem : ∀ (k : ℕ) (w : Fin d → C.A),
      ((fun i => qmap p k (Ideal.Quotient.mk (adI C ^ k) (w i))) =
        (ε.map (Ideal.Quotient.mk (adI D ^ k))).mulVec (fun i => qmap q k (Ideal.Quotient.mk (adI C ^ k) (w i)))) ↔
      ∀ i, p.f (w i) - ε.mulVec (fun j => q.f (w j)) i ∈ adI D ^ k := by
    intro k w
    rw [funext_iff]
    refine forall_congr' fun i => ?_
    have e1 : qmap p k (Ideal.Quotient.mk (adI C ^ k) (w i)) = Ideal.Quotient.mk (adI D ^ k) (p.f (w i)) :=
      qmap_mk p k _
    have e2 : (ε.map (Ideal.Quotient.mk (adI D ^ k))).mulVec
        (fun i => qmap q k (Ideal.Quotient.mk (adI C ^ k) (w i))) i =
        Ideal.Quotient.mk (adI D ^ k) (ε.mulVec (fun j => q.f (w j)) i) := by
      simp only [qmap_mk]
      exact (RingHom.map_mulVec (Ideal.Quotient.mk (adI D ^ k)) ε (fun j => q.f (w j)) i).symm
    rw [e1, e2]
    exact Ideal.Quotient.eq
  letI alg0 : Algebra (B.A ⧸ adI B ^ m) (C.A ⧸ adI C ^ m) := (qmap h m).toAlgebra
  letI alg1 : Algebra (B.A ⧸ adI B ^ (m + 1)) (C.A ⧸ adI C ^ (m + 1)) := (qmap h (m + 1)).toAlgebra
  haveI : Module.FaithfullyFlat (B.A ⧸ adI B ^ m) (C.A ⧸ adI C ^ m) := hff
  obtain ⟨N, hN, hbN⟩ := H m
  obtain ⟨N', hN', hbN'⟩ := H (m + 1)
  have hpq : ∀ b : B.A, p.f (h.f b) = q.f (h.f b) := fun b => congrArg (fun g : Hom B D => g.f b) hcomm
  let P : Submodule (B.A ⧸ adI B ^ m) (Fin d → C.A ⧸ adI C ^ m) :=
    { carrier := {x | ∃ w : Fin d → C.A, (fun i => Ideal.Quotient.mk (adI C ^ m) (w i)) = x ∧
        ∀ i, p.f (w i) - ε.mulVec (fun j => q.f (w j)) i ∈ adI D ^ (m + 1)}
      zero_mem' := ⟨0, by funext i; simp, fun i => by
        have e : (fun j => q.f ((0 : Fin d → C.A) j)) = 0 := funext fun j => by simp
        rw [e, Matrix.mulVec_zero]
        simp⟩
      add_mem' := by
        rintro _ _ ⟨w₁, rfl, h₁⟩ ⟨w₂, rfl, h₂⟩
        refine ⟨w₁ + w₂, by funext i; simp, fun i => ?_⟩
        have := Ideal.add_mem _ (h₁ i) (h₂ i)
        convert this using 1
        have e : (fun j => q.f ((w₁ + w₂) j)) = (fun j => q.f (w₁ j)) + (fun j => q.f (w₂ j)) := by
          funext j; simp
        rw [e, Matrix.mulVec_add]
        simp only [Pi.add_apply, map_add (f := _)]
        ring
      smul_mem' := by
        rintro c _ ⟨w, rfl, hw⟩
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
        refine ⟨fun i => h.f b * w i, ?_, fun i => ?_⟩
        · funext i
          simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra, qmap_mk]
        · have := Ideal.mul_mem_left _ (q.f (h.f b)) (hw i)
          convert this using 1
          have e : (fun j => q.f (h.f b * w j)) = q.f (h.f b) • (fun j => q.f (w j)) := by
            funext j; simp
          rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, hpq, mul_sub] }
  have hPN : P ≤ N := by
    rintro _ ⟨w, rfl, hw⟩
    exact (hN _).2 ((hmem m w).2 fun i => Ideal.pow_le_pow_right (Nat.le_succ m) (hw i))
  have hspan : Submodule.span (C.A ⧸ adI C ^ m) (P : Set (Fin d → C.A ⧸ adI C ^ m)) = ⊤ := by
    rw [eq_top_iff]
    rintro v -
    let πC := Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ m) : adI C ^ (m + 1) ≤ adI C ^ m)
    let r : (Fin d → C.A ⧸ adI C ^ (m + 1)) → (Fin d → C.A ⧸ adI C ^ m) := fun y i => πC (y i)
    have hr : ∀ y ∈ Submodule.span (C.A ⧸ adI C ^ (m + 1)) (Set.range N'.subtype),
        r y ∈ Submodule.span (C.A ⧸ adI C ^ m) (P : Set (Fin d → C.A ⧸ adI C ^ m)) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨⟨x, hxN⟩, rfl⟩ := hx
        apply Submodule.subset_span
        obtain ⟨w, rfl⟩ : ∃ w : Fin d → C.A, (fun i => Ideal.Quotient.mk _ (w i)) = x :=
          ⟨fun i => (Ideal.Quotient.mk_surjective (x i)).choose,
            funext fun i => (Ideal.Quotient.mk_surjective (x i)).choose_spec⟩
        exact ⟨w, by funext i; simp [r, πC], (hmem (m + 1) w).1 ((hN' _).1 hxN)⟩
      | zero =>
        convert Submodule.zero_mem _ using 1
        funext i; simp [r]
      | add x y _ _ hx hy =>
        convert Submodule.add_mem _ hx hy using 1
        funext i; simp [r]
      | smul c x _ hx =>
        convert Submodule.smul_mem _ (πC c) hx using 1
        funext i; simp [r]
    obtain ⟨w, rfl⟩ : ∃ w : Fin d → C.A, (fun i => Ideal.Quotient.mk (adI C ^ m) (w i)) = v :=
      ⟨fun i => (Ideal.Quotient.mk_surjective (v i)).choose,
        funext fun i => (Ideal.Quotient.mk_surjective (v i)).choose_spec⟩
    have := hr (fun i => Ideal.Quotient.mk _ (w i)) (mem_span_range_of_isBaseChange hbN' _)
    convert this using 1
    funext i; simp [r, πC]
  have hNP : N ≤ P := le_of_span_eq_top_of_isBaseChange P N hPN hbN hspan
  have hzN : (fun i => Ideal.Quotient.mk (adI C ^ m) (z i)) ∈ N := (hN _).2 ((hmem m z).2 hz)
  obtain ⟨w, hw, hwE⟩ := hNP hzN
  exact ⟨w, fun i => Ideal.Quotient.eq.1 (congrFun hw i), hwE⟩

theorem lift_solution_succ : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C D : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C) (p q : Hom C D), Cover h → IsPO h h p q → ∀ (m : ℕ) (z : Fin d → C.A), (∀ i, p.f (z i) - (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z j)) i ∈ adI D ^ m) → ∃ z' : Fin d → C.A, (∀ i, z' i - z i ∈ adI C ^ m) ∧ ∀ i, p.f (z' i) - (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z' j)) i ∈ adI D ^ (m + 1) := by
  intro l _ K bk d S B C D h f p q hcov hpo m z hz
  refine lift_solution_succ_of_descent h p q hpo.comm m (hcov.ff m) _ (fun k => ?_) z hz
  exact (GlobalTheory.T.stratifiedPhiModule_descent_finite_level l K bk d S B C D h f p q hcov hpo k).imp fun N hN => ⟨hN.1, hN.2.2.2⟩

end GlobalTheory.BSP
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftStratifiedSolutionSuccOfCoverStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.lift_stratifiedSolution_succ_of_cover : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C D : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C) (p q : Hom C D), Cover h → IsPO h h p q → ∀ (m : ℕ) (z : Fin d → C.A), (∀ i, p.f (z i) - (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z j)) i ∈ adI D ^ m) → ∃ z' : Fin d → C.A, (∀ i, z' i - z i ∈ adI C ^ m) ∧ ∀ i, p.f (z' i) - (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z' j)) i ∈ adI D ^ (m + 1) := by
  first | exact @GlobalTheory.BSP.lift_solution_succ | exact GlobalTheory.BSP.lift_solution_succ | (intros; apply GlobalTheory.BSP.lift_solution_succ <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDescentSolutionLiftModPrismIdeal

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem pow_smul_top_eq {A : Type} [CommRing A] (I : Ideal A) (n : ℕ) :
    (I ^ n • (⊤ : Submodule A A)) = I ^ n := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top]

theorem mulVec_mem_of_mem {B : Type} [CommRing B] {d : ℕ} (E : Matrix (Fin d) (Fin d) B) (J : Ideal B)
    (v : Fin d → B) (hv : ∀ j, v j ∈ J) (i : Fin d) : E.mulVec v i ∈ J := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hv j)

theorem lift_solution_of_step {A B : Type} [CommRing A] [CommRing B] (I : Ideal A) (J : Ideal B)
    (hA : IsPrecomplete I A) (hB : IsHausdorff J B) {d : ℕ} (p q : A →+* B)
    (hp : ∀ m : ℕ, I ^ m ≤ (J ^ m).comap p) (hq : ∀ m : ℕ, I ^ m ≤ (J ^ m).comap q)
    (E : Matrix (Fin d) (Fin d) B)
    (step : ∀ (m : ℕ) (z : Fin d → A), (∀ i, p (z i) - E.mulVec (fun j => q (z j)) i ∈ J ^ m) →
      ∃ z' : Fin d → A, (∀ i, z' i - z i ∈ I ^ m) ∧
        ∀ i, p (z' i) - E.mulVec (fun j => q (z' j)) i ∈ J ^ (m + 1))
    (z : Fin d → A) (hz : ∀ i, p (z i) - E.mulVec (fun j => q (z j)) i ∈ J ^ 1) :
    ∃ z' : Fin d → A, (∀ i, z' i - z i ∈ I ^ 1) ∧
      (fun i => p (z' i)) = E.mulVec (fun j => q (z' j)) := by

  let res : (Fin d → A) → Fin d → B := fun w i => p (w i) - E.mulVec (fun j => q (w j)) i
  have hres_sub : ∀ (w w' : Fin d → A) (i : Fin d),
      res w i - res w' i = p (w i - w' i) - E.mulVec (fun j => q (w j - w' j)) i := by
    intro w w' i
    have : (fun j => q (w j - w' j)) = (fun j => q (w j)) - (fun j => q (w' j)) := by
      funext j; simp
    show p (w i) - E.mulVec (fun j => q (w j)) i - (p (w' i) - E.mulVec (fun j => q (w' j)) i) = _
    rw [this, Matrix.mulVec_sub, Pi.sub_apply, map_sub]
    ring

  have hseq : ∃ g : ℕ → (Fin d → A), g 0 = z ∧ (∀ k i, res (g k) i ∈ J ^ (k + 1)) ∧
      ∀ k i, g (k + 1) i - g k i ∈ I ^ (k + 1) := by
    let G : (k : ℕ) → {w : Fin d → A // ∀ i, res w i ∈ J ^ (k + 1)} := fun k =>
      Nat.rec (motive := fun k => {w : Fin d → A // ∀ i, res w i ∈ J ^ (k + 1)}) ⟨z, hz⟩
        (fun k w => ⟨Classical.choose (step (k + 1) w.1 w.2),
          (Classical.choose_spec (step (k + 1) w.1 w.2)).2⟩) k
    refine ⟨fun k => (G k).1, rfl, fun k => (G k).2, fun k i => ?_⟩
    exact (Classical.choose_spec (step (k + 1) (G k).1 (G k).2)).1 i
  let g := Classical.choose hseq
  have hg0 : g 0 = z := (Classical.choose_spec hseq).1
  have hgres : ∀ k i, res (g k) i ∈ J ^ (k + 1) := (Classical.choose_spec hseq).2.1
  have hgd : ∀ k i, g (k + 1) i - g k i ∈ I ^ (k + 1) := (Classical.choose_spec hseq).2.2

  have hcau : ∀ i {m n : ℕ}, m ≤ n → g n i - g m i ∈ I ^ m := by
    intro i m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have h1 : g (n + 1) i - g n i ∈ I ^ m :=
        Ideal.pow_le_pow_right (by omega) (hgd n i)
      have := Ideal.add_mem _ h1 ih
      simpa using this

  have hlim : ∀ i, ∃ L : A, ∀ n, g n i - L ∈ I ^ n := by
    intro i
    have h := @IsPrecomplete.prec' A _ I A _ _ hA (fun k => g k i) (fun {m n} hmn => by
      rw [SModEq.sub_mem, pow_smul_top_eq]
      have := hcau i hmn
      rw [← neg_mem_iff, neg_sub] at this
      exact this)
    refine ⟨Classical.choose h, fun n => ?_⟩
    have := Classical.choose_spec h n
    rw [SModEq.sub_mem, pow_smul_top_eq] at this
    exact this
  let z' : Fin d → A := fun i => Classical.choose (hlim i)
  have hz' : ∀ i n, g n i - z' i ∈ I ^ n := fun i => Classical.choose_spec (hlim i)
  refine ⟨z', fun i => ?_, ?_⟩
  · have h1 : g 1 i - z' i ∈ I ^ 1 := hz' i 1
    have h2 : g 1 i - g 0 i ∈ I ^ 1 := hgd 0 i
    rw [hg0] at h2
    have := Ideal.sub_mem _ h2 h1
    simpa using this
  · funext i
    rw [← sub_eq_zero]
    refine hB.haus' _ fun k => ?_
    rw [SModEq.sub_mem, sub_zero, pow_smul_top_eq]
    have hd : res (g k) i - res z' i ∈ J ^ k := by
      rw [hres_sub]
      refine Ideal.sub_mem _ (hp k (hz' i k)) ?_
      exact mulVec_mem_of_mem E _ _ (fun j => hq k (hz' j k)) i
    have hr : res (g k) i ∈ J ^ k := Ideal.pow_le_pow_right (by omega) (hgres k i)
    have := Ideal.sub_mem _ hr hd
    simpa [res] using this

theorem lift_solution (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d)
    (B C D : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C) (p q : Hom C D) (hh : Cover h)
    (hpo : IsPO h h p q) (z : Fin d → C.A)
    (hz : ∀ i, p.f (z i) - (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z j)) i ∈ adI D ^ 1) :
    ∃ z' : Fin d → C.A, (∀ i, z' i - z i ∈ adI C ^ 1) ∧
      (fun i => p.f (z' i)) = (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z' j)) :=
  lift_solution_of_step (adI C) (adI D) C.complete.toIsPrecomplete D.complete.toIsHausdorff p.f q.f
    (adI_pow_le p) (adI_pow_le q) _ (GlobalTheory.T.lift_stratifiedSolution_succ_of_cover l K bk d S B C D h f p q hh hpo) z hz

end GlobalTheory.BSP
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDescentSolutionLiftModPrismIdealStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_descent_solution_lift_mod_prism_ideal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C D : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C) (p q : Hom C D), Cover h → IsPO h h p q → ∀ z : Fin d → C.A, (∀ i, p.f (z i) - (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z j)) i ∈ adI D ^ 1) → ∃ z' : Fin d → C.A, (∀ i, z' i - z i ∈ adI C ^ 1) ∧ (fun i => p.f (z' i)) = (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z' j)) := by
  first | exact @GlobalTheory.BSP.lift_solution | exact GlobalTheory.BSP.lift_solution | (intros; apply GlobalTheory.BSP.lift_solution <;> assumption)
end
end
