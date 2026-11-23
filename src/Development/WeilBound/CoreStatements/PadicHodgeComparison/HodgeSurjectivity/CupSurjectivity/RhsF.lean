module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.ProperGenMap
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.CupK
import GroundTheory.PAdicHodge.NormalizedTraceTower
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HarishChandraFormulaStatement
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsDlogFirstChernClass
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DpZeroRight

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.CastTRfl

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem castT_rfl {M : Model l K} {i : ℕ} (x : M.T i) : castT rfl x = x := rfl

theorem dfac {C : Type*} [CommRing C] {m m' : ℕ} (f : Fin m → C) (g : Fin m' → C) (F : Fin m → C) (G : Fin m' → C)
    (z : ℤ) : ∑ s, ∑ s', f s * g s' * (z • (F s * G s')) = (z • ∑ s, f s * F s) * ∑ s', g s' * G s' := by
  rw [Finset.smul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s' _ => ?_
  simp only [zsmul_eq_mul]
  ring

theorem r1 (hC : CupLaws) {M : Model l K} {D : ℕ} (S : Sq M D) {a' n : ℕ} (x : Hdg M.q a' n) {A β T : ℕ}
    (sl : Hdg S.P.q (A + a') (T + n) →ₗ[K] Hdg M.q β n) (ψ : Module.Dual K (Hdg M.q β n))
    {e f i j : ℕ} (hp : e + f = A) (hT : i + j = T) (u : Hdg M.q e i) (v : Hdg M.q f j)
    {a₁₂ ij : ℕ} (h₁ : e + a' = a₁₂) (g₁ : i + n = ij) (h₂ : a₁₂ + f = A + a') (g₂ : ij + j = T + n) :
    th hC S sl ψ (S.pl₁ a' n x) (cupH S.P.q hp hT (S.pl₁ e i u) (S.pl₂ f j v)) =
      ((-1 : ℤ) ^ (j * n)) • ψ (sl (cupH S.P.q h₂ g₂ (S.pl₁ a₁₂ ij (cupH M.q h₁ g₁ u x)) (S.pl₂ f j v))) := by
  have L := hC K S.P.gen S.P.q
  have LM := hC K M.gen M.q
  simp only [th, LinearMap.comp_apply, LinearMap.flip_apply, cupL_apply]
  rw [L.2.1 hp rfl (rfl : f + a' = f + a') (by omega : e + (f + a') = A + a') hT rfl (rfl : j + n = j + n)
    (by omega : i + (j + n) = T + n)]
  rw [L.2.2.1 (rfl : f + a' = f + a') (add_comm a' f) (rfl : j + n = j + n) (add_comm n j)]
  rw [← cupL_apply hC S.P.q (by omega : e + (f + a') = A + a') (by omega : i + (j + n) = T + n), map_zsmul, cupL_apply]
  rw [← L.2.1 h₁ h₂ (add_comm a' f) (by omega) g₁ g₂ (add_comm n j) (by omega)]
  rw [← LM.2.2.2.2.1 S.P.gen S.P.q (Model.genMap S.p₁ S.h₁) (Model.genMap_q S.p₁ S.h₁) h₁ g₁ u x]
  rw [map_zsmul, map_zsmul]

theorem t1 (hC : CupLaws) (P : HTPre l K) {M : Model l K} (hM : M.Sm) {D : ℕ} (S : Sq M D) {a' n : ℕ} (x : Hdg M.q a' n)
    {α β A t : ℕ} (hA : α + β = A + a') (φ' : Module.Dual K (Hdg M.q α t)) (ψ : Module.Dual K (Hdg M.q β n))
    (sl : Hdg S.P.q (A + a') (t + n) →ₗ[K] Hdg M.q β n) (hsl : IsSl S hA φ' sl)
    {i j : ℕ} (X : M.T i) (Y : M.T j) (Z : S.P.T (i + j))
    (hZ : S.P.CupT (Model.pullT S.p₁ S.h₁ i X) (Model.pullT S.p₂ S.h₂ j Y) Z) (hij : i + j = t) :
    P.h S.P A t (S.P.toV t (castT hij Z)) (th hC S sl ψ (S.pl₁ a' n x)) =
      if hj : j = n then kap hC P x φ' X * P.h M β n (M.toV n (castT hj Y)) ψ else 0 := by
  subst hij
  have hfin : ∀ a k, FiniteDimensional K (Hdg M.q a k) := fun a k => (P.fin M hM a k).1
  let b : ∀ a, Module.Basis (Fin (Module.finrank K (Hdg M.q a i))) K (Hdg M.q a i) := fun a => Module.finBasis K _
  let b' : ∀ a, Module.Basis (Fin (Module.finrank K (Hdg M.q a j))) K (Hdg M.q a j) := fun a => Module.finBasis K _
  rw [castT_rfl, cupK P hM S X Y Z hZ b b' A]
  have tz : ∀ p : (Finset.HasAntidiagonal.antidiagonal A : Finset (ℕ × ℕ)), (p.1.1 + a', i + n) ≠ (α, i + j) → ∀ s s',
      th hC S sl ψ (S.pl₁ a' n x) (cupH S.P.q (Finset.HasAntidiagonal.mem_antidiagonal.1 p.2) rfl
        (S.pl₁ p.1.1 i (b p.1.1 s)) (S.pl₂ p.1.2 j (b' p.1.2 s'))) = 0 := by
    intro p hne s s'
    have hp := Finset.HasAntidiagonal.mem_antidiagonal.1 p.2
    rw [r1 hC S x sl ψ _ rfl _ _ rfl rfl (by omega) (by omega), hsl.2 _ _ _ _ _ _ hne, map_zero, smul_zero]
  have allz : (∀ p : (Finset.HasAntidiagonal.antidiagonal A : Finset (ℕ × ℕ)), (p.1.1 + a', i + n) ≠ (α, i + j)) →
      ∑ p : (Finset.HasAntidiagonal.antidiagonal A : Finset (ℕ × ℕ)), ∑ s, ∑ s',
        P.h M p.1.1 i (M.toV _ X) ((b p.1.1).coord s) * P.h M p.1.2 j (M.toV _ Y) ((b' p.1.2).coord s') *
        kC K (th hC S sl ψ (S.pl₁ a' n x) (cupH S.P.q (Finset.HasAntidiagonal.mem_antidiagonal.1 p.2) rfl
          (S.pl₁ p.1.1 i (b p.1.1 s)) (S.pl₂ p.1.2 j (b' p.1.2 s')))) = 0 := fun h =>
    Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun s' _ => by
      rw [tz p (h p) s s', map_zero, mul_zero]
  by_cases hj : j = n
  · subst hj
    rw [dite_eq_left rfl, castT_rfl]
    by_cases hα : a' ≤ α
    · have hmem : (α - a', β) ∈ (Finset.HasAntidiagonal.antidiagonal A : Finset (ℕ × ℕ)) :=
        Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp only; omega)
      rw [Finset.sum_eq_single ⟨(α - a', β), hmem⟩]
      · have key : ∀ s s', th hC S sl ψ (S.pl₁ a' j x) (cupH S.P.q (Finset.HasAntidiagonal.mem_antidiagonal.1 hmem) rfl
            (S.pl₁ (α - a') i (b (α - a') s)) (S.pl₂ β j (b' β s'))) =
            ((-1 : ℤ) ^ (j * j)) • (Fx hC x φ' i (b (α - a') s) * ψ (b' β s')) := by
          intro s s'
          rw [r1 hC S x sl ψ _ rfl _ _ (Nat.sub_add_cancel hα) rfl hA rfl, hsl.1, map_smul, smul_eq_mul]
          rw [Fx, dite_eq_left (And.intro hα rfl)]
          simp only [LinearMap.comp_apply, LinearMap.flip_apply, cupL_apply]
        simp only [key, map_zsmul, map_mul]
        rw [dfac, kap, bsum (kC K) _ (fun k φ => P.lin' M _ _ k _ φ) (b (α - a')), bsum (kC K) _ (fun k φ => P.lin' M _ _ k _ φ) (b' β)]
      · intro p _ hne
        refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun s' _ => ?_
        rw [tz p ?_ s s', map_zero, mul_zero]
        intro h
        have hp := Finset.HasAntidiagonal.mem_antidiagonal.1 p.2
        have h1 : p.1.1 + a' = α := (Prod.ext_iff.1 h).1
        exact hne (Subtype.ext (Prod.ext (by simp only; omega) (by simp only; omega)))
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [allz fun p h => hα (by have := (Prod.ext_iff.1 h).1; simp only at this; omega)]
      simp [kap, Fx, hα]
  · rw [dite_eq_right hj]
    exact allz fun p h => hj (by have := (Prod.ext_iff.1 h).2; simp only at this; omega)

end CrystallineSemistableComparison.Onto

end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.GenPb

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

theorem gen_pb {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M P : Model l K} (p₁ p₂ : P.X ⟶ M.X) (h₁ : p₁ ≫ M.p = P.p) (h₂ : p₂ ≫ M.p = P.p) (hP : IsPullback p₁ p₂ M.p M.p) : IsPullback (Model.genMap p₁ h₁) (Model.genMap p₂ h₂) M.q M.q := by
  have hw : Model.genMap p₁ h₁ ≫ M.q = Model.genMap p₂ h₂ ≫ M.q := by
    rw [Model.genMap_q, Model.genMap_q]
  have hc : pullback.fst M.p (Spec.map (CommRingCat.ofHom (OK l K).subtype)) ≫ M.p =
      M.q ≫ Spec.map (CommRingCat.ofHom (OK l K).subtype) := pullback.condition
  have g1 : ∀ {u : P.X ⟶ M.X} (hu : u ≫ M.p = P.p),
      Model.genMap u hu ≫ pullback.fst M.p (Spec.map (CommRingCat.ofHom (OK l K).subtype)) =
        pullback.fst P.p (Spec.map (CommRingCat.ofHom (OK l K).subtype)) ≫ u := fun hu => by
    unfold Model.genMap
    exact pullback.lift_fst _ _ _
  have g2 : ∀ {u : P.X ⟶ M.X} (hu : u ≫ M.p = P.p),
      Model.genMap u hu ≫ pullback.snd M.p (Spec.map (CommRingCat.ofHom (OK l K).subtype)) =
        pullback.snd P.p (Spec.map (CommRingCat.ofHom (OK l K).subtype)) := fun hu =>
    Model.genMap_q _ hu
  refine IsPullback.of_isLimit (c := PullbackCone.mk _ _ hw) ?_
  refine PullbackCone.IsLimit.mk hw
    (fun s => pullback.lift
      (hP.lift (s.fst ≫ pullback.fst _ _) (s.snd ≫ pullback.fst _ _) (by
        simp only [Category.assoc, hc]
        rw [reassoc_of% s.condition]))
      (s.fst ≫ M.q) (by
        rw [← h₁]
        simp only [← Category.assoc, hP.lift_fst]
        simp only [Category.assoc, hc]))
    (fun s => by
      apply pullback.hom_ext
      · simp only [Category.assoc, g1 h₁, pullback.lift_fst_assoc, hP.lift_fst]
      · simp only [Category.assoc, g2 h₁, pullback.lift_snd])
    (fun s => by
      apply pullback.hom_ext
      · simp only [Category.assoc, g1 h₂, pullback.lift_fst_assoc, hP.lift_snd]
      · simp only [Category.assoc, g2 h₂, pullback.lift_snd]
        exact s.condition)
    (fun s m hm₁ hm₂ => by
      apply pullback.hom_ext
      · rw [pullback.lift_fst]
        apply hP.hom_ext
        · rw [hP.lift_fst, Category.assoc, ← g1 h₁, ← Category.assoc, hm₁]
        · rw [hP.lift_snd, Category.assoc, ← g1 h₂, ← Category.assoc, hm₂]
      · rw [pullback.lift_snd, ← hm₁, Category.assoc, g2 h₁])

end CrystallineSemistableComparison.Onto

end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.T2a

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem t2z (hC : CupLaws) (P : HTPre l K) {M : Model l K} (hM : M.Sm) {D : ℕ} (S : Sq M D) {a' n : ℕ} (x : Hdg M.q a' n)
    {α β A t : ℕ} (hA : α + β = A + a') (φ' : Module.Dual K (Hdg M.q α t)) (ψ : Module.Dual K (Hdg M.q β n))
    (sl : Hdg S.P.q (A + a') (t + n) →ₗ[K] Hdg M.q β n) (hsl : IsSl S hA φ' sl)
    (X : M.T t) (Y : M.T 0) (Z : S.P.T (t + 0))
    (hZ : S.P.CupT (Model.pullT S.p₁ S.h₁ t X) (Model.pullT S.p₂ S.h₂ 0 Y) Z) :
    P.h S.P A t (S.P.toV t Z) (th hC S sl ψ (S.pl₂ a' n x)) =
      P.h M α t (M.toV t X) φ' * P.h M 0 0 (M.toV 0 Y) (Gx hC x ψ) := by
  classical
  have hfin : ∀ a n, FiniteDimensional K (Hdg M.q a n) := fun a n => (P.fin M hM a n).1
  have assoc : ∀ {a1 a2 i1 j1 a23 jk : ℕ} (h12 : a1 + a2 = A) (g12 : i1 + j1 = t) (h3 : a2 + a' = a23)
      (g3 : j1 + n = jk) (u : Hdg M.q a1 i1) (v : Hdg M.q a2 j1),
      th hC S sl ψ (S.pl₂ a' n x) (cupH S.P.q h12 g12 (S.pl₁ a1 i1 u) (S.pl₂ a2 j1 v)) =
        ψ (sl (cupH S.P.q (by omega : a1 + a23 = A + a') (by omega : i1 + jk = t + n) (S.pl₁ a1 i1 u)
          (S.pl₂ a23 jk (cupH M.q h3 g3 v x)))) := by
    intro a1 a2 i1 j1 a23 jk h12 g12 h3 g3 u v
    simp only [th, LinearMap.comp_apply, LinearMap.flip_apply, cupL_apply]
    rw [(hC K S.P.gen S.P.q).2.1 h12 (by omega) h3 (by omega) g12 (by omega) g3 (by omega),
      ← (hC K M.gen M.q).2.2.2.2.1 S.P.gen S.P.q (Model.genMap S.p₂ S.h₂) (Model.genMap_q S.p₂ S.h₂) h3 g3 v x]
  refine (cupK P hM S X Y Z hZ (fun a => Module.finBasis K (Hdg M.q a t))
    (fun a => Module.finBasis K (Hdg M.q a 0)) A _).trans ?_
  rw [Fintype.sum_eq_single (⟨(A, 0), by simp⟩ : (Finset.HasAntidiagonal.antidiagonal A : Finset (ℕ × ℕ)))]
  swap
  · rintro ⟨⟨p1, p2⟩, hm⟩ hp
    have hm' : p1 + p2 = A := Finset.HasAntidiagonal.mem_antidiagonal.1 hm
    have h2 : 0 < p2 := by
      rcases Nat.eq_zero_or_pos p2 with h0 | h0
      · exact absurd (by simp only [Subtype.mk.injEq, Prod.mk.injEq]; exact ⟨by omega, h0⟩) hp
      · exact h0
    dsimp only
    have hsub : Subsingleton (Hdg M.q p2 0) := (P.fin M hM p2 0).2 h2
    refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun s' _ => ?_
    exact absurd (Subsingleton.elim _ _) ((Module.finBasis K (Hdg M.q p2 0)).ne_zero s')
  dsimp only
  by_cases hAα : A = α
  · subst hAα
    obtain rfl : β = a' := by omega
    have hG : ∀ v : Hdg M.q 0 0, Gx hC x ψ v = ψ (cupH M.q (Nat.zero_add β) (Nat.zero_add n) v x) := by
      intro v
      unfold Gx
      rw [dite_eq_left (Nat.zero_add β)]
      simp only [LinearMap.comp_apply, LinearMap.flip_apply, cupL_apply]
    have hterm : ∀ (s : Fin (Module.finrank K (Hdg M.q A t))) (s' : Fin (Module.finrank K (Hdg M.q 0 0))),
        th hC S sl ψ (S.pl₂ β n x) (cupH S.P.q (Nat.add_zero A) rfl (S.pl₁ A t (Module.finBasis K (Hdg M.q A t) s))
          (S.pl₂ 0 0 (Module.finBasis K (Hdg M.q 0 0) s'))) =
        φ' (Module.finBasis K (Hdg M.q A t) s) * Gx hC x ψ (Module.finBasis K (Hdg M.q 0 0) s') := by
      intro s s'
      rw [assoc (Nat.add_zero A) rfl (Nat.zero_add β) (Nat.zero_add n), hsl.1, map_smul, smul_eq_mul, hG]
    rw [← bsum (kC K) (P.h M A t (M.toV t X)) (fun k φ => P.lin' M A t k _ φ) (Module.finBasis K (Hdg M.q A t)) φ',
      ← bsum (kC K) (P.h M 0 0 (M.toV 0 Y)) (fun k φ => P.lin' M 0 0 k _ φ) (Module.finBasis K (Hdg M.q 0 0)) (Gx hC x ψ),
      Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
    erw [hterm s s']
    rw [map_mul]
    ring
  · have hG0 : Gx hC x ψ = 0 := by
      unfold Gx
      rw [dite_eq_right (show ¬ (0 + a' = β) by omega)]
    simp only [hG0, map_zero, mul_zero]
    refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun s' _ => ?_
    erw [assoc (i1 := t) (j1 := 0) (Nat.add_zero A) (Nat.add_zero t) rfl rfl,
      hsl.2 A t (0 + a') (0 + n) _ _ (fun h => hAα (congrArg Prod.fst h))]
    simp only [map_zero, mul_zero]

theorem t2a (hC : CupLaws) (P : HTPre l K) {M : Model l K} (hM : M.Sm) {D : ℕ} (S : Sq M D) {a' n : ℕ} (x : Hdg M.q a' n)
    {α β A t : ℕ} (hA : α + β = A + a') (φ' : Module.Dual K (Hdg M.q α t)) (ψ : Module.Dual K (Hdg M.q β n))
    (sl : Hdg S.P.q (A + a') (t + n) →ₗ[K] Hdg M.q β n) (hsl : IsSl S hA φ' sl)
    {i j : ℕ} (X : M.T i) (Y : M.T j) (Z : S.P.T (i + j))
    (hZ : S.P.CupT (Model.pullT S.p₁ S.h₁ i X) (Model.pullT S.p₂ S.h₂ j Y) Z) (hij : i + j = t) (hj : j ≠ 0) :
    P.h S.P A t (S.P.toV t (castT hij Z)) (th hC S sl ψ (S.pl₂ a' n x)) = 0 := by
  classical
  have hfin : ∀ a n, FiniteDimensional K (Hdg M.q a n) := fun a n => (P.fin M hM a n).1
  subst hij
  have assoc : ∀ {a1 a2 i1 j1 a23 jk : ℕ} (h12 : a1 + a2 = A) (g12 : i1 + j1 = (i + j)) (h3 : a2 + a' = a23)
      (g3 : j1 + n = jk) (u : Hdg M.q a1 i1) (v : Hdg M.q a2 j1),
      th hC S sl ψ (S.pl₂ a' n x) (cupH S.P.q h12 g12 (S.pl₁ a1 i1 u) (S.pl₂ a2 j1 v)) =
        ψ (sl (cupH S.P.q (by omega : a1 + a23 = A + a') (by omega : i1 + jk = (i + j) + n) (S.pl₁ a1 i1 u)
          (S.pl₂ a23 jk (cupH M.q h3 g3 v x)))) := by
    intro a1 a2 i1 j1 a23 jk h12 g12 h3 g3 u v
    simp only [th, LinearMap.comp_apply, LinearMap.flip_apply, cupL_apply]
    rw [(hC K S.P.gen S.P.q).2.1 h12 (by omega) h3 (by omega) g12 (by omega) g3 (by omega),
      ← (hC K M.gen M.q).2.2.2.2.1 S.P.gen S.P.q (Model.genMap S.p₂ S.h₂) (Model.genMap_q S.p₂ S.h₂) h3 g3 v x]
  refine (cupK P hM S X Y Z hZ (fun a => Module.finBasis K (Hdg M.q a i))
    (fun a => Module.finBasis K (Hdg M.q a j)) A _).trans ?_
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun s' _ => ?_
  have hm : p.1.1 + p.1.2 = A := Finset.HasAntidiagonal.mem_antidiagonal.1 p.2
  rw [assoc hm rfl rfl rfl, hsl.2 p.1.1 i (p.1.2 + a') (j + n) (by omega) (by omega)
    (fun h => hj (by have := congrArg Prod.snd h; dsimp only at this; omega))]
  simp only [map_zero, mul_zero]

end CrystallineSemistableComparison.Onto

end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.RhsF

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem eid (hC : CupLaws) (hS : Slant) (P : HTPre l K) {M : Model l K} (hM : M.Sm) {d : ℕ} (Dt : Dat hC P M d)
    {a' n : ℕ} (x : Hdg M.q a' n) {α : ℕ} (φ' : Module.Dual K (Hdg M.q α (2 + 2 * d))) :
    lhsF hC P Dt x φ' = rhsF hC P Dt x φ' := by
  funext β ψ
  have hL : lhsF hC P Dt x φ' β ψ =
      (∑ s, if h : 0 = n then kap hC P x φ' (Dt.a₀ s) * P.h M β n (M.toV n (castT h (Dt.b₀ s))) ψ else 0) +
      ∑ s, if h : Dt.j s = n then kap hC P x φ' (Dt.a s) * P.h M β n (M.toV n (castT h (Dt.b s))) ψ else 0 := by
    simp only [lhsF, Pi.add_apply, Finset.sum_apply]
    congr 1 <;> refine Finset.sum_congr rfl fun s _ => ?_ <;> split_ifs <;> rfl
  rw [hL]
  simp only [rhsF]
  by_cases hlt : a' ≤ α + β
  · obtain ⟨A, hA⟩ : ∃ A, α + β = A + a' := ⟨α + β - a', by omega⟩
    have hPM := sm_gen hM
    have := hPM.1
    have := hPM.2
    obtain ⟨sl, hsl⟩ := slantR hS K M.gen M.gen Dt.S.P.gen M.q M.q (Model.genMap Dt.S.p₁ Dt.S.h₁)
      (Model.genMap Dt.S.p₂ Dt.S.h₂) (gen_pb _ _ _ _ Dt.S.prod) Dt.S.P.q (Model.genMap_q _ _) (Model.genMap_q _ _)
      α (2 + 2 * d) β n (A + a') (2 + 2 * d + n) hA rfl φ'
    have hsl' : IsSl Dt.S hA φ' sl := hsl
    have hy : pullH (Model.genMap Dt.S.Δ Dt.S.hΔ) (Model.genMap_q Dt.S.Δ Dt.S.hΔ) a' n
        (Dt.S.pl₁ a' n x - Dt.S.pl₂ a' n x) = 0 := by
      rw [map_sub, sub_eq_zero]
      have c7 := (hC K M.gen M.q).2.2.2.2.2.2
      rw [c7 _ _ _ _ _ _ _ _ (𝟙 _) (Category.id_comp _) (gen_sec _ _ _ _ Dt.S.Δ₁) a' n x,
        c7 _ _ _ _ _ _ _ _ (𝟙 _) (Category.id_comp _) (gen_sec _ _ _ _ Dt.S.Δ₂) a' n x]
    have hk := Dt.kill A a' n _ hy (ψ ∘ₗ sl)
    have split : (ψ ∘ₗ sl) ∘ₗ (cupL hC Dt.S.P.q (a := A) (a' := a') (i := 2 + 2 * d) (j := n) rfl rfl).flip
        (Dt.S.pl₁ a' n x - Dt.S.pl₂ a' n x) = th hC Dt.S sl ψ (Dt.S.pl₁ a' n x) - th hC Dt.S sl ψ (Dt.S.pl₂ a' n x) := by
      ext C
      simp [th]
    rw [split, map_sub, sub_eq_zero, Dt.dec] at hk

    simp only [map_add (f := _), map_sum, AddMonoidHom.add_apply, AddMonoidHom.finsetSum_apply] at hk
    have e1 : ∀ s, P.h Dt.S.P A (2 + 2 * d) (Dt.S.P.toV (2 + 2 * d) (Dt.ab₀ s)) (th hC Dt.S sl ψ (Dt.S.pl₁ a' n x)) =
        if h : 0 = n then kap hC P x φ' (Dt.a₀ s) * P.h M β n (M.toV n (castT h (Dt.b₀ s))) ψ else 0 :=
      fun s => t1 hC P hM Dt.S x hA φ' ψ sl hsl' (Dt.a₀ s) (Dt.b₀ s) (Dt.ab₀ s) (Dt.cup₀ s) rfl
    have e2 : ∀ s, P.h Dt.S.P A (2 + 2 * d) (Dt.S.P.toV (2 + 2 * d) (castT (Dt.hij s) (Dt.ab s)))
        (th hC Dt.S sl ψ (Dt.S.pl₁ a' n x)) =
        if h : Dt.j s = n then kap hC P x φ' (Dt.a s) * P.h M β n (M.toV n (castT h (Dt.b s))) ψ else 0 :=
      fun s => t1 hC P hM Dt.S x hA φ' ψ sl hsl' (Dt.a s) (Dt.b s) (Dt.ab s) (Dt.cup s) (Dt.hij s)
    have f1 : ∀ s, P.h Dt.S.P A (2 + 2 * d) (Dt.S.P.toV (2 + 2 * d) (Dt.ab₀ s)) (th hC Dt.S sl ψ (Dt.S.pl₂ a' n x)) =
        P.h M α _ (M.toV _ (Dt.a₀ s)) φ' * P.h M 0 0 (M.toV 0 (Dt.b₀ s)) (Gx hC x ψ) :=
      fun s => t2z hC P hM Dt.S x hA φ' ψ sl hsl' (Dt.a₀ s) (Dt.b₀ s) (Dt.ab₀ s) (Dt.cup₀ s)
    have f2 : ∀ s, P.h Dt.S.P A (2 + 2 * d) (Dt.S.P.toV (2 + 2 * d) (castT (Dt.hij s) (Dt.ab s)))
        (th hC Dt.S sl ψ (Dt.S.pl₂ a' n x)) = 0 :=
      fun s => t2a hC P hM Dt.S x hA φ' ψ sl hsl' (Dt.a s) (Dt.b s) (Dt.ab s) (Dt.cup s) (Dt.hij s) (Dt.jne s)
    simp only [e1, e2, f1, f2, Finset.sum_const_zero, add_zero] at hk
    exact hk
  · have hk : ∀ {i : ℕ} (X : M.T i), kap hC P x φ' X = 0 := by
      intro i X
      rw [kap, Fx, dite_eq_right (fun h => hlt (by omega)), map_zero, smul_zero]
    have hg : Gx hC x ψ = 0 := by
      rw [Gx, dite_eq_right (by omega)]
    simp only [hk, hg, zero_mul, map_zero, mul_zero, dite_eq_ite, ite_self, Finset.sum_const_zero, add_zero]

end CrystallineSemistableComparison.Onto

end
end
end
