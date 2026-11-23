module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FirstChernCoboundary
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosievePairingFamilyCompatStatement
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingIsoOfComponentIsosStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingRestrictCompatStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictSelfPullCEqStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethOfRestrictBijectiveStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethProductLocalGlobalStatement
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethSwap

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.KunGlue

universe w

variable {K : Type} [Field K]

abbrev Idx.swap {c n : ℕ} (t : Idx c n) : Idx c n :=
  ⟨t.a', t.j, t.a, t.i, by have := t.ha; omega, by have := t.h; omega⟩

def swapSum (P Q : ℕ → Cx.{w} K) (c n : ℕ) :
    (⨁ t : Idx c n, (P t.a).H t.i ⊗[K] (Q t.a').H t.j) →ₗ[K]
      (⨁ t : Idx c n, (Q t.a).H t.i ⊗[K] (P t.a').H t.j) :=
  DirectSum.toModule K _ _ fun t =>
    ((-1 : ℤ) ^ (t.i * t.j)) •
      ((DirectSum.lof K _ (fun t : Idx c n => (Q t.a).H t.i ⊗[K] (P t.a').H t.j) t.swap).comp
        (TensorProduct.comm K ((P t.a).H t.i) ((Q t.a').H t.j)).toLinearMap)

theorem swapSum_lof (P Q : ℕ → Cx.{w} K) (c n : ℕ) (t : Idx c n) (u : (P t.a).H t.i) (v : (Q t.a').H t.j) :
    swapSum P Q c n (DirectSum.lof K _ (fun t : Idx c n => (P t.a).H t.i ⊗[K] (Q t.a').H t.j) t (u ⊗ₜ v)) =
      ((-1 : ℤ) ^ (t.i * t.j)) •
        DirectSum.lof K _ (fun t : Idx c n => (Q t.a).H t.i ⊗[K] (P t.a').H t.j) t.swap (v ⊗ₜ u) := by
  unfold swapSum
  rw [DirectSum.toModule_lof]
  rfl

theorem swapSum_swapSum (P Q : ℕ → Cx.{w} K) (c n : ℕ) (z) :
    swapSum Q P c n (swapSum P Q c n z) = z := by
  have key : (swapSum Q P c n).comp (swapSum P Q c n) = LinearMap.id := by
    refine DirectSum.linearMap_ext K fun t => TensorProduct.ext' fun u v => ?_
    simp only [LinearMap.comp_apply, LinearMap.id_apply, swapSum_lof, map_zsmul]
    have hs : ((-1 : ℤ) ^ (t.i * t.j)) * ((-1 : ℤ) ^ (t.swap.i * t.swap.j)) = 1 := by
      change ((-1 : ℤ) ^ (t.i * t.j)) * ((-1 : ℤ) ^ (t.j * t.i)) = 1
      rw [Nat.mul_comm t.j t.i, ← mul_pow]
      simp
    refine (congrArg (fun w => ((-1 : ℤ) ^ (t.i * t.j)) • w) (swapSum_lof Q P c n t.swap v u)).trans ?_
    dsimp only
    rw [smul_smul, hs, one_smul]
  exact LinearMap.congr_fun key z

theorem kunE_swap {P Q T : ℕ → Cx.{1} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)) (h : KunE pr) :
    KunE (P := Q) (Q := P) (T := T) (fun {a a' c} ha => swapPr pr ha) := by
  intro c n
  obtain ⟨e, he⟩ := h c n
  let σ : (⨁ t : Idx c n, (Q t.a).H t.i ⊗[K] (P t.a').H t.j) ≃ₗ[K]
      (⨁ t : Idx c n, (P t.a).H t.i ⊗[K] (Q t.a').H t.j) :=
    LinearEquiv.ofLinear (swapSum Q P c n) (swapSum P Q c n)
      (LinearMap.ext fun z => swapSum_swapSum P Q c n z) (LinearMap.ext fun z => swapSum_swapSum Q P c n z)
  refine ⟨σ.trans e, fun t x y hx hy hz => ?_⟩
  have hz' : (T c).d n ((pr (show t.a' + t.a = c by have := t.ha; omega)).μ (show t.j + t.i = n by have := t.h; omega) y x) = 0 := by
    have e0 := (pr (show t.a' + t.a = c by have := t.ha; omega)).leib (show t.j + t.i = n by have := t.h; omega) y x
    rw [e0, hx, hy]
    simp
  have e1 := he t.swap y x hy hx hz'
  change e (swapSum Q P c n (DirectSum.lof K _ (fun t : Idx c n => (Q t.a).H t.i ⊗[K] (P t.a').H t.j) t
    ((Q t.a).cls x hx ⊗ₜ (P t.a').cls y hy))) = _
  rw [swapSum_lof]
  change e.toLinearMap (((-1 : ℤ) ^ (t.i * t.j)) •
    DirectSum.lof K _ (fun t : Idx c n => (P t.a).H t.i ⊗[K] (Q t.a').H t.j) t.swap
      ((P t.a').cls y hy ⊗ₜ (Q t.a).cls x hx)) = _
  rw [map_zsmul e.toLinearMap]
  refine (congrArg _ e1).trans ?_
  rfl

end GlobalTheory.CompanionTheory.KunGlue
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethSwapStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

theorem _root_.GlobalTheory.T.kuenneth_swap : ∀ {K : Type} [Field K] {P Q T : ℕ → Cx.{1} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)), KunE pr → KunE (P := Q) (Q := P) (T := T) (fun {a a' c} ha => swapPr pr ha) := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.kunE_swap | exact GlobalTheory.CompanionTheory.KunGlue.kunE_swap | (intros; apply GlobalTheory.CompanionTheory.KunGlue.kunE_swap <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethMayerVietorisRight

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue

theorem mapH_id_bij {K : Type} [Field K] (C : Cx.{1} K) (n : ℕ) :
    Function.Bijective ((Cx.Hom.id C).mapH n) := by
  have h : ∀ x : C.H n, (Cx.Hom.id C).mapH n x = x := by
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  exact ⟨fun x y e => by simpa only [h] using e, fun y => ⟨y, h y⟩⟩

theorem swapPr_swapPr_apply {K : Type} [Field K] {P Q T : ℕ → Cx.{1} K}
    (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)) {a a' c : ℕ} (ha : a + a' = c)
    {i j n : ℕ} (h : i + j = n) (x : (P a).X i) (y : (Q a').X j) :
    (swapPr (P := Q) (Q := P) (T := T) (fun {a a' c} ha => swapPr pr ha) ha).μ h x y = (pr ha).μ h x y := by
  simp only [swapPr, LinearMap.smul_apply, LinearMap.flip_apply, smul_smul]
  have s : ((-1 : ℤ) ^ (i * j) * (-1) ^ (j * i)) = 1 := by
    rw [mul_comm j i, ← mul_pow]
    simp
  rw [s, one_smul]

theorem glue_l : MVBij → CovDesc → ∀ {K : Type} [Field K] (E : XD K) (U₂ : ObjectProperty E.C₂) {ι : Type} [DecidableEq ι] [Fintype ι] (V : ι → ObjectProperty E.C₁) (W : ι → ObjectProperty E.D), (∀ α, Cosieve (V α)) → (∀ α, Cosieve (W α)) → ∀ (h₁ : ∀ S : Finset ι, ∀ T, capU W S T → capU V S (E.L₁.obj T)) (h₂ : ∀ S : Finset ι, ∀ T, capU W S T → U₂ (E.L₂.obj T)), (∀ S : Finset ι, S.Nonempty → E.Kun (capU V S) U₂ (capU W S) (h₁ S) (h₂ S)) → E.Kun (capU V ∅) U₂ (capU W ∅) (h₁ ∅) (h₂ ∅) := by
  intro hMV hCD K _ E U₂ ι _ _ V W hV hW h₁ h₂ hK
  let Rel : ObjectProperty E.C₁ → ObjectProperty E.D → Prop := fun U U' =>
    (∀ T, U' T → U (E.L₁.obj T)) ∧ (∀ T, U' T → U₂ (E.L₂.obj T))
  let prr : ∀ (U : ObjectProperty E.C₁) (U' : ObjectProperty E.D), Rel U U' → ∀ {a a' c : ℕ}, a + a' = c →
      CxPairing (CH.cx (U₂.ι ⋙ E.F₂ a)) (CH.cx (U.ι ⋙ E.F₁ a')) (CH.cx (U'.ι ⋙ E.F₃ c)) :=
    fun U U' r {a a' c} ha =>
      swapPr (P := fun a => CH.cx (U.ι ⋙ E.F₁ a)) (Q := fun a => CH.cx (U₂.ι ⋙ E.F₂ a))
        (T := fun c => CH.cx (U'.ι ⋙ E.F₃ c)) (fun {a a' c} ha => E.pr U U₂ U' r.1 r.2 ha) ha
  have hnat : ∀ {U₁ U₂' : ObjectProperty E.C₁} {U₁' U₂'' : ObjectProperty E.D} (r₁ : Rel U₁ U₁') (r₂ : Rel U₂' U₂'')
      (k : U₂' ≤ U₁) (k' : U₂'' ≤ U₁') {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (hn : i + j = n)
      (x : (CH.cx (U₂.ι ⋙ E.F₂ a)).X i) (y : CH.Cn (U₁.ι ⋙ E.F₁ a') j),
      (resU (E.F₃ c) k').pullC n ((prr U₁ U₁' r₁ ha).μ hn x y) = (prr U₂' U₂'' r₂ ha).μ hn x ((resU (E.F₁ a') k).pullC j y) := by
    intro U₁ U₂' U₁' U₂'' r₁ r₂ k k' a a' c ha i j n hn x y
    simp only [prr, swapPr, LinearMap.smul_apply, LinearMap.flip_apply, map_zsmul]
    rw [GlobalTheory.T.pairing_restrict_compat E r₁.1 r₁.2 r₂.1 r₂.2 k (le_refl U₂) k' (show a' + a = c by omega) (show j + i = n by omega) y x,
      GlobalTheory.T.restrict_self_pullC_eq (E.F₂ a) U₂ (le_refl U₂) i x]
  have key := GlobalTheory.T.cosieve_pairing_family_compat hMV hCD E.F₁ E.F₃ (fun a => CH.cx (U₂.ι ⋙ E.F₂ a)) Rel prr hnat V W hV hW
    (fun S => ⟨h₁ S, h₂ S⟩) (fun S hS => GlobalTheory.T.kuenneth_swap _ (hK S hS))
  have k2 := GlobalTheory.T.kuenneth_swap _ key
  refine (GlobalTheory.T.pairing_iso_of_component_isos _ _ (fun a => Cx.Hom.id _) (fun a => Cx.Hom.id _) (fun a => Cx.Hom.id _)
    (fun a n => mapH_id_bij _ n) (fun a n => mapH_id_bij _ n) (fun a n => mapH_id_bij _ n) ?_).1 k2
  intro a a' c ha i j n h x y
  exact swapPr_swapPr_apply (P := fun a => CH.cx ((capU V ∅).ι ⋙ E.F₁ a)) (Q := fun a => CH.cx (U₂.ι ⋙ E.F₂ a))
    (T := fun c => CH.cx ((capU W ∅).ι ⋙ E.F₃ c)) (fun {a a' c} ha => E.pr (capU V ∅) U₂ (capU W ∅) (h₁ ∅) (h₂ ∅) ha) ha h x y

end GlobalTheory.CompanionTheory.KunGlue
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethMayerVietorisRightStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

theorem _root_.GlobalTheory.T.kuenneth_mayer_vietoris_right : MVBij → CovDesc → ∀ {K : Type} [Field K] (E : XD K) (U₂ : ObjectProperty E.C₂) {ι : Type} [DecidableEq ι] [Fintype ι] (V : ι → ObjectProperty E.C₁) (W : ι → ObjectProperty E.D), (∀ α, Cosieve (V α)) → (∀ α, Cosieve (W α)) → ∀ (h₁ : ∀ S : Finset ι, ∀ T, capU W S T → capU V S (E.L₁.obj T)) (h₂ : ∀ S : Finset ι, ∀ T, capU W S T → U₂ (E.L₂.obj T)), (∀ S : Finset ι, S.Nonempty → E.Kun (capU V S) U₂ (capU W S) (h₁ S) (h₂ S)) → E.Kun (capU V ∅) U₂ (capU W ∅) (h₁ ∅) (h₂ ∅) := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.glue_l | exact GlobalTheory.CompanionTheory.KunGlue.glue_l | (intros; apply GlobalTheory.CompanionTheory.KunGlue.glue_l <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethProductProperSmooth

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue

theorem resU_self_bij {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R)
    (U : ObjectProperty C) (k : U ≤ U) (n : ℕ) : Function.Bijective ((resU F k).pull n) := by
  have h : ∀ x, (resU F k).pull n x = x := by
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  exact ⟨fun x y e => by simpa only [h] using e, fun y => ⟨y, h y⟩⟩

theorem resU_bij_congr {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R)
    {U V V' : ObjectProperty C} (e : V = V') (k : V ≤ U) (k' : V' ≤ U) (n : ℕ)
    (h : Function.Bijective ((resU F k').pull n)) : Function.Bijective ((resU F k).pull n) := by
  subst e
  exact h

theorem kun_congr {K : Type} [Field K] (E : XD K) {U₁ U₁' : ObjectProperty E.C₁} {U₂ : ObjectProperty E.C₂}
    {U₃ U₃' : ObjectProperty E.D} (e₁ : U₁ = U₁') (e₃ : U₃ = U₃')
    (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T))
    (h₁' : ∀ T, U₃' T → U₁' (E.L₁.obj T)) (h₂' : ∀ T, U₃' T → U₂ (E.L₂.obj T))
    (h : E.Kun U₁ U₂ U₃ h₁ h₂) : E.Kun U₁' U₂ U₃' h₁' h₂' := by
  subst e₁ e₃
  exact h

theorem glue_top (hMV : MVBij) (hCD : CovDesc) {K : Type} [Field K] (E : XD K) (U₁ : ObjectProperty E.C₁)
    (U₂ : ObjectProperty E.C₂) (U₃ : ObjectProperty E.D) {ι : Type} [DecidableEq ι] [Fintype ι]
    (V : ι → ObjectProperty E.C₁) (W : ι → ObjectProperty E.D) (hV : ∀ α, Cosieve (V α)) (hW : ∀ α, Cosieve (W α))
    (h₁ : ∀ S : Finset ι, ∀ T, capU W S T → capU V S (E.L₁.obj T))
    (h₂ : ∀ S : Finset ι, ∀ T, capU W S T → U₂ (E.L₂.obj T))
    (hK : ∀ S : Finset ι, S.Nonempty → E.Kun (capU V S) U₂ (capU W S) (h₁ S) (h₂ S))
    (k₁ : capU V ∅ ≤ U₁) (k₃ : capU W ∅ ≤ U₃)
    (b₁ : ∀ a n, Function.Bijective ((resU (E.F₁ a) k₁).pull n))
    (b₃ : ∀ a n, Function.Bijective ((resU (E.F₃ a) k₃).pull n))
    (g₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (g₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) : E.Kun U₁ U₂ U₃ g₁ g₂ :=
  (GlobalTheory.T.kuenneth_of_restrict_bijective E g₁ g₂ (h₁ ∅) (h₂ ∅) k₁ (le_refl U₂) k₃ b₁ (fun a n => resU_self_bij _ _ _ n) b₃).2
    (GlobalTheory.T.kuenneth_mayer_vietoris_right hMV hCD E U₂ V W hV hW h₁ h₂ hK)

section Site

variable {K : Type} [CommRing K] {Z Y : Scheme.{0}}

theorem inU_pull (hS : SiteLaws) (q : Z ⟶ Spec (CommRingCat.of K)) {r : Y ⟶ Spec (CommRingCat.of K)} (u : Y ⟶ Z)
    (hu : u ≫ q = r) (A : Z.Opens) (T) : inU r (u ⁻¹ᵁ A) T ↔ inU q A ((smS u hu).G.obj T) := by
  subst hu
  exact (hS K Z Z Y q (𝟙 Z) u).2.2.2.2.1 A T

theorem inU_cos (hS : SiteLaws) (q : Z ⟶ Spec (CommRingCat.of K)) (A : Z.Opens) : Cosieve (inU q A) :=
  (hS K Z Z Z q (𝟙 Z) (𝟙 Z)).1 A

theorem inU_top (hS : SiteLaws) (q : Z ⟶ Spec (CommRingCat.of K)) (T) : inU q ⊤ T :=
  (hS K Z Z Z q (𝟙 Z) (𝟙 Z)).2.2.1 T

theorem inU_inf (hS : SiteLaws) (q : Z ⟶ Spec (CommRingCat.of K)) (A B : Z.Opens) (T) :
    inU q (A ⊓ B) T ↔ inU q A T ∧ inU q B T :=
  (hS K Z Z Z q (𝟙 Z) (𝟙 Z)).2.2.2.1 A B T

theorem inU_biInf (hS : SiteLaws) (q : Z ⟶ Spec (CommRingCat.of K)) {ι : Type} [DecidableEq ι] (A : ι → Z.Opens)
    (S : Finset ι) (T) : inU q (⨅ α ∈ S, A α) T ↔ ∀ α ∈ S, inU q (A α) T := by
  induction S using Finset.induction_on with
  | empty => simpa using inU_top hS q T
  | insert a S _ ih =>
    rw [Finset.iInf_insert, inU_inf hS, ih]
    simp

end Site

theorem kun_left : SiteLaws → MVBij → CovDesc → ZarAbs → AffOm → KunAff → ∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) [IsProper q] [Smooth q] [IsProper q'] [Smooth q'] (p₁ : P ⟶ X) (p₂ : P ⟶ X') (hP : IsPullback p₁ p₂ q q'), ∀ (h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T)) (h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q' ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T)), (hodgeXD q q' p₁ p₂ hP.w.symm).Kun (inU q ⊤) (inU q' ⊤) (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤)) h₁ h₂ := by
  intro hS hMV hCD hZ hA hKA K _ _ X X' P q q' _ _ _ _ p₁ p₂ hP g₁ g₂
  classical
  obtain ⟨U⟩ := (cov_ex q).1 inferInstance
  have hw := hP.w.symm
  have inP : ∀ (A : X.Opens) (B : X'.Opens) (T),
      inU (p₁ ≫ q) (p₁ ⁻¹ᵁ A ⊓ p₂ ⁻¹ᵁ B) T ↔
        inU q A ((hodgeXD q q' p₁ p₂ hw).L₁.obj T) ∧ inU q' B ((hodgeXD q q' p₁ p₂ hw).L₂.obj T) := by
    intro A B T
    rw [inU_inf hS, inU_pull hS q p₁ rfl, inU_pull hS q' p₂ hw]
    rfl
  let V : U.ι → ObjectProperty (hodgeXD q q' p₁ p₂ hw).C₁ := fun α => inU q (U.U α)
  let W : U.ι → ObjectProperty (hodgeXD q q' p₁ p₂ hw).D := fun α => inU (p₁ ≫ q) (p₁ ⁻¹ᵁ U.U α ⊓ p₂ ⁻¹ᵁ ⊤)
  have h₁ : ∀ S : Finset U.ι, ∀ T, capU W S T → capU V S ((hodgeXD q q' p₁ p₂ hw).L₁.obj T) := by
    rintro S T ⟨⟨α, hα⟩, h⟩
    exact ⟨⟨α, ((inP _ _ T).1 hα).1⟩, fun β hβ => ((inP _ _ T).1 (h β hβ)).1⟩
  have h₂ : ∀ S : Finset U.ι, ∀ T, capU W S T → inU q' ⊤ ((hodgeXD q q' p₁ p₂ hw).L₂.obj T) :=
    fun S T _ => inU_top hS q' _
  have eV : ∀ S : Finset U.ι, S.Nonempty → inU q (⨅ α ∈ S, U.U α) = capU V S := by
    rintro S ⟨α₀, h₀⟩
    funext T
    refine propext ((inU_biInf hS q U.U S T).trans ⟨fun h => ⟨⟨α₀, h α₀ h₀⟩, h⟩, fun h => h.2⟩)
  have eW : ∀ S : Finset U.ι, S.Nonempty →
      inU (p₁ ≫ q) (p₁ ⁻¹ᵁ (⨅ α ∈ S, U.U α) ⊓ p₂ ⁻¹ᵁ ⊤) = capU W S := by
    rintro S ⟨α₀, h₀⟩
    funext T
    refine propext ((inP _ _ T).trans ⟨fun h => ?_, fun h => ?_⟩)
    · have a : ∀ α ∈ S, W α T := fun α hα =>
        (inP _ _ T).2 ⟨(inU_biInf hS q U.U S _).1 h.1 α hα, h.2⟩
      exact ⟨⟨α₀, a α₀ h₀⟩, a⟩
    · exact ⟨(inU_biInf hS q U.U S _).2 fun α hα => ((inP _ _ T).1 (h.2 α hα)).1, inU_top hS q' _⟩
  have hK : ∀ S : Finset U.ι, S.Nonempty →
      (hodgeXD q q' p₁ p₂ hw).Kun (capU V S) (inU q' ⊤) (capU W S) (h₁ S) (h₂ S) := by
    intro S hSn
    obtain ⟨α₀, h₀⟩ := id hSn
    obtain ⟨c, -⟩ := coord_res (U.c α₀) (iInf₂_le α₀ h₀) (U.inter S hSn)
    exact kun_congr _ (eV S hSn) (eW S hSn) _ _ _ _
      (GlobalTheory.T.kuenneth_product_local_global hS hMV hCD hZ hA hKA K X X' P q q' p₁ p₂ hP _ _ ⟨c⟩
        (fun T h => ((inP _ _ T).1 h).1) (fun T h => ((inP _ _ T).1 h).2))
  have e₁ : capU V ∅ = fun T => ∃ α, inU q (U.U α) T := by
    funext T
    exact propext ⟨fun h => h.1, fun h => ⟨h, fun _ h' => absurd h' (Finset.notMem_empty _)⟩⟩
  have e₃ : capU W ∅ = fun T => ∃ α, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ U.U α ⊓ p₂ ⁻¹ᵁ ⊤) T := by
    funext T
    exact propext ⟨fun h => h.1, fun h => ⟨h, fun _ h' => absurd h' (Finset.notMem_empty _)⟩⟩
  have k₁ : capU V ∅ ≤ inU q ⊤ := fun T _ => inU_top hS q T
  have k₃ : capU W ∅ ≤ inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) := by
    rintro T ⟨⟨α, hα⟩, -⟩
    exact (inP _ _ T).2 ⟨inU_top hS q _, inU_top hS q' _⟩
  have hc : (⨆ α, p₁ ⁻¹ᵁ U.U α ⊓ p₂ ⁻¹ᵁ ⊤) = p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤ := by
    refine le_antisymm (iSup_le fun α => inf_le_inf_right _ ((TopologicalSpace.Opens.map p₁.base).monotone le_top)) ?_
    intro x _
    have hx : p₁ x ∈ (⨆ α, U.U α) := by
      rw [U.cover]
      trivial
    obtain ⟨α, hα⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨α, hα, trivial⟩
  have l₁ : (fun T => ∃ α, inU q (U.U α) T) ≤ inU q ⊤ := fun T _ => inU_top hS q T
  have l₃ : (fun T => ∃ α, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ U.U α ⊓ p₂ ⁻¹ᵁ ⊤) T) ≤ inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) := by
    rintro T ⟨α, hα⟩
    exact (inP _ _ T).2 ⟨inU_top hS q _, inU_top hS q' _⟩
  exact glue_top hMV hCD (hodgeXD q q' p₁ p₂ hw) (inU q ⊤) (inU q' ⊤) _ V W
    (fun α => inU_cos hS q _) (fun α => inU_cos hS _ _) h₁ h₂ hK k₁ k₃
    (fun a n => resU_bij_congr _ e₁ k₁ l₁ n (hZ K X q U.ι ⊤ U.U U.cover l₁ a n))
    (fun a n => resU_bij_congr _ e₃ k₃ l₃ n (hZ K P (p₁ ≫ q) U.ι _ _ hc l₃ a n)) g₁ g₂

end GlobalTheory.CompanionTheory.KunGlue
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethProductProperSmoothStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

theorem _root_.GlobalTheory.T.kuenneth_product_proper_smooth : SiteLaws → MVBij → CovDesc → ZarAbs → AffOm → KunAff → ∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) [IsProper q] [Smooth q] [IsProper q'] [Smooth q'] (p₁ : P ⟶ X) (p₂ : P ⟶ X') (hP : IsPullback p₁ p₂ q q'), ∀ (h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T)) (h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q' ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T)), (hodgeXD q q' p₁ p₂ hP.w.symm).Kun (inU q ⊤) (inU q' ⊤) (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤)) h₁ h₂ := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.kun_left | exact GlobalTheory.CompanionTheory.KunGlue.kun_left | (intros; apply GlobalTheory.CompanionTheory.KunGlue.kun_left <;> assumption)
end
end
