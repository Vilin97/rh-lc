module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.InstFintypeHodgeBidegree
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveBot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineSmoothFormsBijectiveStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFormCupWedgeStatement
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.AffineHodgeIsomorphisms.IsFormT
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.TopRes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
import Mathlib.Tactic.Polynomial.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFormPullbackCompatStatement

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFormIsoOfBijective

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

noncomputable section

namespace GlobalTheory.CompanionTheory.HodgeFormTop

open CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.HT CrystallineSemistableComparison.Om.L2 CrystallineSemistableComparison.Pb

section
variable {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

def omEq (a : ℕ) : CrystallineSemistableComparison.Onto.Om K (CrystallineSemistableComparison.Onto.Sec q ⊤) a ≃ₗ[K] OmU q ⊤ a := LinearEquiv.refl K (OmU q ⊤ a)

abbrev resTop (a : ℕ) := CH.Mor.restrict (G q a) (inU q ⊤).ι

theorem resTop_pullC_bij (a n : ℕ) : Function.Bijective ((resTop q a).pullC n) :=
  (topRes_pf K _ (G q a) (inU q ⊤) ⊥ (fun T => inTop q T) n).1

theorem resTop_bij (a n : ℕ) : Function.Bijective ((resTop q a).pull n) :=
  CrystallineSemistableComparison.P.mapH_bij _ (fun m => resTop_pullC_bij q a m) n

def resTopEquiv (a : ℕ) : Hdg q a a ≃ₗ[K] HV q ⊤ a a :=
  LinearEquiv.ofBijective ((resTop q a).pull a) (resTop_bij q a a)

def LiftsT.toTop (Λ : LiftsT q) : Lifts q ⊤ where
  v T g := Λ.v T.obj g
  hv T g := Λ.hv T.obj g

theorem isFormT_of_isForm {a : ℕ} (g₀ : Γ(X, ⊤)) (g : Fin a → Γ(X, ⊤)) (c : HV q ⊤ a a)
    (h : IsForm q ⊤ (a := a) g₀ g c) : IsFormT q g₀ g ((resTopEquiv q a).symm c) := by
  intro Λ
  obtain ⟨f, hf, hc, hz⟩ := h (LiftsT.toTop q Λ)
  obtain ⟨z, rfl⟩ := (resTop_pullC_bij q a a).2 f
  have hd : CH.d (G q a) a z = 0 := by
    apply (resTop_pullC_bij q a (a + 1)).1
    rw [map_zero, ← CH.Mor.d_pullC]
    exact hf
  have hcz : (resTopEquiv q a) ((CH.cx (G q a)).cls z hd) = c := by
    rw [hc]
    exact CrystallineSemistableComparison.P.mapH_cls (resTop q a).hom a z hd _
  refine ⟨z, hd, ?_, fun t => ?_⟩
  · rw [← hcz, LinearEquiv.symm_apply_apply]
  · exact hz (t ⋙ (inU q ⊤).lift (𝟭 _) (fun T => inTop q T))

end

theorem main : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (a : ℕ),
    (∃ e : CrystallineSemistableComparison.Onto.Om K (CrystallineSemistableComparison.Onto.Sec q ⊤) a →ₗ[K] CrystallineSemistableComparison.Onto.HV q ⊤ a a, CrystallineSemistableComparison.Onto.IsOm q ⊤ a e ∧ Function.Bijective e) →
    ∃ e' : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a, CrystallineSemistableComparison.Om.L2.IsOmT q a e' := by
  intro K _ X q a ⟨e, he, hb⟩
  refine ⟨((resTopEquiv q a).trans (LinearEquiv.ofBijective e hb).symm).trans (omEq q a), fun g₀ g => ?_⟩
  exact isFormT_of_isForm q g₀ g _ (he g₀ g)

end GlobalTheory.CompanionTheory.HodgeFormTop
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFormIsoOfBijectiveStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

theorem _root_.GlobalTheory.T.hodge_form_iso_of_bijective : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (a : ℕ),
    (∃ e : CrystallineSemistableComparison.Onto.Om K (CrystallineSemistableComparison.Onto.Sec q ⊤) a →ₗ[K] CrystallineSemistableComparison.Onto.HV q ⊤ a a, CrystallineSemistableComparison.Onto.IsOm q ⊤ a e ∧ Function.Bijective e) →
    ∃ e' : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a, CrystallineSemistableComparison.Om.L2.IsOmT q a e' := by
  first | exact @GlobalTheory.CompanionTheory.HodgeFormTop.main | exact GlobalTheory.CompanionTheory.HodgeFormTop.main | (intros; apply GlobalTheory.CompanionTheory.HodgeFormTop.main <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFormOne

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

namespace GlobalTheory.CompanionTheory.HodgeFormUnit

theorem gForm_one {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) :
    CrystallineSemistableComparison.Om.L2.gForm q 1 Fin.elim0 = oneOm K (Sec q ⊤) := by
  apply Subtype.ext
  simp [CrystallineSemistableComparison.Onto.form, oneOm]

theorem e_oneH {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (e : CrystallineSemistableComparison.HT.Hdg q 0 0 ≃ₗ[K] OmU q ⊤ 0) (h : CrystallineSemistableComparison.Om.L2.IsOmT q 0 e) :
    e (CrystallineSemistableComparison.HT.oneH q) = oneOm K (Sec q ⊤) := by
  let Λ : CrystallineSemistableComparison.Om.L2.LiftsT q :=
    { v := fun T g => Function.surjInv Ideal.Quotient.mk_surjective
        (CrystallineSemistableComparison.Pb.ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T (CrystallineSemistableComparison.Om.L2.inTop q T) g)
      hv := fun T g => Function.surjInv_eq _ _ }
  obtain ⟨f, hf, hc, hz⟩ := h 1 Fin.elim0 Λ
  have hf' : f = (CrystallineSemistableComparison.Pb.toSq (CrystallineSemistableComparison.Pb.thFil (CrystallineSemistableComparison.smFun X q) (0 : ℕ)) (CrystallineSemistableComparison.Pb.thFil (CrystallineSemistableComparison.smFun X q) (((0 : ℕ) : ℤ) + 1))
      fun T => T.pdPow_zero).pullC 0 (fun s => (1 : (CrystallineSemistableComparison.Pb.thA (CrystallineSemistableComparison.smFun X q)).obj (s.obj (Fin.last 0)))) := by
    funext s
    apply Subtype.ext
    refine (hz s).trans ?_
    have hv : (Λ.form 1 Fin.elim0 s : (s.obj (Fin.last 0)).B) = Λ.v _ 1 := by
      simp [CrystallineSemistableComparison.Om.L2.LiftsT.form]
    have hJ : Λ.v (s.obj (Fin.last 0)) 1 - 1 ∈ (s.obj (Fin.last 0)).J :=
      Ideal.Quotient.eq.1 ((Λ.hv _ 1).trans ((map_one _).trans (map_one _).symm))
    refine Ideal.Quotient.eq.2 ?_
    change Λ.form 1 Fin.elim0 s - 1 ∈ (s.obj (Fin.last 0)).pdPow 1
    rw [hv]
    exact (s.obj (Fin.last 0)).J_le_pdPow_one hJ
  have h1 : CrystallineSemistableComparison.HT.oneH q = e.symm (CrystallineSemistableComparison.Om.L2.gForm q 1 Fin.elim0) := by
    refine Eq.trans ?_ hc.symm
    exact congrArg Submodule.Quotient.mk (Subtype.ext hf'.symm)
  rw [h1, LinearEquiv.apply_symm_apply, gForm_one]

end GlobalTheory.CompanionTheory.HodgeFormUnit
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFormOneStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

theorem _root_.GlobalTheory.T.hodge_form_one : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (e : CrystallineSemistableComparison.HT.Hdg q 0 0 ≃ₗ[K] OmU q ⊤ 0),
    CrystallineSemistableComparison.Om.L2.IsOmT q 0 e → e (CrystallineSemistableComparison.HT.oneH q) = oneOm K (Sec q ⊤) := by
  first | exact @GlobalTheory.CompanionTheory.HodgeFormUnit.e_oneH | exact GlobalTheory.CompanionTheory.HodgeFormUnit.e_oneH | (intros; apply GlobalTheory.CompanionTheory.HodgeFormUnit.e_oneH <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.AffineHodgeIsomorphisms.AsmOnto

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

namespace CrystallineSemistableComparison.Om.L2

theorem asm_of
    (hEx : ∀ (K : Type) [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q] (a : ℕ),
    ∃ e : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a, CrystallineSemistableComparison.Om.L2.IsOmT q a e)
    (hNat : ∀ {K : Type} [CommRing K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K))
    (u : X ⟶ Y) (hu : u ≫ p = q) (a : ℕ) (e : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a) (e' : CrystallineSemistableComparison.HT.Hdg p a a ≃ₗ[K] OmU p ⊤ a),
    CrystallineSemistableComparison.Om.L2.IsOmT q a e → CrystallineSemistableComparison.Om.L2.IsOmT p a e' → ∀ x : CrystallineSemistableComparison.HT.Hdg p a a,
      e (CrystallineSemistableComparison.HT.pullH u hu a a x) = formRes q (show (⊤ : X.Opens) ≤ u ⁻¹ᵁ ⊤ by simp) a (formPull hu ⊤ a (e' x)))
    (hCup : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (a b c : ℕ) (h : a + b = c)
    (eA : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a) (eB : CrystallineSemistableComparison.HT.Hdg q b b ≃ₗ[K] OmU q ⊤ b) (eC : CrystallineSemistableComparison.HT.Hdg q c c ≃ₗ[K] OmU q ⊤ c),
    CrystallineSemistableComparison.Om.L2.IsOmT q a eA → CrystallineSemistableComparison.Om.L2.IsOmT q b eB → CrystallineSemistableComparison.Om.L2.IsOmT q c eC → ∀ x y,
      eC (CrystallineSemistableComparison.HT.cupH q h h x y) = wedgeOm K (Sec q ⊤) h (eA x) (eB y))
    (hOne : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (e : CrystallineSemistableComparison.HT.Hdg q 0 0 ≃ₗ[K] OmU q ⊤ 0),
    CrystallineSemistableComparison.Om.L2.IsOmT q 0 e → e (CrystallineSemistableComparison.HT.oneH q) = oneOm K (Sec q ⊤)) :
    ∀ (K : Type) [Field K] [CharZero K],
    ∃ (e : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q] (a : ℕ),
      HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a) (ε : ℕ → ℕ → ℤ), (∀ a b, ε a b = 1 ∨ ε a b = -1) ∧
    (∀ {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q]
      [IsAffine Y] [Smooth p] (u : X ⟶ Y) (hu : u ≫ p = q) (a : ℕ) (x : HT.Hdg p a a),
      e q a (HT.pullH u hu a a x) = formRes q (show (⊤ : X.Opens) ≤ u ⁻¹ᵁ ⊤ by simp) a (formPull hu ⊤ a (e p a x))) ∧
    (∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q] (a b c : ℕ) (h : a + b = c)
      (x : HT.Hdg q a a) (y : HT.Hdg q b b),
      e q c (HT.cupH q h h x y) = ε a b • wedgeOm K (Sec q ⊤) h (e q a x) (e q b y)) ∧
    ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q], e q 0 (HT.oneH q) = oneOm K (Sec q ⊤) := by
  intro K _ _
  refine ⟨fun q _ _ a => Classical.choose (hEx K q a), fun _ _ => 1, fun _ _ => Or.inl rfl, ?_, ?_, ?_⟩
  · intro X Y q p _ _ _ _ u hu a x
    exact hNat q p u hu a _ _ (Classical.choose_spec (hEx K q a)) (Classical.choose_spec (hEx K p a)) x
  · intro X q _ _ a b c h x y
    simp only [one_smul]
    exact hCup q a b c h _ _ _ (Classical.choose_spec (hEx K q a)) (Classical.choose_spec (hEx K q b))
      (Classical.choose_spec (hEx K q c)) x y
  · intro X q _ _
    exact hOne q _ (Classical.choose_spec (hEx K q 0))

theorem asm_onto (hA : CrystallineSemistableComparison.Onto.AffOm) (hN : CrystallineSemistableComparison.Onto.OmNat)
    (hTop : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (a : ℕ),
    (∃ e : CrystallineSemistableComparison.Onto.Om K (CrystallineSemistableComparison.Onto.Sec q ⊤) a →ₗ[K] CrystallineSemistableComparison.Onto.HV q ⊤ a a, CrystallineSemistableComparison.Onto.IsOm q ⊤ a e ∧ Function.Bijective e) →
    ∃ e' : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a, CrystallineSemistableComparison.Om.L2.IsOmT q a e')
    (hGlue : CrystallineSemistableComparison.Onto.AffOm → CrystallineSemistableComparison.Onto.OmNat → ∀ (K : Type) [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    [IsAffine X] [Smooth q] (a : ℕ),
    ∃ e : CrystallineSemistableComparison.Onto.Om K (CrystallineSemistableComparison.Onto.Sec q ⊤) a →ₗ[K] CrystallineSemistableComparison.Onto.HV q ⊤ a a, CrystallineSemistableComparison.Onto.IsOm q ⊤ a e ∧ Function.Bijective e)
    (hNat : ∀ {K : Type} [CommRing K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K))
    (u : X ⟶ Y) (hu : u ≫ p = q) (a : ℕ) (e : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a) (e' : CrystallineSemistableComparison.HT.Hdg p a a ≃ₗ[K] OmU p ⊤ a),
    CrystallineSemistableComparison.Om.L2.IsOmT q a e → CrystallineSemistableComparison.Om.L2.IsOmT p a e' → ∀ x : CrystallineSemistableComparison.HT.Hdg p a a,
      e (CrystallineSemistableComparison.HT.pullH u hu a a x) = formRes q (show (⊤ : X.Opens) ≤ u ⁻¹ᵁ ⊤ by simp) a (formPull hu ⊤ a (e' x)))
    (hCup : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (a b c : ℕ) (h : a + b = c)
    (eA : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a) (eB : CrystallineSemistableComparison.HT.Hdg q b b ≃ₗ[K] OmU q ⊤ b) (eC : CrystallineSemistableComparison.HT.Hdg q c c ≃ₗ[K] OmU q ⊤ c),
    CrystallineSemistableComparison.Om.L2.IsOmT q a eA → CrystallineSemistableComparison.Om.L2.IsOmT q b eB → CrystallineSemistableComparison.Om.L2.IsOmT q c eC → ∀ x y,
      eC (CrystallineSemistableComparison.HT.cupH q h h x y) = wedgeOm K (Sec q ⊤) h (eA x) (eB y))
    (hOne : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (e : CrystallineSemistableComparison.HT.Hdg q 0 0 ≃ₗ[K] OmU q ⊤ 0),
    CrystallineSemistableComparison.Om.L2.IsOmT q 0 e → e (CrystallineSemistableComparison.HT.oneH q) = oneOm K (Sec q ⊤)) :
    ∀ (K : Type) [Field K] [CharZero K],
    ∃ (e : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q] (a : ℕ),
      HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a) (ε : ℕ → ℕ → ℤ), (∀ a b, ε a b = 1 ∨ ε a b = -1) ∧
    (∀ {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q]
      [IsAffine Y] [Smooth p] (u : X ⟶ Y) (hu : u ≫ p = q) (a : ℕ) (x : HT.Hdg p a a),
      e q a (HT.pullH u hu a a x) = formRes q (show (⊤ : X.Opens) ≤ u ⁻¹ᵁ ⊤ by simp) a (formPull hu ⊤ a (e p a x))) ∧
    (∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q] (a b c : ℕ) (h : a + b = c)
      (x : HT.Hdg q a a) (y : HT.Hdg q b b),
      e q c (HT.cupH q h h x y) = ε a b • wedgeOm K (Sec q ⊤) h (e q a x) (e q b y)) ∧
    ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q], e q 0 (HT.oneH q) = oneOm K (Sec q ⊤) := by
  exact asm_of (fun K _ _ _ q _ _ a => hTop q a (hGlue hA hN K q a)) hNat hCup hOne

end CrystallineSemistableComparison.Om.L2
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.AffineHodgeIsomorphisms.HdgAffIsoOnto

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

namespace CrystallineSemistableComparison.Om.L2

theorem hdg_aff_iso_onto (hA : CrystallineSemistableComparison.Onto.AffOm) (hN : CrystallineSemistableComparison.Onto.OmNat) :
    ∀ (K : Type) [Field K] [CharZero K],
    ∃ (e : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q] (a : ℕ),
      HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a) (ε : ℕ → ℕ → ℤ), (∀ a b, ε a b = 1 ∨ ε a b = -1) ∧
    (∀ {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q]
      [IsAffine Y] [Smooth p] (u : X ⟶ Y) (hu : u ≫ p = q) (a : ℕ) (x : HT.Hdg p a a),
      e q a (HT.pullH u hu a a x) = formRes q (show (⊤ : X.Opens) ≤ u ⁻¹ᵁ ⊤ by simp) a (formPull hu ⊤ a (e p a x))) ∧
    (∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q] (a b c : ℕ) (h : a + b = c)
      (x : HT.Hdg q a a) (y : HT.Hdg q b b),
      e q c (HT.cupH q h h x y) = ε a b • wedgeOm K (Sec q ⊤) h (e q a x) (e q b y)) ∧
    ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q], e q 0 (HT.oneH q) = oneOm K (Sec q ⊤) :=
  asm_onto hA hN GlobalTheory.T.hodge_form_iso_of_bijective GlobalTheory.T.affine_smooth_forms_bijective GlobalTheory.T.hodge_form_pullback_compat GlobalTheory.T.hodge_form_cup_wedge GlobalTheory.T.hodge_form_one

end CrystallineSemistableComparison.Om.L2
end
end
end
