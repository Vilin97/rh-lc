module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveBot
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.EtaleChartBaseChange.CLBAlg
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormLaws
public import Mathlib.RingTheory.RingHom.Etale
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
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Finite

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.EtaleChartBaseChange.CLBGen

section

@[expose] public section

set_option linter.style.haveILetI false

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace CrystallineSemistableComparison.Onto.CLB

theorem etale_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)
    (hf : f.Etale) (hg : g.Etale) : (g.comp f).Etale :=
  RingHom.Etale.stableUnderComposition f g hf hg

theorem etale_reindex {K B σ τ : Type} [CommRing K] [CommRing B] (s : K →+* B) (y : σ → B) (e : τ ≃ σ)
    (h : (MvPolynomial.eval₂Hom s y : MvPolynomial σ K →+* B).Etale) :
    (MvPolynomial.eval₂Hom s (y ∘ e) : MvPolynomial τ K →+* B).Etale := by
  have heq : (MvPolynomial.eval₂Hom s (y ∘ e) : MvPolynomial τ K →+* B) =
      (MvPolynomial.eval₂Hom s y).comp (MvPolynomial.rename (R := K) e).toRingHom :=
    RingHom.ext fun p => (MvPolynomial.eval₂Hom_rename s e y p).symm
  rw [heq]
  exact etale_comp _ _ (RingHom.Etale.of_bijective (MvPolynomial.renameEquiv K e).bijective) h

theorem coord_nzd {K B σ : Type} [Field K] [CommRing B] [Algebra K B] (y : σ → B)
    (h : (MvPolynomial.eval₂Hom (algebraMap K B) y : MvPolynomial σ K →+* B).Etale) (j : σ) :
    ∀ (a : ℕ) (ω : Om K B a), y j • ω = 0 → ω = 0 := by
  intro a ω hω
  letI : Algebra (MvPolynomial σ K) B := (MvPolynomial.eval₂Hom (algebraMap K B) y).toAlgebra
  haveI : Algebra.Etale (MvPolynomial σ K) B := h.toAlgebra
  haveI : IsScalarTower K (MvPolynomial σ K) B := IsScalarTower.of_algebraMap_eq fun r => by
    change _ = MvPolynomial.eval₂Hom (algebraMap K B) y (MvPolynomial.C r)
    simp
  haveI : Module.Free (MvPolynomial σ K) Ω[MvPolynomial σ K⁄K] :=
    Module.Free.of_basis (KaehlerDifferential.mvPolynomialBasis K σ)
  haveI : Module.Free B Ω[B⁄K] :=
    Module.Free.of_equiv (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (MvPolynomial σ K) B)
  have hX : IsSMulRegular (MvPolynomial σ K) (MvPolynomial.X j : MvPolynomial σ K) :=
    (MvPolynomial.isRegular_X (R := K) (n := j)).left
  have hB : IsSMulRegular B (algebraMap (MvPolynomial σ K) B (MvPolynomial.X j)) := IsSMulRegular.of_flat hX
  have hy : algebraMap (MvPolynomial σ K) B (MvPolynomial.X j) = y j := by
    change MvPolynomial.eval₂Hom (algebraMap K B) y (MvPolynomial.X j) = y j
    simp
  rw [hy] at hB
  have hmem : y j ∈ nonZeroDivisors B := by
    rw [mem_nonZeroDivisors_iff_right]
    intro z hz
    exact hB (by simpa [smul_eq_mul, mul_comm] using hz)
  exact Module.Flat.isSMulRegular_of_nonZeroDivisors hmem (show y j • ω = y j • (0 : Om K B a) by rw [hω, smul_zero])

theorem quot_etale {K B C σ : Type} [CommRing K] [CommRing B] [CommRing C] (s : K →+* B) (y : σ → B) (j0 : σ)
    (h : (MvPolynomial.eval₂Hom s y : MvPolynomial σ K →+* B).Etale) (ψ : B →+* C) (hψ : Function.Surjective ψ)
    (hk : RingHom.ker ψ = Ideal.span {y j0}) :
    (MvPolynomial.eval₂Hom (ψ.comp s) (fun j : {j // j ≠ j0} => ψ (y j)) : MvPolynomial {j // j ≠ j0} K →+* C).Etale := by
  classical
  let f : MvPolynomial σ K →+* B := MvPolynomial.eval₂Hom s y
  let g : MvPolynomial σ K →+* MvPolynomial {j // j ≠ j0} K :=
    MvPolynomial.eval₂Hom MvPolynomial.C (fun j => if hj : j = j0 then 0 else MvPolynomial.X ⟨j, hj⟩)
  let e : MvPolynomial {j // j ≠ j0} K →+* C := MvPolynomial.eval₂Hom (ψ.comp s) (fun j => ψ (y j))
  have hy0 : ψ (y j0) = 0 := by
    rw [← RingHom.mem_ker, hk]; exact Ideal.subset_span rfl
  have heg : e.comp g = ψ.comp f := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [e, g, f]
    · intro j
      by_cases hj : j = j0
      · subst hj; simp [e, g, f, hy0]
      · simp [e, g, f, hj]
  have hg : Function.Surjective g := by
    have hid : g.comp (MvPolynomial.rename (R := K) (Subtype.val : {j // j ≠ j0} → σ)).toRingHom = RingHom.id _ := by
      apply MvPolynomial.ringHom_ext
      · intro r; simp [g]
      · intro j; simp [g, j.2]
    intro p
    exact ⟨MvPolynomial.rename Subtype.val p, RingHom.congr_fun hid p⟩
  letI : Algebra (MvPolynomial σ K) B := f.toAlgebra
  letI : Algebra (MvPolynomial σ K) (MvPolynomial {j // j ≠ j0} K) := g.toAlgebra
  letI : Algebra (MvPolynomial σ K) C := (ψ.comp f).toAlgebra
  haveI : Algebra.Etale (MvPolynomial σ K) B := h.toAlgebra
  haveI := Algebra.Etale.baseChange (MvPolynomial σ K) B (MvPolynomial {j // j ≠ j0} K)
  let eA : MvPolynomial {j // j ≠ j0} K →ₐ[MvPolynomial σ K] C :=
    { e with commutes' := fun p => RingHom.congr_fun heg p }
  let ψA : B →ₐ[MvPolynomial σ K] C := { ψ with commutes' := fun p => rfl }
  let Φ := Algebra.TensorProduct.lift eA ψA (fun _ _ => Commute.all _ _)
  have key : ∀ t : TensorProduct (MvPolynomial σ K) (MvPolynomial {j // j ≠ j0} K) B, ∃ b : B, t = 1 ⊗ₜ b := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul q b =>
      obtain ⟨p, rfl⟩ := hg q
      refine ⟨f p * b, ?_⟩
      have h1 : (g p : MvPolynomial {j // j ≠ j0} K) = p • (1 : MvPolynomial {j // j ≠ j0} K) := by
        rw [Algebra.smul_def, mul_one]; rfl
      rw [h1, TensorProduct.smul_tmul, Algebra.smul_def]; rfl
    | add a b ha hb =>
      obtain ⟨x, rfl⟩ := ha
      obtain ⟨z, rfl⟩ := hb
      exact ⟨x + z, by rw [TensorProduct.tmul_add]⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro t ht
      obtain ⟨b, rfl⟩ := key t
      have hb : ψ b = 0 := by simpa [Φ, eA, ψA] using ht
      rw [← RingHom.mem_ker, hk, Ideal.mem_span_singleton'] at hb
      obtain ⟨c, rfl⟩ := hb
      have h2 : c * y j0 = (MvPolynomial.X j0 : MvPolynomial σ K) • c := by
        rw [Algebra.smul_def, mul_comm]
        change _ = MvPolynomial.eval₂Hom s y (MvPolynomial.X j0) * c
        simp
      have h3 : (MvPolynomial.X j0 : MvPolynomial σ K) • (1 : MvPolynomial {j // j ≠ j0} K) = 0 := by
        rw [Algebra.smul_def, mul_one]
        change g (MvPolynomial.X j0) = 0
        simp [g]
      rw [h2, ← TensorProduct.smul_tmul, h3, TensorProduct.zero_tmul]
    · intro c
      obtain ⟨b, rfl⟩ := hψ c
      exact ⟨1 ⊗ₜ b, by simp [Φ, eA, ψA]⟩
  have hcomp : e = (Φ : TensorProduct (MvPolynomial σ K) (MvPolynomial {j // j ≠ j0} K) B →+* C).comp
      (algebraMap (MvPolynomial {j // j ≠ j0} K) (TensorProduct (MvPolynomial σ K) (MvPolynomial {j // j ≠ j0} K) B)) := by
    ext q
    · simp [Φ, eA, ψA, e, Algebra.TensorProduct.algebraMap_apply]
    · simp [Φ, eA, ψA, e, Algebra.TensorProduct.algebraMap_apply]
  change e.Etale
  rw [hcomp]
  exact etale_comp _ _ (RingHom.etale_algebraMap.2 inferInstance) (RingHom.Etale.of_bijective hΦ)

end CrystallineSemistableComparison.Onto.CLB

end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.EtaleChartBaseChange.CLBKer

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace CrystallineSemistableComparison.Onto.CLB

theorem app_surj {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f] (U : Y.Opens) (hU : IsAffineOpen U) :
    Function.Surjective (f.app U).hom :=
  f.app_surjective U hU

theorem fromSpec_appLE_top {Y : Scheme.{0}} {D : Y.Opens} (hD : IsAffineOpen D)
    (e : (⊤ : (Spec Γ(Y, D)).Opens) ≤ hD.fromSpec ⁻¹ᵁ D) :
    hD.fromSpec.appLE D ⊤ e = (Scheme.ΓSpecIso Γ(Y, D)).inv := by
  unfold Scheme.Hom.appLE
  rw [hD.fromSpec_app_self]
  simp [← Functor.map_comp]

theorem SpecMap_appLE_top {R S : CommRingCat.{0}} (f : R ⟶ S) (e : (⊤ : (Spec S).Opens) ≤ Spec.map f ⁻¹ᵁ ⊤) :
    (Spec.map f).appLE ⊤ ⊤ e = (Scheme.ΓSpecIso R).hom ≫ f ≫ (Scheme.ΓSpecIso S).inv := by
  rw [← Scheme.ΓSpecIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

theorem appLE_fromSpec_quot {Y : Scheme.{0}} {D : Y.Opens} (hD : IsAffineOpen D) (J : Ideal Γ(Y, D))
    (e : (⊤ : (Spec (CommRingCat.of (Γ(Y, D) ⧸ J))).Opens) ≤
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ hD.fromSpec) ⁻¹ᵁ D) (x : Γ(Y, D)) :
    ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ hD.fromSpec).appLE D ⊤ e).hom x =
      (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, D) ⧸ J))).inv.hom (Ideal.Quotient.mk J x) := by
  rw [← Scheme.Hom.appLE_comp_appLE _ _ D ⊤ ⊤ (by simp [hD.fromSpec_preimage_self]) (by simp)]
  rw [fromSpec_appLE_top, SpecMap_appLE_top]
  change (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, D) ⧸ J))).inv.hom (Ideal.Quotient.mk J
    ((Scheme.ΓSpecIso Γ(Y, D)).hom.hom ((Scheme.ΓSpecIso Γ(Y, D)).inv.hom x))) = _
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

theorem ker_snd {W Z Y : Scheme.{0}} (i : W ⟶ Z) [IsClosedImmersion i] (π : Y ⟶ Z) (V : Z.Opens) (hV : IsAffineOpen V)
    (D : Y.Opens) (hD : IsAffineOpen D) (hDV : D ≤ π ⁻¹ᵁ V) :
    RingHom.ker ((pullback.snd i π).app D).hom = Ideal.map (π.appLE V D hDV).hom (RingHom.ker (i.app V).hom) := by
  apply le_antisymm
  · set I := RingHom.ker (i.app V).hom
    set J := Ideal.map (π.appLE V D hDV).hom I
    have hI' : IsAffineOpen (i ⁻¹ᵁ V) := hV.preimage i
    have hsurj := i.app_surjective V hV
    let e := RingHom.quotientKerEquivOfSurjective hsurj
    have hIJ : I ≤ J.comap (π.appLE V D hDV).hom := Ideal.le_comap_map
    let ψ : Γ(W, i ⁻¹ᵁ V) →+* Γ(Y, D) ⧸ J := (Ideal.quotientMap J (π.appLE V D hDV).hom hIJ).comp e.symm.toRingHom
    let a : Spec (CommRingCat.of (Γ(Y, D) ⧸ J)) ⟶ Y := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ hD.fromSpec
    let w : Spec (CommRingCat.of (Γ(Y, D) ⧸ J)) ⟶ W := Spec.map (CommRingCat.ofHom ψ) ≫ hI'.fromSpec
    have hring : i.appLE V (i ⁻¹ᵁ V) le_rfl ≫ CommRingCat.ofHom ψ =
        π.appLE V D hDV ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) := by
      ext x
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
      rw [← Scheme.Hom.app_eq_appLE]
      have : e.symm ((i.app V).hom x) = Ideal.Quotient.mk I x := by
        rw [RingEquiv.symm_apply_eq]; rfl
      change Ideal.quotientMap J (π.appLE V D hDV).hom hIJ (e.symm ((i.app V).hom x)) = _
      rw [this, Ideal.quotientMap_mk]
    have hw : w ≫ i = a ≫ π := by
      simp only [w, a, Category.assoc]
      rw [← IsAffineOpen.SpecMap_appLE_fromSpec i hV hI' le_rfl,
        ← IsAffineOpen.SpecMap_appLE_fromSpec π hV hD hDV, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, hring]
    let c := pullback.lift w a hw
    intro x hx
    rw [RingHom.mem_ker] at hx
    have he : (⊤ : (Spec (CommRingCat.of (Γ(Y, D) ⧸ J))).Opens) ≤ a ⁻¹ᵁ D := by
      simp [a, hD.fromSpec_preimage_self]
    have h0 : (a.appLE D ⊤ he).hom x = 0 := by
      have hca : c ≫ pullback.snd i π = a := pullback.lift_snd _ _ _
      have key : ∀ (b : Spec (CommRingCat.of (Γ(Y, D) ⧸ J)) ⟶ Y) (hb : c ≫ pullback.snd i π = b) (e' : ⊤ ≤ b ⁻¹ᵁ D),
          (b.appLE D ⊤ e').hom x = 0 := by
        rintro b rfl e'
        rw [← Scheme.Hom.appLE_comp_appLE _ _ D ((pullback.snd i π) ⁻¹ᵁ D) ⊤ le_rfl (by simpa using e'),
          ← Scheme.Hom.app_eq_appLE]
        simp [hx]
      exact key a hca he
    rw [appLE_fromSpec_quot hD J he x] at h0
    have h1 : Ideal.Quotient.mk J x = 0 := by
      have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, D) ⧸ J))).hom.hom h0
      rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply, map_zero] at h2
      exact h2
    exact Ideal.Quotient.eq_zero_iff_mem.1 h1
  · rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [RingHom.mem_ker] at hg
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have h1 : ∀ (f : pullback i π ⟶ Z) (hf : pullback.fst i π ≫ i = f) (e : (pullback.snd i π) ⁻¹ᵁ D ≤ f ⁻¹ᵁ V),
        (f.appLE V _ e).hom g = 0 := by
      rintro f rfl e
      rw [Scheme.Hom.comp_appLE]
      simp [hg]
    rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    exact h1 _ pullback.condition _

end CrystallineSemistableComparison.Onto.CLB

end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.EtaleChartBaseChange.ChartLawsB

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace CrystallineSemistableComparison.Onto

open Pb CLB

variable {K : Type} [CommRing K] {W Z Y : Scheme.{0}}

theorem strV_appLE (q : Z ⟶ Spec (CommRingCat.of K)) (π : Y ⟶ Z) (V : Z.Opens) (U : Y.Opens) (h : U ≤ π ⁻¹ᵁ V) :
    strV (π ≫ q) U = (π.appLE V U h).hom.comp (strV q V) := by
  unfold strV
  rw [← Scheme.Hom.appLE_comp_appLE π q ⊤ V U le_top h]
  rfl

theorem strV_app (q : Z ⟶ Spec (CommRingCat.of K)) (π : Y ⟶ Z) (U : Z.Opens) :
    strV (π ≫ q) (π ⁻¹ᵁ U) = (π.app U).hom.comp (strV q U) := by
  rw [strV_appLE q π U (π ⁻¹ᵁ U) le_rfl, Scheme.Hom.app_eq_appLE]

theorem rs_appLE (π : Y ⟶ Z) (V : Z.Opens) (U U' : Y.Opens) (hU : U ≤ π ⁻¹ᵁ V) (h : U' ≤ U) (a : Γ(Z, V)) :
    rs h ((π.appLE V U hU).hom a) = (π.appLE V U' (h.trans hU)).hom a := by
  unfold rs
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem card_ne (m : ℕ) (j0 : Fin m) : Fintype.card {j : Fin m // j ≠ j0} = m - 1 := by
  simp [Fintype.card_subtype_compl]

theorem chartLaws_B : ∀ (K : Type) [Field K] (W Z Y : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Z)
    [IsClosedImmersion i] (π : Y ⟶ Z) (d : ℕ) (V : Z.Opens) (c : BChart q i π d V),
    ∀ (k : Fin d) (D : Y.Opens) (h : D ≤ c.C k), IsAffineOpen D → Nonempty (Coord (π ≫ q) D (c.n + d)) ∧
      Nonempty (Coord (pullback.snd i π ≫ π ≫ q) (pullback.snd i π ⁻¹ᵁ D) (c.n + d - 1)) ∧
      RingHom.ker ((pullback.snd i π).app D).hom = Ideal.span {(π.appLE V D (h.trans (c.C_le k))).hom (c.t k)} ∧
      ∀ (a : ℕ) (ω : Om K (Sec (π ≫ q) D) a),
        (show Sec (π ≫ q) D from (π.appLE V D (h.trans (c.C_le k))).hom (c.t k)) • ω = 0 → ω = 0 := by
  intro K _ W Z Y q i _ π d V c k D h hD
  have hDV : D ≤ π ⁻¹ᵁ V := h.trans (c.C_le k)
  set φ := (π.appLE V (c.C k) (c.C_le k)).hom with hφ
  set yC : Fin c.n ⊕ Fin d → Γ(Y, c.C k) := Sum.elim (φ ∘ c.x) (fun j => if j = k then φ (c.t k) else c.u k j) with hyC
  have hC := chart_etale (strV q V) c.x c.t c.etale φ (c.u k) k (c.surj k) (c.rel k)
  let cC : Coord (π ≫ q) (c.C k) (c.n + d) :=
    ⟨c.C_aff k, yC ∘ finSumFinEquiv.symm, by
      rw [strV_appLE q π V (c.C k) (c.C_le k)]
      exact etale_reindex _ _ _ hC⟩
  obtain ⟨cD, hcD⟩ := coord_res cC h hD
  set j0 : Fin (c.n + d) := finSumFinEquiv (Sum.inr k) with hj0
  set τ := (π.appLE V D hDV).hom (c.t k) with hτ
  have ht : cD.t j0 = τ := by
    rw [hcD]
    change rs h (yC (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr k)))) = _
    rw [Equiv.symm_apply_apply]
    simp only [hyC, Sum.elim_inr, hφ]
    exact rs_appLE π V (c.C k) D (c.C_le k) h (c.t k)

  have hrel : ∀ j, φ (c.t j) = φ (c.t k) * c.u k j := by
    intro j
    have hm : MvPolynomial.C (c.t j) - MvPolynomial.C (c.t k) * MvPolynomial.X j ∈
        RingHom.ker (MvPolynomial.eval₂Hom φ (c.u k)) := by
      rw [c.rel k]
      exact Ideal.subset_span (Set.mem_insert_of_mem _ ⟨j, rfl⟩)
    rw [RingHom.mem_ker] at hm
    simpa [sub_eq_zero] using hm
  have hker : RingHom.ker ((pullback.snd i π).app D).hom = Ideal.span {τ} := by
    rw [ker_snd i π V c.affine D hD hDV, c.ker, Ideal.map_span]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_span_singleton']
      refine ⟨rs h (c.u k j), ?_⟩
      rw [hτ, ← rs_appLE π V (c.C k) D (c.C_le k) h, ← rs_appLE π V (c.C k) D (c.C_le k) h, ← map_mul, ← hφ,
        hrel j, mul_comm]
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.subset_span ⟨c.t k, ⟨k, rfl⟩, rfl⟩
  refine ⟨⟨cD⟩, ?_, hker, ?_⟩
  · have hsurj := app_surj (pullback.snd i π) D hD
    have hq := quot_etale (strV (π ≫ q) D) cD.t j0 cD.etale ((pullback.snd i π).app D).hom hsurj (by rw [hker, ht])
    let e : Fin (c.n + d - 1) ≃ {j : Fin (c.n + d) // j ≠ j0} :=
      (Fintype.equivFinOfCardEq (card_ne (c.n + d) j0)).symm
    refine ⟨⟨hD.preimage (pullback.snd i π), (fun j : {j : Fin (c.n + d) // j ≠ j0} =>
      ((pullback.snd i π).app D).hom (cD.t j)) ∘ e, ?_⟩⟩
    rw [strV_app (π ≫ q) (pullback.snd i π) D]
    exact etale_reindex _ _ _ hq
  · intro a ω hω
    have hal : algebraMap K (Sec (π ≫ q) D) = strV (π ≫ q) D := rfl
    have he : (MvPolynomial.eval₂Hom (algebraMap K (Sec (π ≫ q) D)) (cD.t : Fin (c.n + d) → Sec (π ≫ q) D)).Etale := by
      rw [hal]; exact cD.etale
    have key : ∀ ω' : Om K (Sec (π ≫ q) D) a, (cD.t j0 : Sec (π ≫ q) D) • ω' = 0 → ω' = 0 :=
      coord_nzd (K := K) (B := Sec (π ≫ q) D) _ he j0 a
    apply key
    rw [ht]
    exact hω

end CrystallineSemistableComparison.Onto

end
end
end
