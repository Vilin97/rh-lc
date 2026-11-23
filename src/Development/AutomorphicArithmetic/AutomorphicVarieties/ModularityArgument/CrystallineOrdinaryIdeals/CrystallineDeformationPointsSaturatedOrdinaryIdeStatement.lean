module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmProd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmSub
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CrLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OrdinaryDeformation
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.LocalField
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.CrystallineTwistByUnramifiedCharacterStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ExistsTruncatedPolynomialThickeningFibreSquareStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsEps
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDiag
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OrdinaryIdealSaturatorsMapAlgHomStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.SaturatingElementUnramifiedTwistEqPowMulUnitStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.UnramifiedLiftDeformation
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.CrystallineDeformationAmalgamateOverFibreProductStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem _root_.GlobalTheory.T.crystallineDeformation_amalgamate_over_fibre_product_cover : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (C : Type) [CommRing C] [Algebra ℚ_[l] C] [Module.Finite ℚ_[l] C] [Algebra O C] [Algebra ℤ_[l] C] [IsScalarTower ℤ_[l] O C] [IsScalarTower ℤ_[l] ℚ_[l] C] [Algebra E C] [IsScalarTower O E C] [IsScalarTower ℚ_[l] E C] (πC : C →ₐ[E] E) (hπC : ∀ a, πC a = 0 → IsNilpotent a) (T : Type) [CommRing T] [Algebra ℚ_[l] T] [Module.Finite ℚ_[l] T] [Algebra O T] [Algebra ℤ_[l] T] [IsScalarTower ℤ_[l] O T] [IsScalarTower ℤ_[l] ℚ_[l] T] [Algebra E T] [IsScalarTower O E T] [IsScalarTower ℚ_[l] E T] (πT : T →ₐ[E] E) (hπT : ∀ a, πT a = 0 → IsNilpotent a) (p₁ : T →ₐ[E] B) (p₂ : T →ₐ[E] C), π.comp p₁ = πT → πC.comp p₂ = πT → (∀ b c, π b = πC c → ∃ t, p₁ t = b ∧ p₂ t = c) → ∀ (r₁ : GQ l →* GG (m := 3) (R := B)) (r₂ : GQ l →* GG (m := 3) (R := C)), D.InDcr (π : B →+* E) r₁ → D.InDcr (πC : C →+* E) r₂ → ∃ r : GQ l →* GG (m := 3) (R := T), D.InDcr (πT : T →+* E) r ∧ (GG.map (p₁ : T →+* B)).comp r = r₁ ∧ (GG.map (p₂ : T →+* C)).comp r = r₂ := by
  intro hP l _ O _ _ _ _ _ _ _ D E _ _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ C _ _ _ _ _ _ _ _ _ _ πC hπC
    T _ _ _ _ _ _ _ _ _ _ πT hπT p₁ p₂ h₁ h₂ hs r₁ r₂ hr₁ hr₂
  let I : Ideal T := RingHom.ker p₁ ⊓ RingHom.ker p₂
  let q : T →ₐ[E] (T ⧸ I) := Ideal.Quotient.mkₐ E I
  have hq : Function.Surjective q := Ideal.Quotient.mkₐ_surjective E I
  let q₁ : (T ⧸ I) →ₐ[E] B := Ideal.Quotient.liftₐ I p₁ fun a ha => ha.1
  let q₂ : (T ⧸ I) →ₐ[E] C := Ideal.Quotient.liftₐ I p₂ fun a ha => ha.2
  have e₁ (t : T) : q₁ (q t) = p₁ t := rfl
  have e₂ (t : T) : q₂ (q t) = p₂ t := rfl
  have f₁ (t : T) : π (p₁ t) = πT t := DFunLike.congr_fun h₁ t
  have hn : ∀ a, (π.comp q₁) a = 0 → IsNilpotent a := by
    intro a ha
    obtain ⟨t, rfl⟩ := hq a
    exact (hπT t ((f₁ t).symm.trans ha)).map q
  have hf : ∀ x y, q₁ x = q₁ y → q₂ x = q₂ y → x = y := by
    intro x y hx₁ hx₂
    obtain ⟨s, rfl⟩ := hq x
    obtain ⟨t, rfl⟩ := hq y
    refine Ideal.Quotient.eq.2 ⟨?_, ?_⟩
    · change p₁ (s - t) = 0
      rw [map_sub, ← e₁ s, ← e₁ t, hx₁, sub_self]
    · change p₂ (s - t) = 0
      rw [map_sub, ← e₂ s, ← e₂ t, hx₂, sub_self]
  have hglue : ∃ r' : GQ l →* GG (m := 3) (R := T ⧸ I),
      D.InDcr ((π.comp q₁ : (T ⧸ I) →ₐ[E] E) : (T ⧸ I) →+* E) r' ∧
      (GG.map (q₁ : (T ⧸ I) →+* B)).comp r' = r₁ ∧
      (GG.map (q₂ : (T ⧸ I) →+* C)).comp r' = r₂ := by
    have hsurj : ∀ b c, π b = πC c → ∃ a, q₁ a = b ∧ q₂ a = c := by
      intro b c h
      obtain ⟨t, ht₁, ht₂⟩ := hs b c h
      exact ⟨q t, (e₁ t).trans ht₁, (e₂ t).trans ht₂⟩
    have hred := hr₁.red.trans hr₂.red.symm
    have hprojections : ∃ r' : GQ l →* GG (m := 3) (R := T ⧸ I),
        (GG.map (q₁ : (T ⧸ I) →+* B)).comp r' = r₁ ∧
        (GG.map (q₂ : (T ⧸ I) →+* C)).comp r' = r₂ := by
      have hg (g : GQ l) : GG.map (π : B →+* E) (r₁ g) = GG.map (πC : C →+* E) (r₂ g) :=
        DFunLike.congr_fun hred g
      choose n hn₁ hn₂ using fun g =>
        OrdinaryDeformation.glue_GL (q₁ : (T ⧸ I) →+* B) (q₂ : (T ⧸ I) →+* C)
          (π : B →+* E) (πC : C →+* E) hf hsurj (r₁ g).left (r₂ g).left
          (congrArg SemidirectProduct.left (hg g))
      let x : GQ l → GG (m := 3) (R := T ⧸ I) := fun g => ⟨n g, (r₁ g).right⟩
      have hx₁ (g : GQ l) : GG.map (q₁ : (T ⧸ I) →+* B) (x g) = r₁ g :=
        SemidirectProduct.ext (hn₁ g) rfl
      have hx₂ (g : GQ l) : GG.map (q₂ : (T ⧸ I) →+* C) (x g) = r₂ g := by
        refine SemidirectProduct.ext (hn₂ g) ?_
        simpa only [GG.map_right] using congrArg SemidirectProduct.right (hg g)
      have hsep {a b : GG (m := 3) (R := T ⧸ I)}
          (ha : GG.map (q₁ : (T ⧸ I) →+* B) a = GG.map (q₁ : (T ⧸ I) →+* B) b)
          (hb : GG.map (q₂ : (T ⧸ I) →+* C) a = GG.map (q₂ : (T ⧸ I) →+* C) b) : a = b := by
        refine SemidirectProduct.ext (Units.ext (Matrix.ext fun i j => hf _ _ ?_ ?_)) ?_
        · exact congrArg (fun u => u.mat i j) ha
        · exact congrArg (fun u => u.mat i j) hb
        · simpa only [GG.map_right] using congrArg SemidirectProduct.right ha
      refine ⟨MonoidHom.mk' x (fun g g' => hsep ?_ ?_), MonoidHom.ext hx₁, MonoidHom.ext hx₂⟩
      · rw [map_mul, hx₁, hx₁, hx₁, map_mul]
      · rw [map_mul, hx₂, hx₂, hx₂, map_mul]
    obtain ⟨r', g₁, g₂⟩ := hprojections
    refine ⟨r', ?_, g₁, g₂⟩
    rw [← g₁] at hr₁
    rw [← g₂] at hr₂
    let L₁ := (q₁.restrictScalars ℚ_[l]).toLinearMap
    let L₂ := (q₂.restrictScalars ℚ_[l]).toLinearMap
    have hc : ∀ a b, QCont l fun g => (r' g).mat a b := fun a b =>
      OrdinaryDeformation.qcont_pair L₁ L₂ hf (hr₁.cont a b) (hr₂.cont a b)
    have hm : HasMult D.η r' := hr₁.mult
    refine ⟨hm, hr₁.red, hc, ?_⟩
    obtain ⟨ρ₁, hρ₁, hcr₁⟩ := hr₁.cr
    obtain ⟨ρ₂, hρ₂, hcr₂⟩ := hr₂.cr
    let _ : TopologicalSpace B := moduleTopology ℚ_[l] B
    have : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
    have : IsTopologicalRing B := IsModuleTopology.isTopologicalRing ℚ_[l] B
    let _ : TopologicalSpace C := moduleTopology ℚ_[l] C
    have : IsModuleTopology ℚ_[l] C := ⟨rfl⟩
    have : IsTopologicalRing C := IsModuleTopology.isTopologicalRing ℚ_[l] C
    let _ : TopologicalSpace (T ⧸ I) := moduleTopology ℚ_[l] (T ⧸ I)
    have : IsModuleTopology ℚ_[l] (T ⧸ I) := ⟨rfl⟩
    have : IsTopologicalRing (T ⧸ I) := IsModuleTopology.isTopologicalRing ℚ_[l] (T ⧸ I)
    have c₁ : ContAction (resCoef ℚ_[l] (colRep ρ₁)) := OrdinaryDeformation.cont_col ρ₁ fun a b => by
      simp only [hρ₁]
      exact (hr₁.cont a b).comp (continuous_subtype_val (p := fun g => g ∈ D.HL))
    have c₂ : ContAction (resCoef ℚ_[l] (colRep ρ₂)) := OrdinaryDeformation.cont_col ρ₂ fun a b => by
      simp only [hρ₂]
      exact (hr₂.cont a b).comp (continuous_subtype_val (p := fun g => g ∈ D.HL))
    have cprod : ContAction ((resCoef ℚ_[l] (colRep ρ₁)).prod (resCoef ℚ_[l] (colRep ρ₂))) :=
      (c₁.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
        (c₂.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
    have hHL := OrdinaryDeformation.HL_emb D
    have hprod := (isCrys_isDR_prod _ hHL _ _ c₁ c₂).1 hcr₁ hcr₂
    refine ⟨(glPart D.η r' hm).comp (Subgroup.inclusion inf_le_left), fun _ => rfl, ?_⟩
    refine ((isCrys_isDR_sub_quot _ hHL _ _ (OrdinaryDeformation.cont_col _ fun a b => ?_) cprod
      ((L₁.compLeft (Fin 3)).prod (L₂.compLeft (Fin 3))) fun g x => ?_).1
      (fun x y h => ?_)).1 hprod
    · exact (hc a b).comp continuous_subtype_val
    · refine Prod.ext (funext fun a => ?_) (funext fun a => ?_)
      · change _ = Matrix.mulVec (ρ₁ g : Matrix (Fin 3) (Fin 3) B) _ a
        rw [hρ₁]
        exact RingHom.map_mulVec (q₁ : (T ⧸ I) →+* B) _ x a
      · change _ = Matrix.mulVec (ρ₂ g : Matrix (Fin 3) (Fin 3) C) _ a
        rw [hρ₂]
        exact RingHom.map_mulVec (q₂ : (T ⧸ I) →+* C) _ x a
    · exact funext fun a => hf _ _ (congrFun (congrArg Prod.fst h) a) (congrFun (congrArg Prod.snd h) a)
  obtain ⟨r', hr', g₁, g₂⟩ := hglue
  obtain ⟨r, hr, rfl⟩ := crLift hP D E T πT hπT (T ⧸ I) (π.comp q₁) hn q hq (AlgHom.ext f₁) r' hr'
  exact ⟨r, hr, by rw [← g₁]; rfl, by rw [← g₂]; rfl⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OrdIdealEqBotOfCrystallineDeformation

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc.DcrOrd

variable {O G : Type} [CommRing O] [Group G]

def Cond (Ψ : G →* Oˣ) (I : Subgroup G) {C : Type} [CommRing C] [Algebra O C] (r : G →* GG (m := 3) (R := C)) : Prop :=
  (∀ s ∈ I, (r s).mat.charpoly = ∏ a, (X - Polynomial.C (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi Ψ a s)))) ∧
    ∀ s : Fin 3 → G, (∀ a, s a ∈ I) →
      ((r (s 0)).mat - Matrix.scalar _ (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi Ψ 0 (s 0)))) *
        ((r (s 1)).mat - Matrix.scalar _ (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi Ψ 1 (s 1)))) *
        ((r (s 2)).mat - Matrix.scalar _ (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi Ψ 2 (s 2)))) = 0

theorem cond_tri (Ψ : G →* Oˣ) (I : Subgroup G) {C : Type} [CommRing C] [Algebra O C] (u : G →* GG (m := 3) (R := C))
    (ht : ∀ g a b, wt a b < 0 → (u g).mat a b = 0)
    (hd : ∀ s ∈ I, ∀ a, (u s).mat a a = algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi Ψ a s)) : Cond Ψ I u := by
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · rw [Matrix.charpoly_of_isUpperTriangular]
    · simp only [hd s hs]
    · intro a b hab
      apply ht
      have : (b : ℕ) < a := hab
      simp only [wt, wt1]
      omega
  · have h10 := fun g => ht g 1 0 (by decide)
    have h20 := fun g => ht g 2 0 (by decide)
    have h21 := fun g => ht g 2 1 (by decide)
    have e0 := hd _ (hs 0) 0
    have e1 := hd _ (hs 1) 1
    have e2 := hd _ (hs 2) 2
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, h10, h20, h21, e0, e1, e2]

theorem cond_conj (Ψ : G →* Oˣ) (I : Subgroup G) {C : Type} [CommRing C] [Algebra O C] (u : G →* GG (m := 3) (R := C))
    (hu : ∀ s ∈ I, (u s).right = 1) (n : GL (Fin 3) C) (h : Cond Ψ I u) : Cond Ψ I (conjBy n u) := by
  have hm : ∀ s ∈ I, (conjBy n u s).mat =
      (n : Matrix (Fin 3) (Fin 3) C) * (u s).mat * ((n⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
    intro s hs
    have : (conjBy n u s).left = n * (u s).left * n⁻¹ := by
      simp [conjBy, hu s hs]
    simp only [GG.mat, this, Units.val_mul]
  have hc : ∀ (A : Matrix (Fin 3) (Fin 3) C) (c : C),
      (n : Matrix (Fin 3) (Fin 3) C) * A * ((n⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) - Matrix.scalar _ c =
      (n : Matrix (Fin 3) (Fin 3) C) * (A - Matrix.scalar _ c) *
        ((n⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
    intro A c
    rw [mul_sub, sub_mul, ← (Matrix.scalar_commute c (fun _ => Commute.all _ _) _).eq, mul_assoc (Matrix.scalar _ c),
      Units.mul_inv, mul_one]
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · rw [hm s hs, ← h.1 s hs, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
  · rw [hm _ (hs 0), hm _ (hs 1), hm _ (hs 2), hc, hc, hc]
    have := h.2 s hs
    generalize (u (s 0)).mat - _ = A at *
    generalize (u (s 1)).mat - _ = B at *
    generalize (u (s 2)).mat - _ = D at *
    simp only [mul_assoc, Units.inv_mul_cancel_left]
    rw [← mul_assoc B, ← mul_assoc A, ← mul_assoc A, this, zero_mul, mul_zero]

theorem ordIdeal_eq_bot {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    (D : Dat3 l O) {C : Type} [CommRing C] [Algebra O C] (r : GQ l →* GG (m := 3) (R := C)) (h : Cond D.Ψ (Iq l) r) :
    GlobalTheory.OrdLoc.ordIdeal D r = ⊥ := by
  rw [eq_bot_iff, GlobalTheory.OrdLoc.ordIdeal, Ideal.span_le]
  rintro x (⟨s, hs, i, rfl⟩ | ⟨s, hs, i, j, rfl⟩)
  · rw [h.1 s hs.2, sub_self, Polynomial.coeff_zero]
    exact Submodule.zero_mem _
  · have := h.2 s fun a => (hs a).2
    simp only [GlobalTheory.OrdLoc.sh, this]
    exact Submodule.zero_mem _

end GlobalTheory.OrdLoc.DcrOrd


open GlobalTheory.OrdLoc.DcrOrd in
theorem GlobalTheory.OrdLoc.ordIdeal_eq_bot_of_inDcr : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (r : GQ l →* GG (m := 3) (R := B)), D.InDcr (π : B →+* E) r → GlobalTheory.OrdLoc.ordIdeal D r = ⊥ := by
  intro hL l _ O _ _ _ _ _ _ _ D E _ _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ r hr
  obtain ⟨u, m, hu, -, -, rfl⟩ := (ordEq hL D E B π hπ r).1 hr
  exact ordIdeal_eq_bot D _ (cond_conj _ _ u (fun s hs => (hu.mult s).trans (D.η_unr s hs)) m
    (cond_tri _ _ u hu.tri (triDiag D E B π hπ u hu)))
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OrdIdealEqBotOfCrystallineDeformationStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem _root_.GlobalTheory.T.ordIdeal_eq_bot_of_crystalline_deformation : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (r : GQ l →* GG (m := 3) (R := B)), D.InDcr (π : B →+* E) r → D.ordIdeal r = ⊥ := by
  first | exact @GlobalTheory.OrdLoc.ordIdeal_eq_bot_of_inDcr | exact GlobalTheory.OrdLoc.ordIdeal_eq_bot_of_inDcr | (intros; apply GlobalTheory.OrdLoc.ordIdeal_eq_bot_of_inDcr <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.CrystallineDeformationPointsSaturatedOrdinaryIde

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.CrFrac

theorem push_comp {O R A B' Γ : Type} [CommRing O] [CommRing R] [CommRing A] [CommRing B'] [Algebra O R]
    [Algebra O A] [Algebra O B'] [Group Γ] (g : A →ₐ[O] B') (F : R →ₐ[O] A)
    (r : Γ →* GG (m := 3) (R := R)) :
    push (g.comp F) r = (GG.map (g : A →+* B')).comp (push F r) := rfl

theorem core (hL : LocalPublishedTheorems) {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O)
    (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ)) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E]
    [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E]
    (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B]
    [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B]
    [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (f : U.R →ₐ[O] B)
    (hf : D.InDcr (π : B →+* E) (push f U.r.hom))
    (C : Type) [CommRing C] [Algebra ℚ_[l] C] [Module.Finite ℚ_[l] C] [Algebra O C] [Algebra ℤ_[l] C]
    [IsScalarTower ℤ_[l] O C] [IsScalarTower ℤ_[l] ℚ_[l] C] [Algebra E C] [IsScalarTower O E C]
    [IsScalarTower ℚ_[l] E C]
    (T : Type) [CommRing T] [Algebra ℚ_[l] T] [Module.Finite ℚ_[l] T] [Algebra O T] [Algebra ℤ_[l] T]
    [IsScalarTower ℤ_[l] O T] [IsScalarTower ℤ_[l] ℚ_[l] T] [Algebra E T] [IsScalarTower O E T]
    [IsScalarTower ℚ_[l] E T]
    (πC : C →ₐ[E] E) (p₁ : T →ₐ[E] B) (p₂ : T →ₐ[E] C) (t : C) (ht : IsNilpotent t)
    (hπC : ∀ a, πC a = 0 → IsNilpotent a) (hπT : ∀ a, π (p₁ a) = 0 → IsNilpotent a)
    (hcomp : π.comp p₁ = πC.comp p₂) (hsurj : ∀ b c, π b = πC c → ∃ s, p₁ s = b ∧ p₂ s = c) (k : ℕ)
    (hcanc : ∀ (P y : T) (j : ℕ) (v : Cˣ), j ≤ 2 * k → p₂ P = t ^ j * v → P * y = 0 → p₁ y = 0)
    (a : U.R) (ha : GlobalTheory.OrdLoc.del D U.r.hom ^ k * a ∈ GlobalTheory.OrdLoc.ordIdeal D U.r.hom) : f a = 0 := by
  obtain ⟨u, hu1, hu2, hu3, j, v, hj, hdel⟩ := GlobalTheory.T.saturatingElement_unramified_twist_eq_pow_mul_unit D E C t ht
  have hr₂ := GlobalTheory.T.crystalline_twist_by_unramified_character D E C πC hπC u hu1 hu2 hu3
  obtain ⟨r, hr, hr1, hr2⟩ := GlobalTheory.T.crystallineDeformation_amalgamate_over_fibre_product_cover hL D E B π hπ C πC hπC T (π.comp p₁) hπT p₁ p₂ rfl hcomp.symm hsurj
    (push f U.r.hom) _ hf hr₂
  have hx : (GG.map (π : B →+* E)).comp (push f U.r.hom) = push ((π.restrictScalars O).comp f) U.r.hom :=
    (push_comp (π.restrictScalars O) f U.r.hom).symm
  obtain ⟨F, hF, -⟩ := unramified_lift_deformation D U E T (π.comp p₁) hπT ((π.restrictScalars O).comp f) r hr.mult
    (hr.red.trans (hf.red.symm.trans hx)) hr.cont
  have hF1 : (p₁.restrictScalars O).comp F = f := by
    obtain ⟨g, -, hg⟩ := unramified_lift_deformation D U E B π hπ ((π.restrictScalars O).comp f) (push f U.r.hom) hf.mult hx hf.cont
    refine (hg _ ?_).trans (hg f rfl).symm
    show push ((p₁.restrictScalars O).comp F) U.r.hom = push f U.r.hom
    rw [push_comp, hF]
    exact hr1
  have h0 := GlobalTheory.T.ordIdeal_eq_bot_of_crystalline_deformation hL D E T (π.comp p₁) hπT r hr
  obtain ⟨hmap, -, hdelF⟩ := GlobalTheory.T.ordinaryIdeal_saturators_map_algHom D F U.r.hom
  have h1 : F (GlobalTheory.OrdLoc.del D U.r.hom ^ k * a) = 0 := by
    have h := Ideal.mem_map_of_mem (F : U.R →+* T) ha
    rw [hmap, hF, h0] at h
    exact (Submodule.mem_bot _).1 h
  rw [map_mul, map_pow, hdelF, hF] at h1
  obtain ⟨-, -, hdel2⟩ := GlobalTheory.T.ordinaryIdeal_saturators_map_algHom D (p₂.restrictScalars O) r
  have hpush : push (p₂.restrictScalars O) r = r0 D.η ((Units.map (algebraMap O C : O →* C)).comp D.Ψ * u) := hr2
  rw [hpush, hdel] at hdel2
  have hP : p₂ (GlobalTheory.OrdLoc.del D r ^ k) = t ^ (j * k) * ((v ^ k : Cˣ) : C) := by
    rw [map_pow, show p₂ (GlobalTheory.OrdLoc.del D r) = t ^ j * v from hdel2, mul_pow, ← pow_mul, Units.val_pow_eq_pow_val]
  have h2 := hcanc _ (F a) (j * k) (v ^ k) (by nlinarith) hP h1
  rw [← hF1]
  exact h2

theorem main (hL : LocalPublishedTheorems) {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O)
    (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ)) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E]
    [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E]
    (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B]
    [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B]
    [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (f : U.R →ₐ[O] B)
    (hf : D.InDcr (π : B →+* E) (push f U.r.hom)) : GlobalTheory.OrdLoc.IY D U ≤ RingHom.ker f := by
  rintro a ⟨k, hk⟩
  haveI : Module.Finite E B := Module.Finite.of_restrictScalars_finite ℚ_[l] E B
  obtain ⟨C, _, _, _, T, _, _, _, πC, p₁, p₂, t, ht, hπC, hπT, hcomp, hsurj, hcanc⟩ := GlobalTheory.T.exists_truncated_polynomial_thickening_fibre_square π hπ (2 * k)
  letI : Algebra O C := Algebra.compHom C (algebraMap O E)
  letI : Algebra ℚ_[l] C := Algebra.compHom C (algebraMap ℚ_[l] E)
  letI : Algebra ℤ_[l] C := Algebra.compHom C (algebraMap ℤ_[l] E)
  haveI : IsScalarTower O E C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℚ_[l] E C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℤ_[l] O C := IsScalarTower.of_algebraMap_eq fun x =>
    congrArg (algebraMap E C) (IsScalarTower.algebraMap_apply ℤ_[l] O E x)
  haveI : IsScalarTower ℤ_[l] ℚ_[l] C := IsScalarTower.of_algebraMap_eq fun x =>
    congrArg (algebraMap E C) (IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] E x)
  haveI : Module.Finite ℚ_[l] C := Module.Finite.trans E C
  letI : Algebra O T := Algebra.compHom T (algebraMap O E)
  letI : Algebra ℚ_[l] T := Algebra.compHom T (algebraMap ℚ_[l] E)
  letI : Algebra ℤ_[l] T := Algebra.compHom T (algebraMap ℤ_[l] E)
  haveI : IsScalarTower O E T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℚ_[l] E T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℤ_[l] O T := IsScalarTower.of_algebraMap_eq fun x =>
    congrArg (algebraMap E T) (IsScalarTower.algebraMap_apply ℤ_[l] O E x)
  haveI : IsScalarTower ℤ_[l] ℚ_[l] T := IsScalarTower.of_algebraMap_eq fun x =>
    congrArg (algebraMap E T) (IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] E x)
  haveI : Module.Finite ℚ_[l] T := Module.Finite.trans E T
  exact core hL D U E B π hπ f hf C T πC p₁ p₂ t ht hπC hπT hcomp hsurj k hcanc a hk

end GlobalTheory.CrFrac
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.CrystallineDeformationPointsSaturatedOrdinaryIdeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem _root_.GlobalTheory.T.crystallineDeformation_points_saturatedOrdinaryIdeal_fracO : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ)) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (f : U.R →ₐ[O] B), D.InDcr (π : B →+* E) (push f U.r.hom) → GlobalTheory.OrdLoc.IY D U ≤ RingHom.ker f := by
  first | exact @GlobalTheory.CrFrac.main | exact GlobalTheory.CrFrac.main | (intros; apply GlobalTheory.CrFrac.main <;> assumption)
end
end
